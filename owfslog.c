/* owfslog.c: Simple program to read owfs files and log to file.
 *
 * Author: Steinar Midtskogen <steinar@latinitas.org>
 *
 * To compile: gcc -Os -o owfslog owfslog.c -lowcapi -lm -lpthread
 *
 * owfs and the owcapi library can be downloaded from http://owfs.org.
 *
 * Usage: owfslog [options]
 *
 * Valid options:
 * -a                      : Align logging time
 *                         :  This will delay the start of the program until the
 *                         :  logging times will match those if the program had
 *                         :  been started at the epoch (1 Jan 1970 00:00:00).
 * -c <configuration file> : Use this file rather than default /etc/owfslog.conf
 * -d                      : Run program in the background
 * -f <format>             : strftime time format, default: %Y%m%d%H%M%S
 * -h                      : Print a description of the configuration format
 * -i <seconds>            : Time between log updates, default: 300
 * -l <logfile>            : Log to this file, not to stdout
 * -p <depth>              : Depth of directory parsing
 *                         :  Normally, files need to be have a full path, but
 *                         :  this options makes owfslog search for the sensor
 *                         :  to the depth specified.  Default: 0
 * -P <pidfile>            : Write pid to file.
 * -q                      : Use local queueing (POSIX)
 *                         :  This ensures that owserver only receives one
 *                         :  request at a time.  Simultanious requests might
 *                         :  cause owserver to crash.
 * -Q                      : Use local queueing (System V)
 *                         :  As -q, but use System V semaphores rather than
 *                         :  POSIX semaphores.
 * -t                      : Use threads
 *                         :  owfslog always forks off one new process per
 *                         :  source, but by using this option owfslog will use
 *                         :  one thread per sensor rather than one process.
 * -u <userid>             : Change userid
 *                         :  Only works if run as root.
 * -v                      : Increase verbosity
 *                         :  For debugging.
 *
 * This program appends one line periodically as specified by the log interval.
 * The log format for n lines in the configuration file is:
 *
 *   <time stamp> val1 val2 ... valn
 *
 * Default time stamp format is YYYYMMDDhhmmss where YYYY is the year, MM is
 * the month, DD is the day, hh is the hour, mm is the minute and ss is the
 * second as returned from gmtime (UTC).
 *
 * See the owfs documentation for how to tune 1-wire options.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <time.h>
#include <unistd.h>
#include <string.h>
#include <sys/param.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/ipc.h>
#include <sys/time.h>
#include <sys/shm.h>
#include <sys/sem.h>
#include <sys/select.h>
#include <regex.h>
#include <owcapi.h>
#include <errno.h>
#include <math.h>
#include <semaphore.h>

#define VALARR_SIZE 4
#define QUEUE_SIZE 64

static sem_t semaphores[QUEUE_SIZE*2];

typedef struct {
  double val;          /* sensor value */
  double diff;         /* difference since last value */
  double inc;          /* increase in current log interval */
  time_t delta;        /* time since different value was sampled */
  time_t incdelta;     /* time since last value in previous interval */
  time_t update;       /* time when this value was sampled */
  time_t changedelta;  /* delta since last change */
  time_t changedelta2; /* last delta between change */
} val;

typedef struct _queueentry {
  time_t locktime;
  volatile int ack;
  const char *path;
} queueentry;

typedef struct {
  char *file;
  double interval;
  int sourceid;
  volatile val *vals[VALARR_SIZE];
  double shift;
  time_t update;
  time_t lastupdate;
  time_t prevupdate;
  time_t changed[VALARR_SIZE];
  double lastval[VALARR_SIZE];
  double prevval[VALARR_SIZE];
  double minrate[VALARR_SIZE];
  int minrateset[VALARR_SIZE];

  time_t changedelta[VALARR_SIZE]; /* time since a different value was sampled */
  time_t changedelta2[VALARR_SIZE]; /* previous changedelta */

  char message[80];
} sensor;

typedef struct {
  char *source;
  char *source2;
  char *name;
  char *files;
  char *file;
  char *file2;
  sensor *sensor;
  sensor *sensor2;
  int fileid;
  int fileid2;
  char *format;
  double interval;
  double farg1;
  double farg2;
  double farg3;
  double farg4;
  double farg5;
  double farg1b;
  double farg2b;
  double farg3b;
  double farg4b;
  double farg5b;
  double retvalue;
  char entry[32];
  unsigned int numvals;
  volatile val *vals[VALARR_SIZE];
  volatile val *vals2[VALARR_SIZE];
  int sourceid;
  int sourceid2;
} function;

static int log_interval = 300;
static function *functions = NULL;
static int count = 0;
static int threads = 0;
static int queueing = 0;
static int queueing_global = 0;
static int posixsem = 1;
static char *sensor_buf = NULL;
static queueentry *queues = NULL;
static queueentry *queue = NULL;
static int debug = 0;
static unsigned int max_depth = 0;
static char timestamp[80];
static const char *dateformat = "%Y%m%d%H%M%S";
static int semid = 0;
static pid_t ipcpid = 0;
static const char *pidfile = 0;
static int uid = 0;

int seminit(int id, int value)
{
  return posixsem ? sem_init(&semaphores[id], 1, value) : semctl(semid, id, SETVAL, value);
}


int semtrywait(int id)
{
  struct sembuf sb = {id, -1, IPC_NOWAIT};
  return posixsem ? sem_trywait(&semaphores[id]) : semop(semid, &sb, 1);
}

int sempost(int id)
{
  struct sembuf sb = {id, 1, 0};
  return posixsem ? sem_post(&semaphores[id]) : semop(semid, &sb, 1);
}

int semwait(int id)
{
  struct sembuf sb = {id, -1, 0};
  return posixsem ? sem_wait(&semaphores[id]) : semop(semid, &sb, 1);
}

int semtimedwait(int id, const struct timespec *timeout)
{
  struct sembuf sb = {id, -1, 0};
  struct timespec ts = *timeout;
  if (!posixsem) {
    struct timeval tv;

    gettimeofday(&tv, NULL);
    if (ts.tv_nsec < tv.tv_usec * 1000) {
      ts.tv_nsec += 1000000000;
      ts.tv_sec--;
    }
    ts.tv_nsec -= tv.tv_usec * 1000;
    ts.tv_sec -= tv.tv_sec;
  }

  return posixsem ? sem_timedwait(&semaphores[id], &ts) : semtimedop(semid, &sb, 1, &ts);
}

int semdestroy(int id)
{
  return posixsem ? sem_destroy(&semaphores[id]) : 0;
}

void quicksort(val *vals, int length)
{
  int i, j;
  double v;
  val t;
 
  if (length <= 1)
    return;
 
  i = 0;
  j = length;
  v = vals[0].val;
  while (1) {
    while (vals[++i].val < v && i < length);
    while (vals[--j].val > v);
    if (i >= j)
      break;
    t = vals[i];
    vals[i] = vals[j];
    vals[j] = t;
  }
  t = vals[i - 1];
  vals[i - 1] = vals[0];
  vals[0] = t;
  quicksort(vals, i - 1);
  quicksort(vals + i, length - i);
}

int sorttrim(val *vals, double discard, double min, double max, int len)
{
  int start, nl, i;
  val *valw = vals;

  /* Remove nan's */
  for (i = 0; i < len; i++)
    if (!isnan(vals[i].val))
      *valw++ = vals[i];

  if (valw == vals) {
    vals[0].val = atof("nan");
    return 1;
  }

  /* Remove values outside lower limit */
  valw = vals;
  for (i = 0; i < len; i++)
    if (vals[i].val >= min || min == atof("-inf"))
      *valw++ = vals[i];

  if (valw == vals) {
    vals[0].val = discard > 0 ? atof("nan") : min;
    return 1;
  }

  /* Remove values outside upper limit */
  len = valw - vals;
  valw = vals;
  for (i = 0; i < len; i++)
    if (vals[i].val <= max || max == atof("inf"))
      *valw++ = vals[i];

  if (valw == vals) {
    vals[0].val = discard > 0 ? atof("nan") : max;
    return 1;
  }

  len = valw - vals;

  quicksort(vals, len);
  if (discard <= 0)
    return len;
  if (discard > 50)
    discard = 50;
  start = (int)(len * discard / 100);
  nl = len - 2 * start > 0 ? len - 2 * start : 1;
  memmove(vals, vals + start, nl * sizeof(*vals));
  vals[nl].val = atof("nan");
  vals[nl].delta = 0;
  return nl;
}

void copy(val *new, const volatile val *vals, int len)
{
  int c = 0;

  do new[c] = vals[c];
  while (!isnan(vals[c].val) && ++c < len);
}

void fix_maxmin(double *min, double *max, double factor, double offset)
{
  *min = (*min - offset) / factor;
  *max = (*max - offset) / factor;
  if (*max < *min) {
    double tmp = *max;
    *max = *min;
    *min = tmp;
  }
}

double fun_average(const volatile val *vals, int len,
		   double factor, double offset, double discard,
		   double min, double max)
{
  double sum = 0;
  val local[len + 1];
  int c, nl;

  if (!vals || !len)
    return atof("nan");

  copy(local, vals, len + 1);
  fix_maxmin(&min, &max, factor, offset);
  nl = sorttrim(local, discard, min, max, len);
  for (c = 0; c < nl; c++)
    sum += local[c].val;

  return factor * sum / c + offset;
}

double fun_mode(const volatile val *vals, int len,
		double factor, double offset, double discard,
		double min, double max)
{
  double sum = 0;
  val local[len + 1];
  int count[len + 1];
  int c, nl, x, maxcount, n;

  if (!vals || !len)
    return atof("nan");

  memset(count, 0, sizeof(count));
  copy(local, vals, len + 1);
  fix_maxmin(&min, &max, factor, offset);
  nl = sorttrim(local, discard, min, max, len);

  for (x = c = 0; c < nl; c++) {
    count[x]++;
    local[x].val = local[c].val;
    if (c < nl - 1)
      x += local[c].val != local[c+1].val;
  }

  for (maxcount = c = 0; c <= x; c++)
    if (count[c] > maxcount)
      maxcount = count[c];

  for (n = c = 0; c <= x; c++)
    if (count[c] == maxcount) {
      sum += local[c].val;
      n++;
    }

  return factor * sum / n + offset;
}

double fun_max(const volatile val *vals, int len,
	       double factor, double offset, double discard,
	       double min, double max)
{
  val local[len + 1];
  
  if (!vals || !len)
    return atof("nan");

  copy(local, vals, len + 1);
  fix_maxmin(&min, &max, factor, offset);
  return local[sorttrim(local, discard, min, max, len) - 1].val * factor + offset;
}

double fun_min(const volatile val *vals, int len,
	       double factor, double offset, double discard,
	       double min, double max)
{
  val local[len + 1];

  if (!vals || !len)
    return atof("nan");

  copy(local, vals, len + 1);
  fix_maxmin(&min, &max, factor, offset);
  sorttrim(local, discard, min, max, len);
  return local[0].val * factor + offset;
}

double fun_deltarate(const volatile val *vals, int len,
		     double timeunit, int rate)
{
  double res;
  double changedelta;

  if (!vals || !len)
    return atof("nan");

  changedelta = vals[len-1].changedelta2 + vals[len-1].changedelta;

  res = vals[len-1].inc * 1000 * (timeunit ? timeunit : 1) / vals[len-1].incdelta;

  if (vals[len-1].inc < 2 && rate) {
    double res2 = 1000 * (timeunit ? timeunit : 1) / changedelta;
    res = res < res2 && res > 0 ? res : res2;
  }

  if (res < 0)
    res = 0;

  return res;
}

double fun_rate(const volatile val *vals, int len, double timeunit)
{
  return fun_deltarate(vals, len, timeunit, 1);
}

double fun_delta(const volatile val *vals, int len, double timeunit)
{
  return fun_deltarate(vals, len, timeunit, 0);
}

double fun_maxdelta(const volatile val *vals, int len,
		    double timeunit, double offset, double discard,
		    double min, double max)
{
  val local[len + 1];
  int i;
  
  if (!vals || !len)
    return atof("nan");

  copy(local, vals, len + 1);

  for (i = 0; i < len; i++)
    local[i].val = timeunit == 0 ? local[i].diff :
      local[i].diff * timeunit * 1000 / local[i].delta;

  return local[sorttrim(local, discard, min - offset, max - offset, len) - 1].val + offset;
}

double fun_events(const volatile val *vals, int len,
		  double factor, double offset)
{
  int i, c;
  
  if (!vals || !len)
    return atof("nan");

  for (c = i = 0; i < len; i++)
    c += vals[i].diff != 0;

  return c * factor + offset;
}

double fun_pressure(const volatile val *vals, int len1,
		    const volatile val *vals2, int len2,
		    double factor1, double factor2,
		    double offset1, double offset2,
		    double discard1, double discard2,
		    double min1, double min2,
		    double max1, double max2)
{
  double sum1 = 0, sum2 = 0;
  val local1[len1 + 1];
  val local2[len2 + 1];
  int c1, c2, nl1, nl2;
  double pressure, temp;

  if (!vals || !vals2 || !len1 || !len2)
    return atof("nan");
    
  copy(local1, vals, len1 + 1);
  copy(local2, vals2, len2 + 1);
  fix_maxmin(&min1, &max1, factor1, 0);
  fix_maxmin(&min2, &max2, factor2, offset2);
  nl1 = sorttrim(local1, discard1, min1, max1, len1);
  nl2 = sorttrim(local2, discard2, min2, max2, len2);
  for (c1 = 0; c1 < nl1; c1++)
    sum1 += local1[c1].val;
  for (c2 = 0; c2 < nl2; c2++)
    sum2 += local2[c2].val;

  pressure = factor1 * sum1 / c1 + offset1;
  temp = sum2 / c2 + offset2 + 273.1;

  return pressure / exp((-9.80665 * 0.0289644 * factor2) / (8.31432 * temp));
}

double fun_direction(volatile val *const vals[VALARR_SIZE], int len1,
		     const volatile val *vals2, int len2,
		     double factor, double offset)
{
  int i = 0, j;
  double nan = atof("nan");
  double dir = nan, x = 0, y = 0;
  double lastdir = nan;
  int valid_dir = 0;

  if (!vals || !len1)
    return nan;

  for (i = 0; i < 4; i++)
    if (!vals[i])
      return nan;

  for (i = 0; i < len1; i++) {
    double m, a, b, c, d, speed;
    signed char lookup[] = {
      -1, -1, -1, -1, -1, -1, -1, -1,  3,
      -1, -1, -1, -1, -1, -1, -1, -1, -1,
      -1, -1, -1, -1, -1, -1, -1,  5,  4,
      -1, -1, -1, -1, -1, -1, -1, -1, -1,
      -1, -1, -1, -1, -1, -1, -1, -1, 11,
      -1, -1, -1, -1, -1, -1, 13, -1, 12,
      -1, -1,  1, -1, -1, -1, -1, -1,  2,
      -1, -1, -1, -1, -1,  9, -1, -1, 10,
      15, -1,  0, -1,  7,  8, 14,  6, -1 };

    /* Normalise */
    m = vals[0][i].val;
    if (vals[1][i].val > m) m = vals[1][i].val;
    if (vals[2][i].val > m) m = vals[2][i].val;
    if (vals[3][i].val > m) m = vals[3][i].val;
    a = vals[0][i].val / m;
    b = vals[1][i].val / m;
    c = vals[2][i].val / m;
    d = vals[3][i].val / m;

#if 0
    dir = factor / 16 * lookup[(a > 0.25 ? (a > 0.75 ? 2 : 1) : 0) * 27 +
			       (b > 0.25 ? (b > 0.75 ? 2 : 1) : 0) * 9  +
			       (c > 0.25 ? (c > 0.75 ? 2 : 1) : 0) * 3  +
			       (d > 0.25 ? (d > 0.75 ? 2 : 1) : 0)];
    if (dir < 0)
      continue;
#else    
    /* Calculate bearing, based on Oww */
    dir = factor / 16 * (a < 0.26 ? (b < 0.505 ? 11 : (d < 0.755 ? 13 : 12)) : (b < 0.26 ? (c < 0.505 ? 9 : 10) : (c < 0.26 ? (d < 0.505 ? 7 : 8) : (d < 0.26 ? (a < 0.755 ? 5 : 6) : (d < 0.84 ? (c < 0.84 ? 15 : 14) : (a < 0.845 ? (b < 0.845 ? 3 : 4) : (b > 0.84 ? 0 : (c > 0.845 ? 2 : 1))))))));
#endif

    /* Check for stuck vane */
    if (dir != lastdir && !isnan(lastdir))
      valid_dir = 1;
    lastdir = dir;

    if (!vals2 || !len2)
      speed = 1;
    else { /* Find the corresponding speed */
      for (j = vals2[0].delta == 0; j < len2 && vals2[j].update < vals[0][i].update; j++);
      speed = vals2[j].delta == 0 ? 0 : vals2[j].diff / vals2[j].delta;
    }
    j -= j == len2;
    if (speed == 0.0)
      speed = 0.00001;

    /* Add vector */
    x += cos(dir / 180 * 3.1415926535) * speed;
    y += sin(dir / 180 * 3.1415926535) * speed;
  }

  if (!valid_dir)
    return nan;

  return x == 0 && y == 0 ? dir :
    fmod(atan2(y, x) * factor / 2 / 3.1415926535 + offset*360/factor + 360, 360) * factor / 360;
}

double fun_averagediff(const volatile val *vals, int len1,
		       const volatile val *vals2, int len2,
		       double factor1, double factor2,
		       double offset1, double offset2,
		       double discard1, double discard2,
		       double min1, double min2,
		       double max1, double max2)
{
  double sum1 = 0, sum2 = 0;
  val local1[len1 + 1];
  val local2[len2 + 1];
  int c1, c2, nl1, nl2;

  if (!vals || !vals2 || !len1 || !len2)
    return atof("nan");
    
  copy(local1, vals, len1 + 1);
  copy(local2, vals2, len2 + 1);
  fix_maxmin(&min1, &max1, factor1, offset1);
  fix_maxmin(&min2, &max2, factor2, offset2);
  nl1 = sorttrim(local1, discard1, min1, max1, len1);
  nl2 = sorttrim(local2, discard2, min2, max2, len2);
  for (c1 = 0; c1 < nl1; c1++)
    sum1 += local1[c1].val;
  for (c2 = 0; c2 < nl2; c2++)
    sum2 += local2[c2].val;

  return (factor1 * sum1 / c1 + offset1) - (factor2 * sum2 / c2 + offset2);
}

double fun_deltadiff(const volatile val *vals1, int len1,
		     const volatile val *vals2, int len2,
		     double timeunit1, double timeunit2)
{
  return fun_deltarate(vals1, len1, timeunit1, 0) -
    fun_deltarate(vals2, len2, timeunit2, 0);
}

double fun_ratediff(const volatile val *vals1, int len1,
		     const volatile val *vals2, int len2,
		     double timeunit1, double timeunit2)
{
  return fun_deltarate(vals1, len1, timeunit1, 1) -
    fun_deltarate(vals2, len2, timeunit2, 1);
}

double fun_lcd(function *fun, const char *file, const char *format,
	       sensor *sensor, unsigned int numfun)
{
  char timestamp2[80];
  char f[256];
  int i, j, k;
  char tmp = 0;

  strncpy(f, format, sizeof(f));
  f[sizeof(f) - 1] = 0;

  for (i = j = 0; i < sizeof(sensor->message) - 1 && f[j]; j++) {
    unsigned int ref;
    while ((f[j] < '0' || f[j] > '9') && f[j])
      sensor->message[i++] = f[j++];
    if (!f[j])
      break;
    ref = atoi(f + j);
    while ((f[j] >= '0' && f[j] <= '9') && f[j]) j++;
    if (ref == 0) {
      struct tm t;
      for (k = 0; f[j + k] && f[j + k] != ' '; k++);
      tmp = f[j + k];
      f[j + k] = 0;
      strptime(timestamp, dateformat, &t);
      strftime(timestamp2 + i, sizeof(timestamp), f + j, &t);
      i += snprintf(sensor->message + i, sizeof(sensor->message) - i, "%s", timestamp2);
      j += k - 1;
      if (tmp && f[j])
	f[j + 1] = tmp;
   } else {
      ref--;
      for (k = 0; f[j + k] && f[j + k] != 'f'; k++);
      if (ref >= numfun) {
	i += snprintf(sensor->message + i, sizeof(sensor->message), "nan");
      } else {
	tmp = 0;
	if (f[j + k]) {
	  tmp = f[j + k + 1];
	  f[j + k + 1] = 0;
	}
	i += snprintf(sensor->message + i, sizeof(sensor->message) - i, f + j, fun[ref].retvalue);
	j += k;
	if (tmp && f[j])
	  f[j + 1] = tmp;
      }
    }
  }
  sensor->message[i] = 0;
  return atof("nan");
}

time_t mtime()
{
  struct timeval tv;
  gettimeofday(&tv, NULL);
  return tv.tv_sec * 1000 + tv.tv_usec / 1000;
}

int thread_sleep(unsigned int ms)
{
  struct timeval tv;

  if (ms < 100) ms = 100;
  tv.tv_sec = ms / 1000;
  tv.tv_usec = ms % 1000 * 1000;
  select(0, NULL, NULL, NULL, &tv);
  return ms < 0 ? 0 : select(0, NULL, NULL, NULL, &tv);
}

void cancel_handler(void *parm)
{
  if (parm)
    free(parm);
}

void disable_interrupt()
{
  if (threads)
    pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, NULL);
  else {
    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGHUP);
    sigaddset(&mask, SIGINT);
    sigprocmask(SIG_BLOCK, &mask, NULL);
  }
}

void enable_interrupt()
{
  if (threads)
    pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL);
  else {
    sigset_t mask;
    sigemptyset(&mask);
    sigprocmask(SIG_SETMASK, &mask, NULL);
  }
}

unsigned int basenamelength(const char *s)
{
  unsigned int res1, res2, pos;

  while (*s == '/') s++;
  if (!strncmp(s, "uncached/", 9))
    s += 9;

  for (res1 = res2 = pos = 0; *s; pos++)
    if (*s++ == '/') {
      res2 = res1;
      res1 = pos;
    }

  return res2;
}

int queue_supervisor(unsigned int ms)
{
  time_t start = mtime();
  time_t now = start;
  const char *prevpath = 0;

  while (now - start <= ms) {
    int i, next = -1;
    int qlen;
    time_t first = 0;
    time_t remaining = ms - (now - start), remaining2;
    struct timespec timeout;
    struct timeval tv;

    /* Only wait up to 25% of the log interval for locks */
    remaining2 = remaining;
    if (remaining2 > log_interval * 250)
      remaining2 = log_interval * 250;

    gettimeofday(&tv, NULL);
    timeout.tv_nsec = tv.tv_usec * 1000 + remaining2 % 1000 * 1000000;
    timeout.tv_sec = tv.tv_sec + remaining2 / 1000 + timeout.tv_nsec / 1000000000;
    timeout.tv_nsec %= 1000000;

    /* Search for next request to process */
    for (qlen = i = 0; i < QUEUE_SIZE; i++) {
      if (semtrywait(i*2+0)) {
	if (queue[i].locktime && (first == 0 || queue[i].locktime < first)) {
	  unsigned int len = basenamelength(queue[i].path);
	  qlen++;
	  first = queue[i].locktime;
	  next = i;

	  /* 5 second priority to uncached files */
	  if (queue[i].path[0] == 'u' && queue[i].path[1] == 'n' &&
	      queue[i].path[2] == 'c' && queue[i].path[3] == 'a' &&
	      queue[i].path[4] == 'c' && queue[i].path[5] == 'h' &&
	      queue[i].path[6] == 'e' && queue[i].path[7] == 'd')
	    first -= 5000;

	  /* 2 second priority to write function */
	  if (queue[i].path[0] == '*') {
	    first -= 2000;
	    if (queue[i].path[1] == 'u' && queue[i].path[2] == 'n' &&
		queue[i].path[3] == 'c' && queue[i].path[4] == 'a' &&
		queue[i].path[5] == 'c' && queue[i].path[6] == 'h' &&
		queue[i].path[7] == 'e' && queue[i].path[8] == 'd')
	      first -= 5000;
	  }

	  /* 5 second priority to files sharing branch with the previous */
	  if (len && prevpath && !strncmp(queue[i].path, prevpath, len))
	      first -= 5000;
	}
      } else
	sempost(i*2+0);
    }

    if (next >= 0) {

      if (debug > 1)
	printf("Queue length: %d - next: %s\n", qlen, queue[next].path);

      prevpath = queue[next].path;

      /* Wake up the holder of the lock */
      sempost(next*2+1);

      /* Wait for the holder to release the lock */
      if (semtimedwait(next*2+0, &timeout))
	if (errno != ETIMEDOUT && semwait(next*2+0))
	  return 0;

      if (errno == ETIMEDOUT && debug > 0)
	printf("Timeout: %s\n", queue[next].path);

      sempost(next*2+0);
      queue[next].ack = 1;
    } else
      thread_sleep(remaining > 100 ? 100 : remaining);

    now = mtime();
  }
  return 0;
}

ssize_t OW_getput_queued(int get, const char *path, char **buffer,
			 size_t *buffer_length)
{
  int i;
  ssize_t ret;

  /* Find a free lock */
  for (i = 0; i < QUEUE_SIZE; i++)
    if (queue[i].ack && !semtrywait(i*2+0))
	break;

  if (i == QUEUE_SIZE)
    return -1;

  queue[i].path = path;
  queue[i].locktime = mtime();
  queue[i].locktime += !queue[i].locktime;

  /* Wait till the supervisor says go */
  semwait(i*2+1);

  /* Query owserver */
  ret = get ? OW_get(path, buffer, buffer_length) :
    OW_put(path, *buffer, *buffer_length);

  queue[i].locktime = 0;

  /* Unlock and return */
  queue[i].ack = 0;
  sempost(i*2+0);
  return ret;
}

ssize_t OW_get_queued(const char *path, char **buffer, size_t *buffer_length)
{
  return OW_getput_queued(1, path, buffer, buffer_length);
}

ssize_t OW_put_queued(const char *path, const char *buffer, size_t buffer_length)
{
  char *buf = (char*)buffer;
  return OW_getput_queued(0, path, &buf, &buffer_length);
}

void sensor_read(char **buf, sensor *s, int i)
{
  size_t size;
  int j;
  int retry = 1000;

  while ((queueing ? OW_get_queued : OW_get)(s->file, buf, &size) == -1) {
    thread_sleep(retry);
    retry += 1000;
    if (debug > 1)
      printf("%s: retry\n", s->file);
  }
  if (debug > 0)
    printf("%s: ", s->file);
  if (debug > 0) {
    if (*buf)
      printf("%s", *buf);
    printf("\n");
  }

  if (*buf) {
    double newval;
    char *buf2 = *buf;
    time_t now = mtime();

    disable_interrupt();

    for (j = 0; j < VALARR_SIZE; j++) {
      sscanf(buf2, "%lf", &newval);
      s->vals[j][i].val = newval + s->shift;
      while (*buf2 && *buf2 != ',')
        buf2++;
      if (!*buf2)
        break;
      buf2++;
    }

    free(*buf);
    *buf = NULL;

    if (s->update == 0)
      s->lastupdate = now;

    if (i == 0)
      s->prevupdate = s->lastupdate;

    for (j = 0; j < VALARR_SIZE; j++) {
      if (i == 0)
	s->prevval[j] = s->lastval[j];

      if (s->update == 0)
        s->prevval[j] = newval;

      s->vals[j][i].inc = newval - s->prevval[j];
      s->vals[j][i].incdelta = now - s->prevupdate;

      if (newval != s->lastval[j])
	s->changedelta2[j] = s->changedelta[j];

      s->changedelta[j] = s->changed[j] ? now - s->changed[j] : atof("inf");

      if (s->changedelta2[j] == 0)
	s->changedelta2[j] = s->changedelta[j];

      s->vals[j][i].changedelta = s->changedelta[j];
      s->vals[j][i].changedelta2 = s->changedelta2[j];

      if (newval != s->lastval[j])
	s->changed[j] = now;

      s->vals[j][i].diff = s->update ? newval - s->lastval[j] : 0;
      s->vals[j][i].delta = now - s->update;
      s->lastval[j] = newval;
    }
    s->lastupdate = now;
    s->update = now;

    enable_interrupt();
  }
}

void sensor_loop(sensor *s, char **buf)
{
  int i = 0;
  time_t exit = mtime() + log_interval * 1000 - 1000;
  time_t now, next = mtime() + s->interval * 1000;
  unsigned int slen = strlen(s->file);

  /* Special test for write function */
  if (*s->file == '*') {
    int retry = 1000;

    do {
      thread_sleep(100);
      now = mtime();
      if (next > now && next < exit) {
	thread_sleep(next - now);
	next += s->interval * 1000;
      } else
	next = now + s->interval * 1000;
      while ((queueing ? OW_put_queued : OW_put)(s->file + 1, s->message, sizeof(s->message)) == -1) {
	if (debug > 1)
	  printf("%s: retry\n", s->file + 1);
	thread_sleep(retry);
	retry += 1000;
      }
      if (debug > 0)
	printf("%s: %s\n", s->file + 1, s->message);
      now = mtime();
    } while (next < exit && now < exit && s->interval >= 0);

    return;
  }

  /* Special test for LCD display */
  if (!strcmp(s->file + slen - 7, "message")) {
    int retry = 1000;

    while ((queueing ? OW_put_queued : OW_put)(s->file, s->message, sizeof(s->message)) == -1) {
      
      thread_sleep(retry);
      retry += 1000;
    }
    if (debug > 0)
      printf("%s: %s\n", s->file, s->message);

    return;
  }

  /* First time read */
  if (s->update == 0)
    sensor_read(buf, s, i++);

  do {
    /* Special test for humidity: reset clock if humidity < 90 */
    if (i == 1 && !strcmp(s->file + slen - 8, "humidity")) {
      int retry = 1000;
      char backup[6];
      unsigned int index;
      index = slen - (strcmp(s->file + slen - 16, "HIH4000/humidity") ? 8 : 16);
      memcpy(backup, s->file + index, 6);
      memcpy(s->file + index, "udate", 6);
      if (s->vals[0][0].val - s->shift < 90) {
	while ((queueing ? OW_put_queued : OW_put)(s->file, "0", sizeof(s->message)) == -1) {
	  thread_sleep(retry);
	  retry += 1000;
	}
	if (debug > 0)
	  printf("%s: 0\n", s->file);
	
	s->shift = 0;
      } else {
	size_t size;
	while ((queueing ? OW_get_queued : OW_get)(s->file, buf, &size) == -1) {
	  thread_sleep(retry);
	  retry += 1000;
	}
	if (*buf) {
	  unsigned int udate;
	  sscanf(*buf, "%u", &udate);

	  if (debug > 0)
	    printf("%s: %u\n", s->file, udate);

	  if (udate > 3600 * 9)
	    udate = 3600 * 9;

	  /* Add a shift down to -3.0 if humidity stays above 90% */
	  s->shift = -(double)udate / 3600.0 / 3;

	  free(*buf);
	  *buf = NULL;
	}
      }
      memcpy(s->file + index, backup, 6);
    }

    thread_sleep(100);
    now = mtime();
    if (next > now && next < exit) {
      thread_sleep(next - now);
      next += s->interval * 1000;
    } else
      next = now + s->interval * 1000;
    sensor_read(buf, s, i++);
    now = mtime();
  } while (next < exit && now < exit && s->interval >= 0);
}

void *log_sensor(void *ptr)
{
  sensor *s = (sensor*)ptr;
  char *buf = NULL;

  if (threads) {
    pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL);
    pthread_cleanup_push(cancel_handler, buf);

    sensor_loop(s, &buf);

    pthread_cleanup_pop(0);
  } else {
    sensor_buf = buf;
    sensor_loop(s, &buf);
  }

  return NULL;
}


/*
 * name: function name (average, mode, max, min, delta, rate, maxdelta, events, direction, averagediff, deltadiff, ratediff, lcd, pressure)
 * source, source2: sources (e.g. server:3001)
 * file, file2: filenames (e.g. /28.6518A3000000/temperature)
 * format: formatting code (e.g. %.3f)
 * interval: time between each read in seconds (0 = read once)
 * farg1, farg1b: calibration factor(s) or delta unit in seconds
 * farg2, farg2b: calibration offsets(s)
 * farg3, farg3b: percentage to discard of maximum and minimum values
 * farg4, farg4b: discard samples below this/these value(s)
 * farg5, farg5b: discard samples above this/these value(s)
 *
 */
void process(FILE *outf, function *functions, unsigned int numfun)
{
  int l1, l2;
  int i;

  for (i = 0; i < count; i++) {

    function *f = functions + i;

    for (l1 = 0; f->vals[0] && !isnan(f->vals[0][l1].val); l1++);
    for (l2 = 0; f->vals2[0] && !isnan(f->vals2[0][l2].val); l2++);
    
    /* Default return value */
    f->retvalue = atof("nan");

    if (!strcmp(f->name, "average"))
      f->retvalue = fun_average(f->vals[0], l1, f->farg1, f->farg2, f->farg3, f->farg4, f->farg5);
    else if (!strcmp(f->name, "mode"))
      f->retvalue = fun_mode(f->vals[0], l1, f->farg1, f->farg2, f->farg3, f->farg4, f->farg5);
    else if (!strcmp(f->name, "max"))
      f->retvalue = fun_max(f->vals[0], l1, f->farg1, f->farg2, f->farg3, f->farg4, f->farg5);
    else if (!strcmp(f->name, "min"))
      f->retvalue = fun_min(f->vals[0], l1, f->farg1, f->farg2, f->farg3, f->farg4, f->farg5);
    else if (!strcmp(f->name, "rate"))
      f->retvalue = fun_rate(f->vals[0], l1, f->farg1);
    else if (!strcmp(f->name, "delta"))
      f->retvalue = fun_delta(f->vals[0], l1, f->farg1);
    else if (!strcmp(f->name, "maxdelta"))
      f->retvalue = fun_maxdelta(f->vals[0], l1, f->farg1, f->farg2, f->farg3, f->farg4, f->farg5);
    else if (!strcmp(f->name, "events"))
      f->retvalue = fun_events(f->vals[0], l1, f->farg1, f->farg2);
    else if (!strcmp(f->name, "direction"))
      f->retvalue = fun_direction(f->vals, l1, f->vals2[0], l2, f->farg1, f->farg2);
    else if (!strcmp(f->name, "averagediff"))
      f->retvalue = fun_averagediff(f->vals[0], l1, f->vals2[0], l2,
				    f->farg1, f->farg1b,
				    f->farg2, f->farg2b, f->farg3, f->farg3b,
				    f->farg4, f->farg4b, f->farg5, f->farg5b);
    else if (!strcmp(f->name, "pressure"))
      f->retvalue = fun_pressure(f->vals[0], l1, f->vals2[0], l2,
				 f->farg1, f->farg1b,
				 f->farg2, f->farg2b, f->farg3, f->farg3b,
				 f->farg4, f->farg4b, f->farg5, f->farg5b);
    else if (!strcmp(f->name, "deltadiff"))
      f->retvalue = fun_deltadiff(f->vals[0], l1, f->vals2[0], l2,
				  f->farg1, f->farg1b);
    else if (!strcmp(f->name, "ratediff"))
      f->retvalue = fun_ratediff(f->vals[0], l1, f->vals2[0], l2,
				 f->farg1, f->farg1b);
    else if (!strcmp(f->name, "dummy")) {
      f->entry[0] = '\t';
      strncpy(f->entry + 1, f->source, sizeof(f->entry) - 1);
      f->retvalue = atof(f->source);
    }

    if (f->format && strcmp(f->name, "lcd") &&
	f->format && strcmp(f->name, "write") &&
	f->format && strcmp(f->name, "hexwrite")) {
      f->entry[0] = '\t';
      snprintf(f->entry + 1, sizeof(f->entry) - 1, f->format, f->retvalue);
    } else
      if (strcmp(f->name, "dummy"))
	f->entry[0] = 0;

    f->entry[sizeof(f->entry) - 1] = 0;
    
    fprintf(outf, "%s", f->entry);
  }

  /* Since the lcd functions depends on the result of the other functions,
     process them in a seperate pass */
  for (i = 0; i < count; i++)
    if (!strcmp(functions[i].name, "lcd")) {
      functions[i].retvalue = fun_lcd(functions, functions[i].file,
				      functions[i].format, functions[i].sensor,
				      numfun);
    }

}

int strequal(const char *s, const char *t)
{
  return !strcmp(s, t) && strlen(s) == strlen(t);
}

unsigned int label_unique(function *functions, int count, int *s, int *f)
{
  int i;
  int sourceid = 0;
  int fileid = 0;

  for (i = 0; i < count; i++)
    functions[i].sourceid = functions[i].sourceid2 =
      functions[i].fileid = functions[i].fileid2 = -1;

  /* Label unique sources */
  for (i = 0; i < count; i++) {
    int j;
    for (j = 0; j <= i; j++) {
      if (strequal(functions[i].source, functions[j].source))
	functions[i].sourceid = functions[j].sourceid;
      else if (strequal(functions[i].source, functions[j].source2))
	functions[i].sourceid = functions[j].sourceid2;
      if (strequal(functions[i].source2, functions[j].source))
	functions[i].sourceid2 = functions[j].sourceid;
      else if (strequal(functions[i].source2, functions[j].source2)) {
	functions[i].sourceid2 = functions[j].sourceid2;
      }
    }

    if (functions[i].sourceid == -1 && *functions[i].file)
      functions[i].sourceid = sourceid++;
    if (strequal(functions[i].source, functions[i].source2))
      functions[i].sourceid2 = functions[i].sourceid;
    else if (functions[i].sourceid2 == -1 && * functions[i].file2)
      functions[i].sourceid2 = sourceid++;
  }

  /* Label unique files */
  for (i = 0; i < count; i++) {
    int j;
    for (j = 0; j <= i; j++) {
      if (strequal(functions[i].file, functions[j].file))
	functions[i].fileid = functions[j].fileid;
      else if (strequal(functions[i].file, functions[j].file2))
	functions[i].fileid = functions[j].fileid2;
      if (strequal(functions[i].file2, functions[j].file))
	functions[i].fileid2 = functions[j].fileid;
      else if (strequal(functions[i].file2, functions[j].file2)) {
	functions[i].fileid2 = functions[j].fileid2;
      }
    }

    if (functions[i].fileid == -1 && *functions[i].file)
      functions[i].fileid = fileid++;
    if (strequal(functions[i].file, functions[i].file2))
      functions[i].fileid2 = functions[i].fileid;
    else if (functions[i].fileid2 == -1 && *functions[i].file2)
      functions[i].fileid2 = fileid++;
  }

  *s = sourceid;
  *f = fileid;

  return fileid;
}

void signal_handler(int sig)
{
  if (!threads) {
    if (sensor_buf)
      free(sensor_buf);
    sensor_buf = NULL;
  } else
    kill(0, sig);

  if (functions) {
    int i;
    for (i = 0; i < count; i++) {
      free(functions[i].name);
      free(functions[i].files);
      free(functions[i].format);
    }
    free(functions);
    functions = NULL;
  }

  if (semid && ipcpid == getpid())
    semctl(semid, 0, IPC_RMID);
  semid = 0;

  exit(sig);
}

unsigned int parse_directories(unsigned int max_depth, char *directories,
			       int max_length, char *start, int top)
{
  char *buffer = 0;
  size_t buffer_length;
  ssize_t ret = -1;
  int retry = log_interval;
  int i;
  int totlen = 0;

  directories[0] = 0;

  if (max_depth < 1 || max_length < 1)
    return 0;

  while (ret == -1 && --retry > 0) {
    ret = OW_get(start ? start : "/", &buffer, &buffer_length);
    if (ret == -1 && !top)
      return 0;
    if (ret == -1)
      thread_sleep(1000);
  }
  for (i = 0; i < buffer_length - 3; i++)
    if (buffer[i+0] == '1' && buffer[i+2] == '.' &&
	(buffer[i+1] == 'F' || buffer[i+1] == 'f')) {
      int j, k, len;
      static char mn[] = "/main/";
      static char aux[] = "/aux/";
      for (j = 0; buffer[i + j] != '/' && j + i < buffer_length && max_length > 0; j++) {
	directories[j] = buffer[i + j];
	max_length--;
      }
      for (k = 0; mn[k] && max_length > 0; k++) {
	directories[j++] = mn[k];
	max_length--;
      }
      directories[j] = 0;
      len = parse_directories(max_depth - 1, directories + j,
			      max_length, directories, 0);
      if (max_length > 0) {
	directories[j++] = ',';
	directories[j] = 0;
	max_length--;
      }
      directories += len + j;
      totlen += len + j;

      for (j = 0; buffer[i + j] != '/' && j + i < buffer_length && max_length > 0; j++) {
	directories[j] = buffer[i + j];
	max_length--;
      }
      for (k = 0; aux[k] && max_length > 0; k++) {
	directories[j++] = aux[k];
	max_length--;
      }
      directories[j] = 0;
      len = parse_directories(max_depth - 1, directories + j,
			      max_length, directories, 0);
      if (max_length > 0) {
	directories[j++] = ',';
	directories[j] = 0;
	max_length--;
      }
      directories += len + j;
      totlen += len + j;
    }

  free(buffer);
  return totlen;
}

void search_sensors(sensor *sensors, unsigned int s, char *directories, int sourceid)
{
  char scratch[256];
  static char uncached[] = "uncached/";
  char *scratch2;
  int i, j;

  if (debug > 1 && *directories)
    printf("Searching for files in directories %s:\n", directories);

  if (!*directories) {
    if (debug > 1)
      printf("\n");
    return;
  }

  while (directories[0] && directories[1]) {
    const char *cursens;
    for (j = 0; directories[j] != ',' && j < 256; j++);
    directories[j] = 0;

    for (i = 0; i < s; i++) {
      ssize_t ret;
      char *buffer = 0;
      size_t buffer_length;

      if (sensors[i].sourceid != sourceid)
	continue;

      strcpy(scratch, uncached);
      if (sensors[i].file[0] == 'u' && sensors[i].file[1] == 'n' &&
	  sensors[i].file[2] == 'c' && sensors[i].file[3] == 'a' &&
	  sensors[i].file[4] == 'c' && sensors[i].file[5] == 'h' &&
	  sensors[i].file[6] == 'e' && sensors[i].file[7] == 'd' &&
	  sensors[i].file[8] == '/') {
	cursens = sensors[i].file + sizeof(uncached) - 1;
	scratch2 = scratch + sizeof(uncached) - 1;
      } else {
	cursens = sensors[i].file;
	scratch2 = scratch;
      }
      if (directories[1])
	strncpy(scratch2, directories, sizeof(scratch) - (scratch2 - scratch));
      else
	scratch2[0] = 0;
      scratch[sizeof(scratch) - 1] = 0;
      strncat(scratch, cursens, sizeof(scratch) - strlen(scratch));
      ret = OW_get(scratch, &buffer, &buffer_length);
      if (ret != -1) {
	if (debug > 1)
	  printf("  Match: %s is %s\n", cursens, scratch);
	strcpy(sensors[i].file, scratch);
	free(buffer);
      }
    }
    directories[j++] = ',';
    directories += j;
  }
  if (debug > 1)
    printf("\n");
}

/* Read configuration file */
function *readconf(const char **argv, const char *conf, int *c)
{
  regex_t regexp;
  int count, rc, i, j, k;
  FILE *inf = fopen(conf, "r");
  char s[1024];
  function *functions = malloc(sizeof(function) * 64);

  if (!functions || !inf || !c)
    return 0;
  
  if ((rc = regcomp(&regexp, "^[\t ]*([a-z]+)\\((.*)\\)", REG_EXTENDED | REG_ICASE)) != 0) {
    char buffer[100];
    regerror(rc, &regexp, buffer, sizeof(buffer));
    printf("%s: regcomp() failed: '%s'\n", argv[0], buffer);
    return 0;
  }

  for (count = 0; fgets(s, sizeof(s), inf);) {
    char *s2;
    regmatch_t matches[3];

    s[sizeof(s) - 1] = 0;
    if (!regexec(&regexp, s, sizeof(matches) / sizeof(regmatch_t), matches, 0)) {
      
      functions[count].name = malloc(strlen(s + matches[1].rm_eo - matches[1].rm_so + 1));
      if (!functions[count].name) {
	fprintf(stderr, "%s: malloc failed\n", argv[0]);
	exit(EXIT_FAILURE);
      }
      strncpy(functions[count].name, s + matches[1].rm_so, matches[1].rm_eo - matches[1].rm_so + 1);
      functions[count].name[matches[1].rm_eo - matches[1].rm_so] = 0;
      s[matches[2].rm_eo] = 0;
      s2 = s + matches[2].rm_so;
      
      /* Assign default values */
      functions[count].file = functions[count].format = NULL;
      functions[count].interval = 10;
      functions[count].farg1 = 1;	
      if (!strcmp(functions[count].name, "direction"))
	functions[count].farg1 = 360;
      functions[count].farg2 = functions[count].farg3 = 0;
      functions[count].farg4 = functions[count].farg4b = atof("-inf");
      functions[count].farg5 = functions[count].farg5b = atof("+inf");
      
      /* Read remaining arguments */
      for (j = 0; *s2 && *s2 != '\n' && j < 8; j++) {
	if (strcmp(functions[count].name, "dummy"))
	  while (*s2 == ' ' || *s2 == '\t') { s2++; }
	for (i = 0; s2[i] != ',' && s2[i]; i++);
	
	switch (j) {
	  
	case 0:
	  /* Make room to add 1F.XXXXXXXXXXXXxx/main/ */
	  functions[count].file = functions[count].files =
	    malloc(i + 1 + 23 + 23 * 2 * max_depth);
	  if (!functions[count].file) {
	    fprintf(stderr, "%s: malloc failed\n", argv[0]);
	    exit(EXIT_FAILURE);
	  }

	  if (strcmp(functions[count].name, "dummy")) {
	    for (k = 0; k < i && s2[k] != ' '; k++)
	      functions[count].file[k] = s2[k];
	    memset(functions[count].file + k, ' ', 23);
	    memcpy(functions[count].file + k + 23, s2 + k, i - k);
	    functions[count].file[i + 23] = 0;
	  } else {
	    for (k = 0; k < i; k++)
	      functions[count].file[k] = s2[k];
	    functions[count].file[k] = 0;
	  }
	  break;
	  
	case 1:
	  functions[count].format = malloc(i + 1);
	  if (!functions[count].format) {
	    fprintf(stderr, "%s: malloc failed\n", argv[0]);
	    exit(EXIT_FAILURE);
	  }
	  if (strcmp(functions[count].name, "lcd") &&
	      strcmp(functions[count].name, "write") &&
	      strcmp(functions[count].name, "hexwrite"))
	    while (*s2 != '%' && *s2 && i > 0) { s2++; i--; }
	  if (i) {
	    memcpy(functions[count].format, s2, i);
	    functions[count].format[i] = 0;
	  } else
	    functions[count].format = NULL;
	  break;
	  
	case 2:
	  sscanf(s2, "%lf", &functions[count].interval);
	  break;
	  
	case 3:
	  if (sscanf(s2, "%lf %lf", &functions[count].farg1, &functions[count].farg1b) == 1)
	    functions[count].farg1b = functions[count].farg1;
	  break;
	  
	case 4:
	  if (sscanf(s2, "%lf %lf", &functions[count].farg2, &functions[count].farg2b) == 1)
	    functions[count].farg2b = functions[count].farg2;
	  break;
	  
	case 5:
	  if (sscanf(s2, "%lf %lf", &functions[count].farg3, &functions[count].farg3b) == 1)
	    functions[count].farg3b = functions[count].farg3;
	  break;
	  
	case 6:
	  
	  if (sscanf(s2, "%lf %lf", &functions[count].farg4, &functions[count].farg4b) == 1)
	    functions[count].farg4b = functions[count].farg4;
	  break;
	  
	case 7:
	  if (sscanf(s2, "%lf %lf", &functions[count].farg5, &functions[count].farg5b) == 1)
	    functions[count].farg5b = functions[count].farg5;
	  break;
	  
	default:
	  break;
	}
	s2 += i + 1;
      }

      /* Two filenames? */
      functions[count].file2 = functions[count].file;
      if (strcmp(functions[count].name, "dummy")) {
	if (functions[count].file2)
	  while (*functions[count].file2 != ' ' && *functions[count].file2)
	    functions[count].file2++;
	
	if (*functions[count].file2 == ' ') {
	  *functions[count].file2 = 0;
	  while (*++functions[count].file2 == ' ');
	}
      }
      /* Extract sources */
      functions[count].source = functions[count].file;
      while (*functions[count].file != '|' && *functions[count].file)
	functions[count].file++;
      if (*functions[count].file == '|')
	*functions[count].file++ = 0;

      functions[count].source2 = functions[count].file2;
      while (*functions[count].file2 != '|' && *functions[count].file2)
	functions[count].file2++;
      if (*functions[count].file2 == '|')
	*functions[count].file2++ = 0;

      /* Expand function list? */
      if (!(++count % 63)) {
	function *newfunctions = malloc(sizeof(function) * (count + 64));
	if (!newfunctions) {
	  fprintf(stderr, "%s: malloc failed\n", argv[0]);
	  exit(EXIT_FAILURE);
	}
	memcpy(newfunctions, functions, sizeof(function) * count);
	free(functions);
	functions = newfunctions;
      }
    }
  }
  fclose(inf);
  regfree(&regexp);
  *c = count;
  return functions;
}

int main(int argc, const char **argv)
{
  FILE *outf;
  const char *log = NULL;
  int i, j;
  int shmid;
  char **sources;
  sensor *sensors;
  pid_t child = -1;
  pid_t *children;
  int uniquesources, uniquefiles;
  volatile val *sensorvals;
  double nan = atof("nan");
  void *shm;
  const char **myargv = argv + 1;
  int orgargc = argc;
  int daemon = 0;
  const char *conf = "/etc/owfslog.conf";
  time_t now, next;
  int align = 0;
  int samples;

  /* Catch signals */
  signal(SIGHUP, signal_handler);
  signal(SIGINT, signal_handler);
  signal(SIGQUIT, signal_handler);
  signal(SIGTERM, signal_handler);
  signal(SIGABRT, signal_handler);

  /* Ignore dead children */
  signal(SIGCHLD, SIG_IGN);

  log_interval = 300;

  /* Parse options */
  while (myargv - argv < orgargc && myargv[0][0] == '-') {
    switch (myargv[0][1]) {
    case 'a':
      align = 1;
      break;
    case 'c':
      conf = *++myargv;
      argc--;
      break;
    case 'p':
      if (--argc > 1)
	max_depth = atoi(*++myargv);
      break;
    case 'f':
      dateformat = *++myargv;
      argc--;
      break;
    case 'h':
      printf("Configuration file format:\n");
      printf("\n");
      printf(" Each line produces one tabulator separated entry in the log file.\n");
      printf(" Lines beginning with \"#\" are ignored and can be used for comments.\n");
      printf("\n");
      printf(" The format is (except function \"dummy\", see below):\n");
      printf("\n");
      printf("   function(filename(s), format[, interval[, function specific arguments]])\n");
      printf("\n");
      printf("   function is one of\n");
      printf("\n");
      printf("     average(filename, format[, interval[, factor[, offset[, discard[, min[, max]]]]]])\n");
      printf("     mode(filename, format[, interval[, factor[, offset[, discard[, min[, max]]]]]])\n");
      printf("     max(filename, format[, interval[, factor[, offset[, discard[, min[, max]]]]]])\n");
      printf("     min(filename, format[, interval[, factor[, offset[, discard[, min[, max]]]]]])\n");
      printf("     delta(filename, format[, interval[, timeunit]])\n");
      printf("     maxdelta(filename, format[, interval[, timeunit[, offset[, discard[, min[, max]]]]]])\n");
      printf("     rate(filename, format[, interval[, timeunit]])\n");
      printf("     events(filename, format[, interval[, factor[, offset]]])\n");
      printf("     direction(filename(s), format[, interval[, factor[, offset]]])\n");
      printf("     averagediff(filenames, format[, interval[, factor(s)[, offset(s)[, discard(s)[, min[, max]]]]]])\n");
      printf("     pressure(filenames, format[, interval[, factor (elevation [m])[, offset (temperature offset)[, discard(s)[, min[, max]]]]]])\n");
      printf("     deltadiff(filenames, format[, interval[, timeunit(s)]])\n");
      printf("     ratediff(filenames, format[, interval[, timeunit(s)]])\n");
      printf("     lcd(filename, format)\n");
      printf("     dummy(log entry)\n");
      printf("     write(filename, text[, interval])\n");
      printf("     hexwrite(filename, text[, interval])\n");
      printf("\n");
      printf("   \"average\" logs the average of all samples that are not discarded.\n");
      printf("\n");
      printf("   \"mode\" logs the most frequent sample not discarded.\n");
      printf("\n");
      printf("   \"max\" logs the maximum of all samples that are not discarded.\n");
      printf("\n");
      printf("   \"min\" logs the minimum of all samples that are not discarded.\n");
      printf("\n");
      printf("   \"delta\" logs the average increase during the log interval per time unit.\n");
      printf("\n");
      printf("   \"maxdelta\" logs the maximum single increase during the log interval.\n");
      printf("   A zero timeunit means that no time correction is applied.\n");
      printf("\n");
      printf("   \"rate\" is like \"delta\" except when there is no increase during a log\n");
      printf("   interval, when rate will give the rate since the last increase while \"delta\"\n");
      printf("   will give 0.  \"rate\" is useful for rain rate, \"delta\" for wind speed.\n");
      printf("\n");
      printf("   \"events\" logs the number of times the sample changed during the log\n");
      printf("   interval.\n");
      printf("   \"direction\" logs the average direction of an anemometer optionally\n");
      printf("   weighed by wind speeds.\n");
      printf("\n");
      printf("   \"averagediff\" is like \"average\", except that the difference between\n");
      printf("   two given files is used.\n");
      printf("\n");
      printf("   \"pressure\" is like \"average\" assuming that the first file is a barometer\n");
      printf("   and the second is temperature in C.  The elevation in m replaces the temperature factor.\n");
      printf("\n");
      printf("   \"deltadiff\" is like \"delta\", except that the difference between two\n");
      printf("   given files is used.  Offsets are applied before subtractions.  A\n");
      printf("   zero timeunit means that no time correction is applied.\n");
      printf("\n");
      printf("   \"ratediff\" is like \"rate\", except that the difference between two\n");
      printf("   given files is used.  Offsets are applied before subtractions.  A\n");
      printf("   zero timeunit means that no time correction is applied.\n");
      printf("\n");
      printf("   \"lcd\" prints log entries to an LCD display as specified by the \"format\"\n");
      printf("   argument.\n");
      printf("\n");
      printf("   In addition the function \"dummy\" can be used to create a fixed entry in the\n");
      printf("   log file.  The function has one argument, which is the log entry.\n");
      printf("\n");
      printf("   \"filename\" is the source, the path and name of the file to read, must not\n");
      printf("   contain the \"|\", \",\" or \" \" (space) characters.  The source (such as\n");
      printf("   server:port, e.g. 1-wire:3002) must be followed by a pipe (\"|\")\n");
      printf("   immediately followed by the path and name.\n");
      printf("\n");
      printf("   \"format\" is a printf format string, only %%f type allowed (default %%.3f).\n");
      printf("   If empty, nothing will be written to the log.\n");
      printf("\n");
      printf("   If the function is \"lcd\", several %%-type entries may be specified and a\n");
      printf("   number in front of the %% must be given, which acts as a reference to which\n");
      printf("   log entry to print.  0 is the timestamp, 1 is the first (leftmost) log\n");
      printf("   entry etc.  Note that missing log entries (entries with missing format or\n");
      printf("   lcd entries) are counted.  This makes it possible to have entries written\n");
      printf("   to an LCD display that don't appear in the log.\n");
      printf("   The format for entry 0 (the timestamp) follows strftime syntax, but spaces\n");
      printf("   are not allowed.\n");
      printf("     Example: 0%%H:%%M:%%S 2%%7.3f 1%%5.1f\n");
      printf("     This will print the timestamp, the second log entry and the first.\n");
      printf("\n");
      printf("   \"interval\" is the time between each read (default: 10).  A negative\n");
      printf("   number -n sets the time to logging interval + n.  The user must ensure\n");
      printf("   that there is enough time to get a reading before logging is done.\n");
      printf("\n");
      printf("   There is an additional windspeed filename for the \"direction\" function.\n");
      printf("   If unspecified, the wind direction will be averaged without speed weighing.\n");
      printf("\n");
      printf("   The write function will write the specified text to the given gile.\n");
      printf("   The filename must be preceeded by an \'*\'\n");
      printf("\n");
      printf("   The hexwrite function is like write, but the text is interpreted as\n");
      printf("   hexadecimal numbers\n");
      printf("\n");
      printf("\n");
      printf("   Additional arguments are function specific:\n");
      printf("\n");
      printf("     factor:   Multiply the value by this number (default: 360 for direction,\n");
      printf("               1 for other functions).  For functions taking two filenames,\n");
      printf("               two values may be given separated by a space (" ").  If only\n");
      printf("               one still is given, the same value will be assumed for both\n");
      printf("               filenames.\n");
      printf("     offset:   Add the value by this number after multiplication (default: 0).\n");
      printf("               For the function direction, the value will wrap at the factor\n");
      printf("               value.  For functions taking two filenames, two values may be\n");
      printf("               given separated by a space (" ").  If only one still is given,\n");
      printf("               the same value will be assumed for both filenames.\n");
      printf("     discard:  The percentage to discard of maximum and minimum values,\n");
      printf("               0-50, 50 gives median (default: 0).  For functions taking two\n");
      printf("               filenames, two values may be given separated by a space (" ").\n");
      printf("               If only one still is given, the same value will be assumed for\n");
      printf("               both filenames.\n");
      printf("     min:      Samples below this value will be discarded, default: -inf\n");
      printf("     max:      Samples above this value will be discarded, default: +inf\n");
      printf("     timeunit: Delta unit in seconds (default: 1).  For the AAG anemometer use\n");
      printf("               the value 1.9738 to get kph.\n");
      printf("\n");
      printf(" Examples:\n");
      printf("\n");
      printf("   average(1-wire:3002|28.6518A3000000/temperature, %%.3f, 5, 1.0, 0.1, 10)\n");
      printf("     Read every 5 seconds, discard the highest 10%% and the lower 10%%,\n");
      printf("     multiply by 1, add 0.1 and write the result with 3 decimals.\n");
      printf("\n");
      printf("   max(/dev/ttyS0|1D.A1CF08000000F9/counters.B, %%.0f, -2)\n");
      printf("     Read value once 2 seconds before logging it.  With the same arguments the\n");
      printf("     functions min and average will give the same result.\n");
      printf("\n");
      printf("   write(localhost:3000|*12.8F9B53000000/PIO.A, 1, 5)\n");
      printf("     Write \"1\" to 12.8F9B53000000/PIO.A every 5 seconds.\n");
      printf("\n");
      exit(1);
    case 'l':
      log = *++myargv;
      argc--;
      break;
    case 'i':
      if (--argc > 1)
	log_interval = atoi(*++myargv);
      if (log_interval < 1)
	log_interval = 1;
      break;
    case 'u':
      if (--argc > 1)
	uid = atoi(*++myargv);
      break;
    case 'd':
      daemon = 1;
      break;
    case 'v':
      debug++;
      break;
    case 'P':
      if (--argc > 1)
	pidfile = *++myargv;
      break;
    case 'q':
      queueing_global = queueing = 1;
      posixsem = 1;
      break;
    case 'Q':
      queueing_global = queueing = 1;
      posixsem = 0;
      break;
    case 't':
      threads = 1;
      break;
    default:
      argc = 0;
      break;
    }
    argc--;
    myargv++;
  }
  
  if (argc != 1) {
    fprintf(stderr, "owfslog 0.9 by Steinar Midtskogen <steinar@latinitas.org>.\n\n");
    fprintf(stderr, "Usage: %s [options]\n", argv[0]);
    fprintf(stderr, " Valid options:\n");
    fprintf(stderr, "  -a                      : Align logging time\n");
    fprintf(stderr, "                          :  This will delay the start of the program until the\n");
    fprintf(stderr, "                          :  logging times will match those if the program had\n");
    fprintf(stderr, "                          :  been started at the epoch (1 Jan 1970 00:00:00).\n");
    fprintf(stderr, "  -c <configuration file> : Use this file rather than default /etc/owfslog.conf\n");
    fprintf(stderr, "  -d                      : Run program in the background\n");
    fprintf(stderr, "  -f <format>             : strftime time format, default: %%Y%%m%%d%%H%%M%%S\n");
    fprintf(stderr, "  -h                      : Print a description of the configuration format\n");
    fprintf(stderr, "  -i <seconds>            : Time between log updates, default: 300\n");
    fprintf(stderr, "  -l <logfile>            : Log to this file, not to stdout\n");
    fprintf(stderr, "  -p <depth>              : Depth of directory parsing\n");
    fprintf(stderr, "                          :  Normally, files need to be have a full path, but\n");
    fprintf(stderr, "                          :  this options makes owfslog search for the sensor\n");
    fprintf(stderr, "                          :  to the depth specified.  Default: 0\n");
    fprintf(stderr, "  -P <pidfile>            : Write pid to file.\n");
    fprintf(stderr, "  -q                      : Use local queueing (POSIX)\n");
    fprintf(stderr, "                          :  This ensures that owserver only receives one\n");
    fprintf(stderr, "                          :  request at a time.  Simultanious requests might\n");
    fprintf(stderr, "                          :  cause owserver to crash.\n");
    fprintf(stderr, "  -Q                      : Use local queueing (System V)\n");
    fprintf(stderr, "                          :  As -q, but use System V semaphores rather than\n");
    fprintf(stderr, "                          :  POSIX semaphores\n");
    fprintf(stderr, "  -t                      : Use threads\n");
    fprintf(stderr, "                          :  owfslog always forks off one new process per\n");
    fprintf(stderr, "                          :  source, but by using this option owfslog will use\n");
    fprintf(stderr, "                          :  one thread per sensor rather than one process.\n");
    fprintf(stderr, "  -u <userid>             : Change userid\n");
    fprintf(stderr, "                          :  Only works if run as root.\n");
    fprintf(stderr, "  -v                      : Increase verbosity\n");
    fprintf(stderr, "                          :  For debugging.\n");
    exit(EXIT_FAILURE);
  }

  functions = readconf(argv, conf, &count);

  if (!functions) {
    fprintf(stderr, "%s: Could not read configuration file %s\n", argv[0], conf);
    exit(EXIT_FAILURE);
  }

  if (daemon) {
    umask(0);
    setpgrp();
    if (fork())
      return 0;
  }

  /* Count and label unique sources and files */
  label_unique(functions, count, &uniquesources, &uniquefiles);

  ipcpid = getpid();

  /* Save pidfile */
  if (pidfile) {
    FILE *f = fopen(pidfile, "w");
    if (f) {
      fprintf(f, "%d\n", ipcpid);
      fclose(f);
    }
  }

  /* Change user */
  if (uid)
    setuid(uid);

  /* Test that we can access the log file */
  if (log) {
    outf = fopen(log, "a");
    if (!outf) {
      fprintf(stderr, "%s: Could not open logfile %s\n", argv[0], log);
      exit(EXIT_FAILURE);
    }
    fclose(outf);
  }

  if (align) {
    struct timeval tv;
    unsigned int mod;
    gettimeofday(&tv, NULL);
    thread_sleep(1500 - tv.tv_usec / 1000);
    gettimeofday(&tv, NULL);
    mod = (tv.tv_sec + log_interval / 2) % log_interval;
    if (mod)
      sleep(log_interval - mod);
  }

  /* Allocate System V semaphores */
  if (!posixsem && queueing)
    if ((semid = semget(IPC_PRIVATE, sizeof(semaphores) / sizeof(sem_t), IPC_CREAT | 0600)) == -1) {
      fprintf(stderr, "%s: semget error\n", argv[0]);
      exit(EXIT_FAILURE);
    }

  /* Find memory need */
  for (samples = i = 0; i < uniquefiles; i++) {
    double interval = 999999;
    for (j = 0; j < count; j++) {
      if (functions[j].fileid == i) {
	if (functions[j].interval < 0)
	  functions[j].interval = log_interval + functions[j].interval;
	if (functions[j].interval < interval)
	  interval = functions[j].interval;
      } else if (functions[j].fileid2 == i && functions[j].interval < interval)
	interval = functions[j].interval;
    }
    samples += (int)ceil(log_interval / interval) + 1 + /* headroom */ 5;
  }

  /* Allocate System V shared memory */
  shmid = shmget(IPC_PRIVATE, uniquefiles * sizeof(sensor) +
		 sizeof(val) * samples * VALARR_SIZE+
		 uniquesources * sizeof(queueentry) * QUEUE_SIZE,
		 IPC_CREAT | 0600);
  shm = shmat(shmid, 0, 0);
  sensors = (sensor*)shm;
  sensorvals = (volatile val*)(sensors + uniquefiles);
  queues = (queueentry*)(sensorvals + samples * VALARR_SIZE);
  shmctl(shmid, IPC_RMID, 0);
  if (shmid == -1) {
    fprintf(stderr, "%s: shmget error\n", argv[0]); 
   exit(EXIT_FAILURE);
  }

  /* Make list of sensors, find minimum interval and memory need */
  for (i = 0; i < uniquefiles; i++) {
    sensors[i].interval = 999999;
    for (j = 0; j < count; j++) {
      if (functions[j].fileid == i) {
	sensors[i].file = functions[j].file;
	sensors[i].sourceid = functions[j].sourceid;
	if (functions[j].interval < sensors[i].interval)
	  sensors[i].interval = functions[j].interval;
      } else if (functions[j].fileid2 == i) {
	sensors[i].file = functions[j].file2;
	sensors[i].sourceid = functions[j].sourceid2;
	if (functions[j].interval < sensors[i].interval)
	  sensors[i].interval = functions[j].interval;
      }
    }
  }

  /* Make list of sensors */
  for (i = 0; i < uniquefiles; i++) {
    for (j = 0; j < VALARR_SIZE; j++) {
      sensors[i].vals[j] = i ? sensors[i-1].vals[j] + (int)ceil(log_interval / sensors[i-1].interval) + 1 : sensorvals + samples * j;
      sensors[i].lastval[j] = nan;
      sensors[i].prevval[j] = nan;
      sensors[i].changed[j] = 0;
      sensors[i].changedelta[j] = 0;
      sensors[i].changedelta2[j] = 0;
    }
    sensors[i].shift = 0;
    sensors[i].lastupdate = 0;
    sensors[i].prevupdate = 0;
    sensors[i].message[0] = 0;
  }

  /* Create references in functions to sensors */
  for (i = 0; i < count; i++) {
    functions[i].sensor = sensors + functions[i].fileid;
    functions[i].sensor2 = sensors + functions[i].fileid2;
  }

  /* Create pointers to sensor data */
  for (j = 0; j < VALARR_SIZE; j++)
    for (i = 0; i < count; i++) {
      functions[i].vals[j] = functions[i].fileid < 0 ? NULL :
	functions[i].sensor->vals[j];
      functions[i].vals2[j] = functions[i].fileid2 < 0 ? NULL :
	functions[i].sensor2->vals[j];
    }

  /* Assign messages to sensors */
  for (i = 0; i < count; i++)
    if (!strcmp(functions[i].name, "write"))
      strncpy(functions[i].sensor->message, functions[i].format, sizeof(functions[i].sensor->message));
    else if (!strcmp(functions[i].name, "hexwrite")) {
      int x, y;
      for (x = y = 0; x < sizeof(functions[i].sensor->message) && functions[i].format[y]; x++) {
	int nib1, nib2;
	while (functions[i].format[y+1] &&
	       !(functions[i].format[y] >= '0' && functions[i].format[y] <= '9') &&
	       !(functions[i].format[y] >= 'a' && functions[i].format[y] <= 'f') &&
	       !(functions[i].format[y] >= 'A' && functions[i].format[y] <= 'F'))
	  y++;

	if (!functions[i].format[y+1])
	  break;

	if (functions[i].format[y] >= '0' && functions[i].format[y] <= '9')
	  nib1 = functions[i].format[y] - '0';
	else if (functions[i].format[y] >= 'a' && functions[i].format[y] <= 'f')
	  nib1 = functions[i].format[y] - 'a' + 10;
	else
	  nib1 = functions[i].format[y] - 'A' + 10;

	if (functions[i].format[y+1] >= '0' && functions[i].format[y+1] <= '9')
	  nib2 = functions[i].format[y+1] - '0';
	else if (functions[i].format[y+1] >= 'a' && functions[i].format[y+1] <= 'f')
	  nib2 = functions[i].format[y+1] - 'a' + 10;
	else
	  nib2 = functions[i].format[y+1] - 'A' + 10;

	functions[i].sensor->message[x] = (nib1 << 4) | nib2;
	y += 2;
      }
      functions[i].sensor->message[x - (x == sizeof(functions[i].sensor->message))] = 0;
    }

  /* Make list of sources */
  sources = malloc(sizeof(char*) * uniquesources);
  children = malloc(sizeof(pid_t) * uniquesources);
  if (!sources || !children) {
    fprintf(stderr, "%s: malloc failed\n", argv[0]);
    exit(EXIT_FAILURE);
  }
  for (i = 0; i < uniquesources; i++)
    for (j = 0; j < count; j++) {
      if (functions[j].sourceid == i) {
	sources[i] = functions[j].source;
	break;
      } else if (functions[j].sourceid2 == i) {
	sources[i] = functions[j].source2;
	break;
      }
    }

  if (debug > 1) {
    printf("Using %d source%s:\n", uniquesources, uniquesources == 1 ? "" :"s");
    for (i = 0; i < uniquesources; i++)
      printf("  %s\n", sources[i]);
    printf("\n");
  }

  if (debug > 1) {
    printf("Using %d file%s:\n", uniquefiles, uniquefiles == 1 ? "" :"s");
    for (i = 0; i < uniquefiles; i++)
      printf("  %s|%s\n", sources[sensors[i].sourceid], sensors[i].file);
    printf("\n");
  }

  next = mtime() + log_interval * 1000;
  while (1) {

    queue = queues;
    queueing = queueing_global;

    /* Clear all sensor values */
    for (i = 0; i < samples * VALARR_SIZE; i++) {
      sensorvals[i].val = sensorvals[i].diff = nan;
      sensorvals[i].delta = 0;
      sensorvals[i].changedelta = 0;
      sensorvals[i].changedelta2 = 0;
      sensorvals[i].incdelta = 0;
    }

    /* Fork off one new process for every source */
    for (i = 0; i < uniquesources; i++) {
      child = fork();
      if (child == -1) {
	fprintf(stderr, "%s: fork failed\n", argv[0]);
	sleep(1);
      }
      if (child == 0)
	break;
      children[i] = child;
      queue += QUEUE_SIZE;
    }
    
    if (child == 0) {

      int sourceid = i;
      char *source = sources[i];
      unsigned int pace;
      int dir_size = 1024, len = 0;
      char *directories;

      if (OW_init(source)) {
	fprintf(stderr, "OW_init(%s) failed.\n", source);
	exit(EXIT_FAILURE);
      }
      
      if (max_depth > 0) {

	/* Read directory structure */
	do {
	  dir_size *= 2;
	  directories = malloc(dir_size+2);
	  if (directories) {
	    directories[0] = '/';
	    directories[1] = ',';
	    len = parse_directories(max_depth, directories+2, dir_size, "/", 1);
	    if (len == dir_size)
	      free(directories);
	  }
	} while (len == dir_size);
	
	/* Find sensors in directories */
	search_sensors(sensors, uniquefiles, directories, sourceid);
      }

      for (j = 0; j < QUEUE_SIZE; j++) {
	if (seminit(j*2+0, 1) || seminit(j*2+1, 0)) {
	  fprintf(stderr, "%s: seminit failed, temporarily disabling queueing.\n", argv[0]);
	  perror(0);
	  queueing = 0;
	  break;
	}
	queue[j].locktime = 0;
	queue[j].ack = 1;
      }

      for (j = i = 0; i < uniquefiles; i++)
	j += sensors[i].sourceid == sourceid;

      /* In case owserver doesn't like simultanious accesses distribute the */
      /* start of every thread over a full second or at least 1 ms apart */
      pace = 1000 / (j ? j : 1);
      pace += !pace;

      /* Create a thread for every sensor */
      if (threads) {
	pthread_t *threads;
	
	threads = malloc(j * sizeof(pthread_t));
	if (!threads) {
	  fprintf(stderr, "%s: malloc failed\n", argv[0]);
	  exit(EXIT_FAILURE);
	}
	
	for (j = i = 0; i < uniquefiles; i++)
	  if (sensors[i].sourceid == sourceid) {
	    pthread_create(threads + j++, NULL, log_sensor, (void*)(sensors + i));
	    thread_sleep(pace);
	  }

	now = mtime();
	(queueing ? queue_supervisor : thread_sleep)
	  (next - now > log_interval * 1000 || next < now ?
	   log_interval * 1000 : next - now);
	
	for (i = 0; i < j; i++)
	  pthread_cancel(threads[i]);
	
	OW_finish();
	free(threads);
      }
      /* Or fork off a new process for every sensor */
      else {

	pid_t *children;
	
	children = malloc(j * sizeof(pid_t));
	if (!children) {
	  fprintf(stderr, "%s: malloc failed\n", argv[0]);
	  exit(EXIT_FAILURE);
	}
	
	for (j = i = 0; i < uniquefiles; i++) {
	  if (sensors[i].sourceid == sourceid) {
	    children[j++] = fork();
	    if (children[j - 1] == 0) {
	      log_sensor(sensors + i);
	      exit(0);
	    } else if (children[j - 1] < 0)
	      fprintf(stderr, "%s: fork() failed for %s.\n", argv[0], source);
	    thread_sleep(pace);
	  }
	}
	now = mtime();

	(queueing ? queue_supervisor : thread_sleep)
	  (next - now > log_interval * 1000 || next < now ?
	   log_interval * 1000 : next - now);
	
	for (i = 0; i < j; i++)
	  if (waitpid(children[i], NULL, WNOHANG) == 0)
	      kill(children[i], SIGHUP);
	
	for (i = 0; i < j; i++)
	  waitpid(children[i], NULL, 0);

	free(children);

      }

      if (queueing)
	for (j = 0; j < QUEUE_SIZE; j++) {
	  semdestroy(j*2+0);
	  semdestroy(j*2+1);
	}

      return 0;

    } else if (child > 0) {
      time_t middle;

      next += log_interval * 1000;

      for (i = 0; i < uniquesources; i++)
	waitpid(children[i], NULL, 0);

      middle = time(NULL) - log_interval / 2;
      strftime(timestamp, sizeof(timestamp), dateformat, gmtime(&middle));

      outf = log ? fopen(log, "a") : stdout;

      /* TODO: Dont log if everything is nan */
      if (!outf)
	fprintf(stderr, "%s: warning: could not open logfile %s\n", argv[0], log);
      else {
	fprintf(outf, "%s", timestamp);

	process(outf, functions, count);
	fprintf(outf, "\n");
	if (log)
	  fclose(outf);
      }
    }
  }

  if (semid && ipcpid == getpid())
    semctl(semid, 0, IPC_RMID);
  semid = 0;

  return 0;
}
