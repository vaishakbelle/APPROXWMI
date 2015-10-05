/*  doalarm - run a command under an alarm clock
 *  --------------------------------------------
 *  Copyright 2001, M.J. Pomraning <mjp@pilcrow.madison.wi.us>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 *  ChangeLog:
 *    14 Dec 2001   License file fix, tgz cleanup, 0.1.7
 *    11 Dec 2001   man page, GPL, public release, 0.1.6
 *    29 Nov 2001   rlimit timer; 0.1.5
 */

#include <unistd.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <getopt.h>
#include <stdio.h>
#include <errno.h>

#define STR_EQ(x,y)   !strcmp((x),(y))

#define VERSION_STR   "doalarm 0.1.7 (14 Dec 2001)\n"

#define USAGE_STR  \
"Usage: doalarm [-hr] [-t type] sec command [arg...]\n" \
"Run command under an alarm clock.\n" \
"\n" \
"Options:\n" \
" -t <type>         Type of timer: 'real' (SIGALRM), 'virtual' (SIGVTALRM),\n" \
"    --timer=<type> 'profile' (SIGPROF), 'cpu' (SIGXCPU).  Default 'real'.\n" \
" -r --recur        Recurring alarm, every sec seconds.\n" \
" -h --help         Show help text (this message).\n"  \
"    --version      Display version.\n" \
"\n" \
VERSION_STR


/** Globals **/

static int xcpu = 0;    /* 0 == interval timer, 1 == RLIMIT_CPU */
static int timer_type = ITIMER_REAL;
static int recur = 0;

static struct option longopts[] = {
  {"recur",   0, 0, 'r'},
  {"timer",   1, 0, 't'},
  {"help",    0, 0, 'h'},
  {"version", 0, 0, 'V'},   /* V not in optstring */
  {0, 0, 0, 0}
};

static void
usage(const char * msg) {
  if (msg) {
    fprintf(stderr, msg);
  }
  fprintf(msg ? stderr : stdout, USAGE_STR);
  exit(msg ? 1 : 0);
}

static int
parse_options(int ac, char **av) {
  extern char *optarg;
  extern int optind;
  int c;

  while ((c=getopt_long(ac, av, "+hrt:", longopts, NULL)) != -1) {
    switch (c) {
      case 'r':
        recur = 1;
        break;
      case 't':
        if (STR_EQ(optarg,"virtual"))
          timer_type = ITIMER_VIRTUAL;
        else if (STR_EQ(optarg,"cpu")) {
          xcpu = 1;
        }
        else if (STR_EQ(optarg,"profile"))
          timer_type = ITIMER_PROF;
        else if (STR_EQ(optarg,"real"))
          timer_type = ITIMER_REAL;
        else
          usage("Unknown timer type\n");
        break;
      case 'h':
        usage(NULL);
        break; /* not reached */
      case 'V':
        printf(VERSION_STR);
        exit(0);
        break;
      default:
        break;
    }
  }

  if (xcpu && recur)
    usage("cpu timer may not recur\n");

  if (! av[optind] || !av[optind+1])
    usage("Error: missing required parameter\n");

  return optind;

}

static int
rlim_cpu(int s) {
  struct rlimit rl;

  if (getrlimit(RLIMIT_CPU, &rl) == -1)
    return -1;

  rl.rlim_cur = s ? s : rl.rlim_max;

  return setrlimit(RLIMIT_CPU, &rl);

}

static int
set_timer(int s, int which, int recurring) {
  struct itimerval itv;

  itv.it_interval.tv_usec =
  itv.it_value.tv_usec = 0;

  itv.it_value.tv_sec = s;
  itv.it_interval.tv_sec = recurring ? s : 0;

  return setitimer(which, &itv, NULL);
}

int
main(int argc, char **argv) {
  extern int errno;
  int i, seconds;
  char * endptr;
  char **newargv;

  i = parse_options(argc, argv);

  errno = 0;
  seconds = (unsigned int) strtoul(argv[i], &endptr, 10);
  if (errno || &endptr[0] == argv[i])
    usage("Invalid seconds parameter\n");

  /* grab command [args ...] */
  newargv = argv + (i + 1);

  /* schedule alarm */
  if (xcpu) {
    if (rlim_cpu(seconds) == -1) {
      perror("rlimit cpu");
      exit(1);
    }
  } else {
    if (set_timer(seconds, timer_type, recur) == -1) {
      perror("setitimer");
      exit(1);
    }
  }

  execvp(newargv[0], newargv);

  perror("exec");
  exit(1);
}
