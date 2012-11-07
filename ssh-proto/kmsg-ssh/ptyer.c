#include <config.h>

#include <stdlib.h>
#include <time.h>
#include <sys/utsname.h>
#include <argp.h>
#include <error.h>
#include <pty.h>
#include <string.h>
#include <syslog.h>

#include <unistd.h>
#include <sys/types.h>

int msock;
int ssock;
int slave_pty;
char* line;


#define SHELL_PATH "/bin/bash"
#define SHELL_NAME "bash"

#define BUFSIZE 1024*4
char MSG_BUF[BUFSIZE];


void recv_intmsg(int* val) {
  int param_size;
  param_size = read_param(ssock, MSG_BUF, BUFSIZE);
  memcpy(val, MSG_BUF, param_size);
}

void recv_strmsg(char** val) {
  int param_size;
  param_size = read_param(ssock, MSG_BUF, BUFSIZE);
  *val = (char*)malloc(param_size + 1);
  memcpy(*val, MSG_BUF, param_size);
  (*val)[param_size] = 0;
}

int recvstate() { return 0; }

void start_login () {
  execl(SHELL_PATH, SHELL_NAME, NULL);
}

int startslave ()
{
  // DON: Internet(inetd) -> 0,1(slave) -> slave_pty -> 0,1(ptyer) ->
  // bash(under the authenticated user)
  dup2(slave_pty, 0);
  dup2(slave_pty, 1);
  dup2(slave_pty, 2);
  // we have to send back line(char*) and master(fd) here
  //return master;
  start_login ();
}


int main(int argc, char** argv) {
  ssock = atoi(argv[1]);
  slave_pty = atoi(argv[2]);
  syslog (LOG_ERR, "ptyer started:%d:%d, uid:%d\n", ssock, slave_pty, getuid()); fflush(stdout);
  //sleep(15);
  line = argv[3];
  startslave();
  return 0;
}
