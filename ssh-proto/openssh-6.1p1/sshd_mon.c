#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <signal.h>
#include <error.h>
#include <syslog.h>
#include <fcntl.h>
#include <pty.h>
#include <sys/types.h>
#include <signal.h>
#include <openssl/dh.h>
#include <openssl/bn.h>
#include <openssl/md5.h>
#include <openssl/rand.h>
#include "openbsd-compat/openssl-compat.h"

#include "interproc.h"
#include "kauth.h"

#include <pwd.h>
#include "key.h"
#include "authfile.h"

int mon_socket;
int slv_socket;


int print_file_info(int fd) {
  struct flock fl;
  fcntl(fd, F_GETLK, &fl);
  
  printf("type:%d\n",(int)(fl.l_type));
  printf("whence:%d\n",(int)(fl.l_whence));
  printf("start:%d\n", (int)(fl.l_start));
  printf("len:%d\n", (int)(fl.l_len));
  printf("pid:%d\n", (int)(fl.l_pid));
  printf("------------------------\n");
}


uid_t name_to_uid(char const *name)
{
  if (!name)
    return -1;
  long const buflen = sysconf(_SC_GETPW_R_SIZE_MAX);
  if (buflen == -1)
    return -1;
  // requires c99
  char buf[buflen];
  struct passwd pwbuf, *pwbufp;
  if (0 != getpwnam_r(name, &pwbuf, buf, buflen, &pwbufp)
      || !pwbufp)
    return -1;
  return pwbufp->pw_uid;
}


void execute_ptyer(const char* logged_user, int* afd, char* line, int* amaster, int* aslave) {
  int pid = 0;
  int fd[2];

  int master;
  int slave;
  char buf[10][128];

  socketpair(PF_UNIX, SOCK_STREAM, 0, fd);
  if (openpty(&master, &slave, line, NULL, NULL) < 0)  {
    syslog (LOG_ERR, "Out of ptys");
    exit (EXIT_FAILURE);
  }

  // D:this is needed for sshpty.c:208
  // this operation can be called only by the owner.
  // so this must be called by the monitor.

  if (ioctl(slave, TIOCSCTTY, NULL) < 0) {
    syslog (LOG_ERR, "ioctl failed over the slave tty");
  }

  pid = fork();

  if (pid < 0) {
    syslog (LOG_ERR, "Out of pid");
    exit(1);
  }

  if (pid == 0) {
    // close all file descriptors
    close(fd[0]);
    //printf("ptyer-1\n"); fflush(stdout);
    sprintf(buf[0], "%d", fd[1]);
    sprintf(buf[1], "%d", slave); 
    setuid(name_to_uid(logged_user));
    execl(PTYER_SLV_PATH, PTYER_SLV_FILE, buf[0], buf[1], line, NULL);
    syslog (LOG_ERR, "the monitor failed to execute ptyer");
    exit(1);
  } else {
    close(fd[1]);
    *afd = fd[0];
    // line
    *amaster = master;
    *aslave = slave;
  }  
}


Key* host_key;
Key* public_key;
char* public_key_serialized;
int public_key_serialized_len;

int sshd_monitor_run (pid_t slv_pid) {
  char msg_buf[4096];
  char* tmp;
  int login_failcnt = 0;

  char logged_user[128];
  int login_succeeded = 0;
  int regenerated;

  int ptyer_sock;
  char line[1024];
  int master_pty_fd;
  int slave_pty_fd;
  int read_char = 0;

  char* sig;
  int sig_len;

  logged_user[0] = 0;

  while(1) {
    read_char = read_msg_id(mon_socket);
    if(read_char < 0) {
      syslog (LOG_ERR, "sshd_mon has a broken socket :%d", mon_socket);
      break;
    }
    
    syslog (LOG_ERR, "read_char:%d", read_char);

    switch (read_char) {
    case LOGIN_REQ:
      if(login_failcnt > 2) {
	syslog (LOG_ERR, "slave(%d) issued LOGIN_REQ more than 3 times -- killed", slv_pid);
	kill(slv_pid, SIGKILL);
	continue;
      }
      ++login_failcnt;
      read_param(mon_socket, msg_buf, 4096);
      tmp = strchr(msg_buf, '|');
      tmp[0] = 0; ++tmp;
      strncpy(logged_user, msg_buf, strlen(msg_buf) + 1);
      login_succeeded = !check_login(msg_buf, tmp);
      syslog (LOG_ERR, "LOGIN_REQ is received:msg_buf:%s, result:%d", msg_buf, login_succeeded);
      msg_buf[0] = login_succeeded;
      msg_buf[1] = 0;
      write_msg(mon_socket, LOGIN_RES, msg_buf, 1);
      break;

    case REGENERATE_REQ:
      if (login_succeeded != 1) break;      
      read_param(mon_socket, msg_buf, 4096);
      execute_ptyer(logged_user, &ptyer_sock, line, &master_pty_fd, &slave_pty_fd);
      // have to send ptyer_sock(fd) and master_pty_fd(fd) to slave.
      // sleep(2) is to prevent a race condition from happening.
      sleep(2);
      _sendfd(mon_socket, ptyer_sock);
      close(ptyer_sock);
      _sendfd(mon_socket, master_pty_fd);
      _sendfd(mon_socket, slave_pty_fd);
      break;

    case PUB_KEY_REQ:
      read_param(mon_socket, msg_buf, 4096);
      write_msg(mon_socket, PUB_KEY_RES, public_key_serialized, public_key_serialized_len);
      break;

    case KEY_SIGN_REQ:
      read_char = read_param(mon_socket, msg_buf, 4096);      
      ssh_rsa_sign2(host_key, &sig, &sig_len, msg_buf, read_char);
      write_msg(mon_socket, KEY_SIGN_RES, sig, sig_len);
      break;

    default :
      syslog (LOG_ERR, "something strange is read:%d", read_char);
    }
  }
}


int load_host_keys() {
  char buf[4084];
  int read_char = 0;

  OpenSSL_add_all_algorithms();
  host_key = key_load_private(SSH_HOST_RSA_KEY, "", NULL);

  if(host_key == NULL) syslog (LOG_ERR, "host_key is NULL");
  public_key = key_demote(host_key);

  FILE* f = fopen(TMP_KEY_FILE, "w");
  if(f == NULL) syslog (LOG_ERR, "tmp file open failed");
  
  key_write(public_key, f);
  fclose(f);

  f = fopen(TMP_KEY_FILE, "r");
  read_char = fread(buf, 1, 4084, f);
  public_key_serialized = (char*)malloc(read_char * sizeof(char));
  memcpy(public_key_serialized, buf, read_char);
  public_key_serialized_len = read_char;
  
  return 0;
}


int main (int argc, char **argv) {
  int index;

  pid_t pid; 
  int fd[2];
  static const int PSOCKET = 0;
  static const int CSOCKET = 1;
  char buf[1024];
  char nargvs[6][256];
  char* tmp_ptr;
  char** nargv;

  socketpair(PF_UNIX, SOCK_STREAM, 0, fd);

  char val = 0;

  load_host_keys();

  pid = fork();
  
  if (pid < 0) {
    syslog (LOG_ERR, "Out of pid");
    exit(1);
  }

  if (pid == 0) {
    close(fd[PSOCKET]);    
    sprintf(buf, "%d", fd[CSOCKET]);
    setuid(SLAVE_UID);
    execl(SSH_SLV_PATH, SSH_SLV_FILE, buf, NULL);
  } else {
    close(fd[CSOCKET]);
    mon_socket = fd[PSOCKET];
    slv_socket = -1;
    return sshd_monitor_run(pid);
  }
}

