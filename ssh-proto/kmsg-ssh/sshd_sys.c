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

#include <shadow.h>
#include <stdlib.h>
#include <stdio.h>
#include <pwd.h>

#include <pwd.h>
#include "key.h"
#include "authfile.h"
#include "kraken_util.h"
#include "sshd_mon.h"


int check_login(char* user, char* passwd) {
  struct passwd *pw;
  char *epasswd;
  char *tty;

#ifdef USE_SHADOW
  struct spwd *spwd;
  struct spwd *getspnam();
#endif

  if ((pw = getpwnam(user)) == NULL) {
    return 1;
  }
    
#ifdef USE_SHADOW
  pw->pw_passwd = NULL;
  spwd = getspnam(user);
  if (spwd) {
    pw->pw_passwd = spwd->sp_pwdp;
  }
#endif
  /*
   * XXX If no passwd, let NOT them login without one.
   */
  if (pw->pw_passwd == '\0') {
    return 1;
  }
#ifdef HAS_SHADOW
  if ((pw->pw_passwd && pw->pw_passwd[0] == '@'
       && pw_auth (pw->pw_passwd+1, pw->pw_name, PW_LOGIN, NULL))
      || !valid (passwd, pw)) {
    return 1;
  }
#else
  epasswd = crypt(passwd, pw->pw_passwd);
  if (strcmp(epasswd, pw->pw_passwd)) {
    return 1;
  }
#endif
  return 0;
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

char* sch_back(const char* str, char c) {
  if(str == NULL) return NULL;

  char* nstr = (str + strlen(str));

  while(nstr >= str) {
    if(nstr == c) return nstr;
    --nstr;
  }
  return NULL;
}


void execute_ptyer(const char* logged_user, int* afd, char* line, int* amaster, int* aslave) {
  int pid = 0;
  int fd[2];

  int master;
  int slave;
  char buf[10][128];
  char filename[1024];
  char* tptr = NULL;
  const char* path = PTYER_SLV_PATH;

  tptr = sch_back(path, '/');
  if(tptr == NULL) strncpy(filename, path, 1024);
  else strncpy(filename, tptr+1, 1024);


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
    execl(PTYER_SLV_PATH, filename, buf[0], buf[1], line, NULL);
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


void logerror(char* str) {
  syslog (LOG_ERR, str);
}

int load_host_keys() {
  char buf[4084];
  char filename[1024];
  int read_char = 0;

  OpenSSL_add_all_algorithms();
  host_key = key_load_private(SSH_HOST_RSA_KEY, "", NULL);

  if(host_key == NULL) syslog (LOG_ERR, "host_key is NULL");
  public_key = key_demote(host_key);

  strcpy(filename, "/tmp/tempXXXXXXX");
  mktemp(filename);

  syslog (LOG_ERR, "sshd_mon_sys is initiated:%s,", filename);

  FILE* f = fopen(filename, "w");
  if(f == NULL) syslog (LOG_ERR, "tmp file open failed");
  
  key_write(filename, f);
  fclose(f);

  f = fopen(TMP_KEY_FILE, "r");
  read_char = fread(buf, 1, 4084, f);
  public_key_serialized = (char*)malloc(read_char * sizeof(char));
  memcpy(public_key_serialized, buf, read_char);
  public_key_serialized_len = read_char;
  
  return 0;
}

void processLoginReq(param* fp) {
  char* buf = NULL;
  char* tmp = NULL;
  pstr obuf;

  if(fp->ptyp != PTYP_STR) { logerror("loginreq:payload type is unmached"); }
  buf = fp->pval.pstr->buf;
  tmp = strchr(buf, '|');
  tmp[0] = 0; ++tmp;
  obuf.buf = buf;
  obuf.len = strlen(buf);
  send_free(mk_SysLoginRes_msg(&obuf, !check_login(buf, tmp)));
}

void processPubKeyReq(param* fp) {
  pstr obuf;

  if(fp != NULL) { logerror("pubkeyreq:payload type is unmached"); }
  obuf.buf = public_key_serialized;
  obuf.len = public_key_serialized_len;
  send_free(mk_SysPubkeyRes_msg(&obuf));
}

void processKeysignReq(param* fp) {
  char* buf = NULL;
  char* sig = NULL;
  int sig_len = 0;
  pstr obuf;

  if(fp->ptyp != PTYP_STR) { logerror("keysignreq:payload type is unmached"); }
  buf = fp->pval.pstr->buf;
  ssh_rsa_sign2(host_key, &sig, &sig_len, buf, fp->pval.pstr->len);

  obuf.buf = sig;
  obuf.len = sig_len;

  send_free(mk_SysKeysignRes_msg(&obuf));
}

void processCreatePtyerReq(param* fp) {
  char* buf = NULL;
  char* tmp = NULL;
  int ptyer_sock = 0;
  int master_pty_fd = 0;
  int slave_pty_fd = 0;
  char line[1024];

  if(fp->ptyp != PTYP_STR) { logerror("pubkeyreq:payload type is unmached"); }
  buf = fp->pval.pstr->buf;

  execute_ptyer(buf, &ptyer_sock, line, &master_pty_fd, &slave_pty_fd);
  sleep(1);

  send_free(mk_SysCreatePtyerRes_msg(slave_pty_fd, master_pty_fd));
}


void run_msg_loop() {
  msg* m = NULL;
  param* fp = NULL;

  //sleep(15);
  while(m = recv_msg()) {
    fp = m->payload;

    syslog (LOG_ERR, "sshd_mon_sys:msg is received :%d", m->mtyp);

    switch(m->mtyp) {

    case MTYP_SysLoginReq:
      processLoginReq(fp); break;

    case MTYP_SysPubkeyReq:
      processPubKeyReq(fp); break;

    case MTYP_SysKeysignReq:
      processKeysignReq(fp); break;

    case MTYP_SysCreatePtyerReq:
      processCreatePtyerReq(fp); break;

    default:
      break;
    }

    free_msg(m);
  }
}

int main (int argc, char **argv) {
  KCHAN = atoi(argv[1]);
  syslog (LOG_ERR, "sshd_mon_sys is initiated:%d", KCHAN);
  load_host_keys();
  run_msg_loop();
}

