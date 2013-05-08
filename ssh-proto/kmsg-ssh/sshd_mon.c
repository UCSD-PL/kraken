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

#include "kraken_util.h"
#include "kauth.h"

#include <pwd.h>
#include "key.h"
#include "authfile.h"
#include "sshd_mon.h"

/*
(*
  # slave <-> monitor 
  LoginReq(str); 0
  LoginResT(); 1
  LoginResF(); 2

  PubkeyReq(); 3
  PubkeyRes(str); 4

  KeysignReq(str); 5
  KeysignRes(str); 6

  CreatePtyerReq(); 7
  CreatePtyerRes(fdesc, fdesc); 8
*)
*/

int slv_socket = -1;
int sys_socket = -1;

void logerror(char* str) {
  syslog (LOG_ERR, str);
}

void send_to_sys_free(msg* m) {
  int old_kchan = KCHAN;
  KCHAN = sys_socket;
  kraken_send_msg(m);
  free_msg(m);
  KCHAN = old_kchan;
}

void send_to_slv_free(msg* m) {
  int old_kchan = KCHAN;
  KCHAN = slv_socket;
  kraken_send_msg(m);
  free_msg(m);
  KCHAN = old_kchan;
}

void processLoginReq(param* fp) {
  if(fp->ptyp != PTYP_STR) { logerror("mon:loginreq:payload type is unmached"); }
  send_to_sys_free(mk_SysLoginReq_msg(fp->pval.pstr));
}

void processPubKeyReq(param* fp) {
  if(fp != NULL) { logerror("mon:pubkeyreq:payload type is unmached"); }
  send_to_sys_free(mk_SysPubkeyReq_msg());
}

void processKeysignReq(param* fp) {
  if(fp->ptyp != PTYP_STR) { logerror("mon:keysignreq:payload type is unmached"); }
  send_to_sys_free(mk_SysKeysignReq_msg(fp->pval.pstr));
}

void processCreatePtyerReq(param* fp, const char* username) {
  pstr obuf;
  if(fp != NULL) { logerror("mon:pubkeyreq:payload type is unmached"); }

  obuf.buf = (char*)username;
  obuf.len = strlen(username);

  send_to_sys_free(mk_SysCreatePtyerReq_msg(&obuf));
}

void processSysLoginResT(param* fp, char* username) {
  if(fp->ptyp != PTYP_STR) {
    logerror("mon:sysloginresT:payload type is unmached"); 
  }
  memcpy(username, fp->pval.pstr->buf, fp->pval.pstr->len);
  username[fp->pval.pstr->len] = 0;
  //result = fp->next->pval.num;
  send_to_slv_free(mk_LoginResT_msg());
}

void processSysLoginResF(param* fp) {
  if(fp != NULL) {
    logerror("mon:sysloginresF:payload type is unmached"); 
  }
  send_to_slv_free(mk_LoginResF_msg());
}

void processSysPubKeyRes(param* fp) {
  if(fp->ptyp != PTYP_STR) { logerror("mon:syspubkeyres:payload type is unmached"); }
  send_to_slv_free(mk_PubkeyRes_msg(fp->pval.pstr));
}

void processSysKeysignRes(param* fp) {
  if(fp->ptyp != PTYP_STR) { logerror("mon:syskeysignres:payload type is unmached"); }
  send_to_slv_free(mk_KeysignRes_msg(fp->pval.pstr));
}

void processSysCreatePtyerRes(param* fp) {
  if(fp->ptyp != PTYP_FD || fp->next == NULL || fp->next->ptyp != PTYP_FD) {
    logerror("mon:syscreateptyerres:payload type is unmached"); 
  }
  send_to_slv_free(mk_CreatePtyerRes_msg(fp->pval.fd, fp->next->pval.fd));
}

void run_msg_loop() {
  msg* m = NULL;
  param* fp = NULL;

  char username[1024];
  fd_set read_fds;
  //struct timeval tv;
  int retval;
  int login_succeeded = 0;
  
  msg* ms = NULL;

  FD_ZERO(&read_fds);
  FD_SET(sys_socket, &read_fds);
  FD_SET(slv_socket, &read_fds);

  syslog (LOG_ERR, "sshd_mon:msg loop is entered:%d, %d", slv_socket, sys_socket);
  //sleep(15);
  while((retval = select((sys_socket < slv_socket) ? slv_socket + 1 : sys_socket + 1, &read_fds, NULL, NULL, NULL)) > 0) {
    if(FD_ISSET(slv_socket, &read_fds)) {
      KCHAN = slv_socket;
    } else {
      KCHAN = sys_socket;
    }
    syslog (LOG_ERR, "sshd_mon:a new msg is ready:from_slave:%d", slv_socket == KCHAN);

    FD_ZERO(&read_fds);
    FD_SET(slv_socket, &read_fds);
    FD_SET(sys_socket, &read_fds);

    m = recv_msg();
    fp = m->payload;
    syslog (LOG_ERR, "sshd_mon:a new msg is received:%d", m->mtyp);
    switch(m->mtyp) {
      // from slave
    case MTYP_LoginReq:
      processLoginReq(fp); break;
      
    case MTYP_PubkeyReq:
      processPubKeyReq(fp); break;
      
    case MTYP_KeysignReq:
      processKeysignReq(fp); break;

    case MTYP_CreatePtyerReq:
      syslog(LOG_ERR, "login status : %d", login_succeeded);
      if(login_succeeded) {
        syslog(LOG_ERR, "ptyer is created for (%s)", username);
        processCreatePtyerReq(fp, username); 
      }
      break;
	
      // from sys
    case MTYP_SysLoginResT:
      login_succeeded = 1;
      processSysLoginResT(fp, username);
      break;

      // from sys
    case MTYP_SysLoginResF:
      login_succeeded = 0;
      processSysLoginResF(fp);
      break;
      
    case MTYP_SysPubkeyRes:
      processSysPubKeyRes(fp); break;
      
    case MTYP_SysKeysignRes:
      processSysKeysignRes(fp); break;

    case MTYP_SysCreatePtyerRes:
      processSysCreatePtyerRes(fp); break;
      
    default:
      break;
    }
    free_msg(m);
  }
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


int exec_component(const char* path, int uid) {
  int fd[2];
  static const int PSOCKET = 0;
  static const int CSOCKET = 1;
  char buf[1024];
  char filename[1024];
  char* tptr = NULL;
  int pid = 0 ;

  tptr = sch_back(path, '/');
  if(tptr == NULL) strncpy(filename, path, 1024);
  else strncpy(filename, tptr+1, 1024);

  socketpair(PF_UNIX, SOCK_STREAM, 0, fd);

  pid = fork();
  
  if (pid < 0) {
    syslog (LOG_ERR, "Out of pid");
    exit(1);
  }

  if (pid == 0) {
    close(fd[PSOCKET]);
    sprintf(buf, "%d", fd[CSOCKET]);
    setuid(uid);
    execl(path, filename, buf, NULL);
  } else {
    close(fd[CSOCKET]);
    return fd[PSOCKET];
  }
}


int main(int argc, char **argv) {
  sys_socket = exec_component(SSH_SYS_PATH, 0);
  slv_socket = exec_component(SSH_SLV_PATH, SLAVE_UID);
  run_msg_loop();
  return 0;
}

