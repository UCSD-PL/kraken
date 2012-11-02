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
  LoginReq(str);
  LoginRes(num);

  PubkeyReq();
  PubkeyRes(str);

  KeysignReq(str);
  KeysignRes(str);

  CreatePtyerReq();
  CreatePtyerRes(fdesc, fdesc);
*)
*/

void send_to_sys_free(msg* m) {
  int old_kchan = KCHAN;
  KCHAN = sys_socket;
  send_msg(m);
  free_msg(m);
  KCHAN = old_kchan;
}

void send_to_slv_free(msg* m) {
  int old_kchan = KCHAN;
  KCHAN = slv_socket;
  send_msg(m);
  free_msg(m);
  KCHAN = old_kchan;
}

void processLoginReq(param* fp) {
  if(fp->ptyp != PTYP_STR) { logerror("mon:loginreq:payload type is unmached"); }
  send_to_sys_free(mk_SysLoginReq_msg(fp->pval.pstr));
}

void processPubKeyReq(param* fp) {
  if(fp != NULL) { logerror("mon:pubkeyreq:payload type is unmached"); }
  send_to_sys_free(mk_SysPubKeyReq_msg(fp->pval.pstr));
}

void processKeysignReq(param* fp) {
  if(fp->ptyp != PTYP_STR) { logerror("mon:keysignreq:payload type is unmached"); }
  send_to_sys_free(mk_SysKeysignReq_msg(fp->pval.pstr));
}

void processCreatePtyerReq(param* fp, const char* username) {
  pstr obuf;
  if(fp != NULL) { logerror("mon:pubkeyreq:payload type is unmached"); }

  obuf.buf = username;
  obuf.len = strlen(username);

  send_to_sys_free(mk_SysCreatePtyerReq_msg(&obuf));
}

int processSysLoginRes(param* fp, char* username) {
  int result = 0;

  if(fp->ptyp != PTYP_STR || fp->next == NULL || fp->next->ptyp != PTYP_NUM) {
    logerror("mon:sysloginres:payload type is unmached"); 
  }
  memcpy(username, fp->pval.pstr->buf, fp->pval.pstr->len);
  username[fp->pval.pstr->len] = 0;
  result = fp->next->pval.num;
  send_to_slv_free(mk_LoginRes_msg(resul));

  return result;
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
  char* buf = NULL;
  char* tmp = NULL;
  int ptyer_sock = 0;
  int master_pty_fd = 0;
  int slave_pty_fd = 0;
  char line[1024];

  if(fp->ptyp != PTYP_FD || fp->next == NULL || fp->next->ptyp != PTYP_FD) {
    logerror("mon:syscreateptyerres:payload type is unmached"); 
  }
  send_to_slv_free(mk_CreatePtyerRes_msg(fp->pval.fd, fp->next->pval.fd));
}


void run_msg_loop(int slv_socket, int sys_socket) {
  msg* m = NULL;
  param* fp = NULL;

  fd_set read_fd;
  struct timeval tv;
  int retval;

  FD_ZERO(&read_fd);
  FD_SET(slv_socket, &read_fd);
  FD_SET(sys_socket, &read_fd);
  
  while(retval = select(2, &read_fd, NULL, NULL, NULL) != -1) {
    if(FD_ISSET(slv_socket, read_fd)) {
      KCHAN = slv_socket;
    } else {
      KCHAN = sys_socket;
    }
    FD_ZERO(&read_fd);
    FD_SET(slv_socket, &read_fd);
    FD_SET(sys_socket, &read_fd);

    while(m = recv_msg()) {
      fp = m->payload;
      switch(m->mtyp) {
      // from slave
      case MTYP_LoginReq:
        processLoginReq(fp); break;

      case MTYP_PubkeyReq:
        processPubKeyReq(fp); break;
        
      case MTYP_KeysignReq:
        processKeysignReq(fp); break;

      case MTYP_CreatePtyerReq:
        processCreatePtyerReq(fp); break;

      // from sys
      case MTYP_SysLoginRes:
        login_succeeded = processSysLoginRes(fp, username);
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

  tptr = sch_back(path, '/');
  if(tptr == NULL) filename = path;
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
    execl(path, file, buf, NULL);
  } else {
    close(fd[CSOCKET]);
    return fd[PSOCKET];
  }
}

int main (int argc, char **argv) {
  int slave_fd = 0;
  int sys_fd = 0;

  slv_socket = exec_component(SSH_SLV_PATH);
  sys_socket = exec_component(SSH_SYS_PATH);

  socketpair(PF_UNIX, SOCK_STREAM, 0, fd);

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

