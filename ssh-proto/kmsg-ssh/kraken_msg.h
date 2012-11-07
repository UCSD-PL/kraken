#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <assert.h>

#define TRUE     1
#define FALSE    0
//#define NUM_SIZE 1
#define NUM_SIZE 2

// cmsg size for 1 file descriptor
#define FD_CMSG_SPACE CMSG_SPACE(sizeof(int))

// global socket for all kernel communication
int KCHAN;

// Programs using this lib should be forked from a Kraken kernel which will
// set up a socket for communication and pass it to the child as a command
// line argument in the exec. msg_init(arg) takes that argument, makes it a
// socket, and stores it in KCHAN.
void msg_init(char *arg);

typedef enum param_t {
  PTYP_NUM,
  PTYP_STR,
  PTYP_FD,
} param_t;

typedef struct pstr {
  uint32_t len;
  char *buf;
} pstr;

typedef union param_v {
  uint32_t num;
  pstr *pstr;
  int fd;
} param_v;

typedef struct param {
  param_t ptyp;
  param_v pval;
  struct param *next;
} param;

typedef enum msg_t {
  MTYP_LoginReq = 1,
  MTYP_LoginRes = 2,
  MTYP_PubkeyReq = 3,
  MTYP_PubkeyRes = 4,
  MTYP_KeysignReq = 5,
  MTYP_KeysignRes = 6,
  MTYP_CreatePtyerReq = 7,
  MTYP_CreatePtyerRes = 8,
  MTYP_SysLoginReq = 9,
  MTYP_SysLoginRes = 10,
  MTYP_SysPubkeyReq = 11,
  MTYP_SysPubkeyRes = 12,
  MTYP_SysKeysignReq = 13,
  MTYP_SysKeysignRes = 14,
  MTYP_SysCreatePtyerReq = 15,
  MTYP_SysCreatePtyerRes = 16,
} msg_t;

typedef struct msg {
  msg_t mtyp;
  param *payload;
} msg;

pstr * pstr_of_string(char *s);

pstr * mk_pstr(int len, char *buf);

pstr * pstrdup(pstr *s);

// allocate various kinds of msgs

msg * mk_LoginReq_msg(pstr * p0);
msg * mk_LoginRes_msg(uint32_t p0);
msg * mk_PubkeyReq_msg();
msg * mk_PubkeyRes_msg(pstr * p0);
msg * mk_KeysignReq_msg(pstr * p0);
msg * mk_KeysignRes_msg(pstr * p0);
msg * mk_CreatePtyerReq_msg();
msg * mk_CreatePtyerRes_msg(int p0, int p1);
msg * mk_SysLoginReq_msg(pstr * p0);
msg * mk_SysLoginRes_msg(pstr * p0, uint32_t p1);
msg * mk_SysPubkeyReq_msg();
msg * mk_SysPubkeyRes_msg(pstr * p0);
msg * mk_SysKeysignReq_msg(pstr * p0);
msg * mk_SysKeysignRes_msg(pstr * p0);
msg * mk_SysCreatePtyerReq_msg(pstr * p0);
msg * mk_SysCreatePtyerRes_msg(int p0, int p1);

// free all resources tied to this message
void free_msg(msg *m);

// get the ith param of a msg
param * get_param(msg *m, int i);

// return a nice string representation of msg m
// caller is responsible for freeing the returned string
char * string_of_msg(msg *m);

msg * recv_msg(void);

void kraken_send_msg(msg *m);
