#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <assert.h>

#include "kraken_msg.h"

void
msg_init(char *arg) {
  KCHAN = atoi(arg);
}

pstr *
alloc_pstr() {
  pstr *s;

  s = (pstr *)malloc(sizeof(pstr));
  assert(s != NULL);
  return s;
}

pstr *
pstr_of_string(char *s) {
  pstr *p;

  p = alloc_pstr();
  p->len = strlen(s);
  p->buf = strdup(s);
  return p;
}

pstr *
mk_pstr(int len, char *buf) {
  pstr *p;

  p = alloc_pstr();
  p->len = len;
  p->buf = (char *)malloc(p->len);
  assert(p->buf != NULL);
  memcpy(p->buf, buf, p->len);
  return p;
}

pstr *
pstrdup(pstr *s) {
  return mk_pstr(s->len, s->buf);
}

param *
alloc_param() {
  param *p;

  p = (param *)malloc(sizeof(param));
  assert(p != NULL);
  return p;
}

param *
mk_param(param_t t, param *next) {
  param *p;

  p = alloc_param();
  p->ptyp = t;
  p->next = next;
  return p;
}

param *
mk_num_param(uint32_t n, param *next) {
  param *p;

  p = alloc_param();
  p->ptyp = PTYP_NUM;
  p->pval.num = n;
  p->next = next;
  return p;
}

param *
mk_pstr_param(pstr *s, param *next) {
  param *p;

  p = alloc_param();
  p->ptyp = PTYP_STR;
  p->pval.pstr = pstrdup(s);
  p->next = next;
  return p;
}

param *
mk_fd_param(int fd, param *next) {
  param *p;

  p = alloc_param();
  p->ptyp = PTYP_FD;
  p->pval.fd = fd;
  p->next = next;
  return p;
}

msg *
mk_msg(int mtyp, param *pay) {
  msg *m;

  m = (msg *)malloc(sizeof(msg));
  assert(m != NULL);
  m->mtyp = mtyp;
  m->payload = pay;
  return m;
}

msg *
mk_LoginReq_msg(pstr * p0) {
  return mk_msg(MTYP_LoginReq, mk_pstr_param(p0, NULL));
}
msg *
mk_LoginRes_msg(uint32_t p0) {
  return mk_msg(MTYP_LoginRes, mk_num_param(p0, NULL));
}
msg *
mk_PubkeyReq_msg() {
  return mk_msg(MTYP_PubkeyReq, NULL);
}
msg *
mk_PubkeyRes_msg(pstr * p0) {
  return mk_msg(MTYP_PubkeyRes, mk_pstr_param(p0, NULL));
}
msg *
mk_KeysignReq_msg(pstr * p0) {
  return mk_msg(MTYP_KeysignReq, mk_pstr_param(p0, NULL));
}
msg *
mk_KeysignRes_msg(pstr * p0) {
  return mk_msg(MTYP_KeysignRes, mk_pstr_param(p0, NULL));
}
msg *
mk_CreatePtyerReq_msg() {
  return mk_msg(MTYP_CreatePtyerReq, NULL);
}
msg *
mk_CreatePtyerRes_msg(int p0, int p1) {
  return mk_msg(MTYP_CreatePtyerRes, mk_fd_param(p0, mk_fd_param(p1, NULL)));
}
msg *
mk_SysLoginReq_msg(pstr * p0) {
  return mk_msg(MTYP_SysLoginReq, mk_pstr_param(p0, NULL));
}
msg *
mk_SysLoginRes_msg(pstr * p0, uint32_t p1) {
  return mk_msg(MTYP_SysLoginRes, mk_pstr_param(p0, mk_num_param(p1, NULL)));
}
msg *
mk_SysPubkeyReq_msg() {
  return mk_msg(MTYP_SysPubkeyReq, NULL);
}
msg *
mk_SysPubkeyRes_msg(pstr * p0) {
  return mk_msg(MTYP_SysPubkeyRes, mk_pstr_param(p0, NULL));
}
msg *
mk_SysKeysignReq_msg(pstr * p0) {
  return mk_msg(MTYP_SysKeysignReq, mk_pstr_param(p0, NULL));
}
msg *
mk_SysKeysignRes_msg(pstr * p0) {
  return mk_msg(MTYP_SysKeysignRes, mk_pstr_param(p0, NULL));
}
msg *
mk_SysCreatePtyerReq_msg(pstr * p0) {
  return mk_msg(MTYP_SysCreatePtyerReq, mk_pstr_param(p0, NULL));
}
msg *
mk_SysCreatePtyerRes_msg(int p0, int p1) {
  return mk_msg(MTYP_SysCreatePtyerRes, mk_fd_param(p0, mk_fd_param(p1, NULL)));
}

void
free_pstr(pstr *s) {
  free(s->buf);
  s->buf = NULL;
  free(s);
}

void
free_param(param *p) {
  if(p == NULL) {
    return;
  }
  free_param(p->next);
  p->next = NULL;
  switch(p->ptyp) {
    case PTYP_NUM:
      break;
    case PTYP_STR:
      free_pstr(p->pval.pstr);
      break;
    case PTYP_FD:
      break;
    default:
      assert(FALSE);
      break;
  }
  free(p);
}

void
free_msg(msg *m) {
  free_param(m->payload);
  m->payload = NULL;
  free(m);
}

param *
get_param(msg *m, int i) {
  param *it;

  it = m->payload;
  while(i > 0) {
    assert(it != NULL);
    it = it->next;
    i--;
  }
  return it;
}

char *
zsprintf(const char *fmt, ...) {
  va_list args;
  char *s;
  int n;

  va_start(args, fmt);
  n = vasprintf(&s, fmt, args);
  va_end(args);
  assert(n >= 0);
  return s;
}

char *
string_of_mtyp(int mtyp) {
  switch(mtyp) {
    case MTYP_LoginReq:
      return strdup("LoginReq");
    case MTYP_LoginRes:
      return strdup("LoginRes");
    case MTYP_PubkeyReq:
      return strdup("PubkeyReq");
    case MTYP_PubkeyRes:
      return strdup("PubkeyRes");
    case MTYP_KeysignReq:
      return strdup("KeysignReq");
    case MTYP_KeysignRes:
      return strdup("KeysignRes");
    case MTYP_CreatePtyerReq:
      return strdup("CreatePtyerReq");
    case MTYP_CreatePtyerRes:
      return strdup("CreatePtyerRes");
    case MTYP_SysLoginReq:
      return strdup("SysLoginReq");
    case MTYP_SysLoginRes:
      return strdup("SysLoginRes");
    case MTYP_SysPubkeyReq:
      return strdup("SysPubkeyReq");
    case MTYP_SysPubkeyRes:
      return strdup("SysPubkeyRes");
    case MTYP_SysKeysignReq:
      return strdup("SysKeysignReq");
    case MTYP_SysKeysignRes:
      return strdup("SysKeysignRes");
    case MTYP_SysCreatePtyerReq:
      return strdup("SysCreatePtyerReq");
    case MTYP_SysCreatePtyerRes:
      return strdup("SysCreatePtyerRes");
    default:
      assert(FALSE);
      break;
  }
}

char *
string_of_pstr(pstr *s) {
  char *res, *it;
  int i;

  res = (char *)malloc(s->len * 4 + 2);
  assert(res != NULL);
  it = res;
  *it = '"'; it++;
  for(i = 0; i < s->len; i++) {
    if (! isprint(s->buf[i])) {
      sprintf(it, "\\x%02x", s->buf[i]);
      it += 4;
    } else if (s->buf[i] == '"') {
      *it = '\\'; it++;
      *it = '"';  it++;
    } else if (s->buf[i] == '\\') {
      *it = '\\'; it++;
      *it = '\\'; it++;
    } else {
      *it = s->buf[i]; it++;
    }
  }
  *it = '"'; it++;
  *it = '\0';
  return res;
}

char *
string_of_params(param *p) {
  char *s, *h, *t;
  int n;

  if(p == NULL) {
    return strdup("");
  }
  switch(p->ptyp) {
    case PTYP_NUM:
      h = zsprintf("%d", p->pval.num);
      break;
    case PTYP_STR:
      h = string_of_pstr(p->pval.pstr);
      break;
    case PTYP_FD:
      h = zsprintf("fd(%d)", p->pval.fd);
      break;
    default:
      assert(FALSE);
      break;
  }
  if(p->next == NULL) {
    s = h;
  } else {
    t = string_of_params(p->next);
    s = zsprintf("%s, %s", h, t);
    free(t);
    free(h);
  }
  return s;
}

char *
string_of_msg(msg *m) {
  char *s, *ms, *ps;
  int n;

  ms = string_of_mtyp(m->mtyp);
  ps = string_of_params(m->payload);
  s = zsprintf("%s(%s)", ms, ps);
  free(ps);
  free(ms);
  return s;
}

// recv/send raw values

uint32_t
recv_num(void) {
  uint32_t x;
  char *buf;
  int n;

  x = 0; // only some bytes of x get set, make rest 0
  //buf = ((char *)&x) + sizeof(x) - NUM_SIZE;
  buf =  ((char *)&x);
  //n = recv(KCHAN, buf, NUM_SIZE, 0);
  n = recv(KCHAN, buf, sizeof(x), 0);
  //assert(n == NUM_SIZE);
  // convert to host endian
  x = ntohl(x);
  return x;
}

void
send_num(uint32_t x) {
  char *buf;
  int n;

  // for now, num is only 1 byte, check bounds
  //assert(0 <= x && x <= 255);

  // convert to big endian
  x = htonl(x);
  //buf = ((char *)&x) + sizeof(x) - NUM_SIZE;
  buf =  ((char *)&x);
  //n = send(KCHAN, buf, NUM_SIZE, 0);
  n = send(KCHAN, buf, sizeof(x), 0);
  //assert(n == NUM_SIZE);
}

pstr *
recv_pstr(void) {
  pstr *s;
  int n;

  s = alloc_pstr();
  s->len = recv_num();
  s->buf = (char *)malloc(s->len);
  assert(s->buf != NULL);
  n = recv(KCHAN, s->buf, s->len, 0);
  assert(n == s->len);
  return s;
}

void
send_pstr(pstr *s) {
  int n;

  send_num(s->len);
  n = send(KCHAN, s->buf, s->len, 0);
  assert(n == s->len);
}

int
recv_fd(void) {
  struct msghdr hdr;
  struct iovec data;
  char buf[FD_CMSG_SPACE];
  struct cmsghdr *h;
  int n, fd;

  /* init everything to 0 */
  memset(&hdr, 0, sizeof(struct msghdr));
  memset(&data, 0, sizeof(struct iovec));
  memset(buf, 0, FD_CMSG_SPACE);

  /* must recv some msg, single byte will do */
  char dummy    = '\0';
  data.iov_base = &dummy;
  data.iov_len  = sizeof(dummy);

  /* set header values */
  hdr.msg_name       = NULL;
  hdr.msg_namelen    = 0;
  hdr.msg_iov        = &data;
  hdr.msg_iovlen     = 1;
  hdr.msg_control    = buf;
  hdr.msg_controllen = FD_CMSG_SPACE;
  hdr.msg_flags      = 0;

  /* recv file descriptor */
  n = recvmsg(KCHAN, &hdr, 0);

  /* check for errors */
  assert(n == 1);
  h = CMSG_FIRSTHDR(&hdr);
  assert( h != NULL
       && h->cmsg_len    == CMSG_LEN(sizeof(int))
       && h->cmsg_level  == SOL_SOCKET
       && h->cmsg_type   == SCM_RIGHTS
       );

  /* unpack file descriptor */
  fd = ((int *)CMSG_DATA(h))[0];

  assert(fd > 0);
  return fd;
}

void
send_fd(int fd) {
  struct msghdr hdr;
  struct iovec data;
  char buf[FD_CMSG_SPACE];
  struct cmsghdr *h;

  /* init everything to 0 */
  memset(&hdr, 0, sizeof(struct msghdr));
  memset(&data, 0, sizeof(struct iovec));
  memset(buf, 0, FD_CMSG_SPACE);

  /* must send some msg, single byte will do */
  char dummy    = '\0';
  data.iov_base = &dummy;
  data.iov_len  = sizeof(dummy);

  /* set header values */
  hdr.msg_name       = NULL;
  hdr.msg_namelen    = 0;
  hdr.msg_iov        = &data;
  hdr.msg_iovlen     = 1;
  hdr.msg_control    = buf;
  hdr.msg_controllen = FD_CMSG_SPACE;
  hdr.msg_flags      = 0;

  /* set cmsg header values */
  h = CMSG_FIRSTHDR(&hdr);
  h->cmsg_len   = CMSG_LEN(sizeof(int));
  h->cmsg_level = SOL_SOCKET;
  h->cmsg_type  = SCM_RIGHTS;

  /* pack file descriptor into cmsg */
  ((int *)CMSG_DATA(h))[0] = fd;

  /* send file descriptor, checking for errors */
  assert(sendmsg(KCHAN, &hdr, 0) == 1);

  return;
}

// recv/send params

void
recv_params(param *p) {
  if(p == NULL) {
    return;
  }
  switch(p->ptyp) {
    case PTYP_NUM:
      p->pval.num = recv_num();
      break;
    case PTYP_STR:
      p->pval.pstr = recv_pstr();
      break;
    case PTYP_FD:
      p->pval.fd = recv_fd();
      break;
    default:
      assert(FALSE);
      break;
  }
  recv_params(p->next);
}

void
send_params(param *p) {
  if(p == NULL) {
    return;
  }
  switch(p->ptyp) {
    case PTYP_NUM:
      send_num(p->pval.num);
      break;
    case PTYP_STR:
      send_pstr(p->pval.pstr);
      break;
    case PTYP_FD:
      send_fd(p->pval.fd);
      break;
    default:
      assert(FALSE);
      break;
  }
  send_params(p->next);
}

// recv/send message

msg *
recv_msg(void) {
  uint32_t mtyp;
  param *pay;

  mtyp = recv_num();
  switch(mtyp) {
    case MTYP_LoginReq:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_LoginRes:
      pay = mk_param(PTYP_NUM, NULL);
      recv_params(pay);
      break;
    case MTYP_PubkeyReq:
      pay = NULL;
      recv_params(pay);
      break;
    case MTYP_PubkeyRes:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_KeysignReq:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_KeysignRes:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_CreatePtyerReq:
      pay = NULL;
      recv_params(pay);
      break;
    case MTYP_CreatePtyerRes:
      pay = mk_param(PTYP_FD, mk_param(PTYP_FD, NULL));
      recv_params(pay);
      break;
    case MTYP_SysLoginReq:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_SysLoginRes:
      pay = mk_param(PTYP_STR, mk_param(PTYP_NUM, NULL));
      recv_params(pay);
      break;
    case MTYP_SysPubkeyReq:
      pay = NULL;
      recv_params(pay);
      break;
    case MTYP_SysPubkeyRes:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_SysKeysignReq:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_SysKeysignRes:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_SysCreatePtyerReq:
      pay = mk_param(PTYP_STR, NULL);
      recv_params(pay);
      break;
    case MTYP_SysCreatePtyerRes:
      pay = mk_param(PTYP_FD, mk_param(PTYP_FD, NULL));
      recv_params(pay);
      break;
    default:
      assert(FALSE);
      break;
  }
  return mk_msg(mtyp, pay);
}

void
kraken_send_msg(msg *m) {
  send_num(m->mtyp);
  send_params(m->payload);
}

void send_free(msg* m) {
  kraken_send_msg(m);
  free_msg(m);
}
