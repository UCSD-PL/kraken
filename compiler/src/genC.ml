open Common
open Kernel

let c_mtyp tag_map m =
  mkstr "  MTYP_%s = %d,"
    m.tag (List.assoc m.tag tag_map)

let c_mtyp_str m =
  String.concat "\n"
    [ mkstr "    case MTYP_%s:" m.tag
    ; mkstr "      return strdup(\"%s\");" m.tag
    ]

let c_typ = function
  | Num -> "uint32_t"
  | Str -> "char *"
  | Fdesc -> "int"

let c_ptyp = function
  | Num -> "PTYP_NUM"
  | Str -> "PTYP_STR"
  | Fdesc -> "PTYP_FD"

let c_mk_param_typ = function
  | Num -> "mk_num_param"
  | Str -> "mk_str_param"
  | Fdesc -> "mk_fd_param"

let c_msg_ctor m =
  let args =
    m.payload
      |> mapi (fun i t -> mkstr "%s p%d" (c_typ t) i)
      |> String.concat ", "
  in
  (* foldr for this is just too ugly *)
  let pay =
    let rec loop i = function
      | [] -> "NULL"
      | t::ts -> mkstr "%s(p%d, %s)" (c_mk_param_typ t) i (loop (i+1) ts)
    in
    loop 0 m.payload
  in
  String.concat "\n"
    [       "msg *"
    ; mkstr "mk_%s_msg(%s) {" m.tag args
    ; mkstr "  return mk_msg(MTYP_%s, %s);" m.tag pay
    ;       "}"
    ]

let c_recv_msg m =
  let pay =
    List.fold_right
      (fun t acc -> mkstr "mk_param(%s, %s)" (c_ptyp t) acc)
      m.payload
      "NULL"
  in
  String.concat "\n"
    [ mkstr "    case MTYP_%s:" m.tag
    ; mkstr "      pay = %s;" pay
    ;       "      recv_params(pay);"
    ;       "      break;"
    ]

(* c msg lib template has string holes for
 *  1. mtyp enum cases
 *  2. ctor for each msg type
 *  3. mtyp string cases
 *  4. recv cases
 *)
let c_template = format_of_string "
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <assert.h>

#define TRUE     1
#define FALSE    0
#define NUM_SIZE 1

// cmsg size for 1 file descriptor
#define FD_CMSG_SPACE CMSG_SPACE(sizeof(int))

// global socket for all kernel communication
int KCHAN;

// Programs using this lib should be forked from a Kraken kernel which will
// set up a socket for communication and pass it to the child as a command
// line argument in the exec. msg_init(arg) takes that argument, makes it a
// socket, and stores it in KCHAN.
void
msg_init(char *arg) {
  KCHAN = atoi(arg);
}

// messages

typedef enum param_t {
  PTYP_NUM,
  PTYP_STR,
  PTYP_FD,
} param_t;

typedef union param_v {
  uint32_t num;
  char *str;
  int fd;
} param_v;

typedef struct param {
  param_t ptyp;
  param_v pval;
  struct param *next;
} param;

typedef enum msg_t {
%s
} msg_t;

typedef struct msg {
  msg_t mtyp;
  param *payload;
} msg;

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
mk_str_param(char *s, param *next) {
  param *p;

  p = alloc_param();
  p->ptyp = PTYP_STR;
  p->pval.str = strdup(s);
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

%s

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
      free(p->pval.str);
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
%s
    default:
      assert(FALSE);
      break;
  }
}

char *
string_of_params(param *p) {
  char *s, *h, *t;
  int n;

  if(p == NULL) {
    return strdup(\"\");
  }
  switch(p->ptyp) {
    case PTYP_NUM:
      h = zsprintf(\"%%d\", p->pval.num);
      break;
    case PTYP_STR:
      h = zsprintf(\"\\\"%%s\\\"\", p->pval.str);
      break;
    case PTYP_FD:
      h = zsprintf(\"fd(%%d)\", p->pval.fd);
      break;
    default:
      assert(FALSE);
      break;
  }
  if(p->next == NULL) {
    s = h;
  } else {
    t = string_of_params(p->next);
    s = zsprintf(\"%%s, %%s\", h, t);
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
  s = zsprintf(\"%%s(%%s)\", ms, ps);
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
  buf = ((char *)&x) + sizeof(x) - NUM_SIZE;
  n = recv(KCHAN, buf, NUM_SIZE, 0);
  assert(n == NUM_SIZE);
  // convert to host endian
  x = ntohl(x);
  return x;
}

void
send_num(uint32_t x) {
  char *buf;
  int n;

  // for now, num is only 1 byte, check bounds
  assert(0 <= x && x <= 255);

  // convert to big endian
  x = htonl(x);
  buf = ((char *)&x) + sizeof(x) - NUM_SIZE;
  n = send(KCHAN, buf, NUM_SIZE, 0);
  assert(n == NUM_SIZE);
}

char *
recv_str(void) {
  uint32_t len;
  char *buf;
  int n;

  len = recv_num();
  buf = (char *)malloc(len);
  assert(buf != NULL);
  n = recv(KCHAN, buf, len, 0);
  assert(n == len);
  return buf;
}

void
send_str(char *buf) {
  uint32_t len;
  int n;

  len = strlen(buf);
  send_num(len);
  n = send(KCHAN, buf, len, 0);
  assert(n == len);
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
  char dummy    = '\\0';
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
  char dummy    = '\\0';
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
      p->pval.str = recv_str();
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
      send_str(p->pval.str);
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
%s
    default:
      assert(FALSE);
      break;
  }
  return mk_msg(mtyp, pay);
}

void
send_msg(msg *m) {
  send_num(m->mtyp);
  send_params(m->payload);
}
"

let c_lib s =
  let tm = gen_tag_map s in
  let fmt l f =
    String.concat "\n" (List.map f l)
  in
  mkstr c_template
    (fmt s.msg_decls (c_mtyp tm))
    (fmt s.msg_decls c_msg_ctor)
    (fmt s.msg_decls c_mtyp_str)
    (fmt s.msg_decls c_recv_msg)
