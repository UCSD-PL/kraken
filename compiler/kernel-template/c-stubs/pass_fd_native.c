#include <sys/types.h>
#include <sys/socket.h>
#include <string.h>
#include <assert.h>
#include <caml/mlvalues.h>

/* cmsg size for 1 file descriptor */
#define FD_CMSG_SPACE CMSG_SPACE(sizeof(int))

int _recv_fd_native(int sock) {
  struct msghdr hdr;
  struct iovec data;
  char buf[FD_CMSG_SPACE];
  struct cmsghdr *h;
  int n, fd;

  /* must recv some msg, single byte will do */
  char dummy    = '\0';
  data.iov_base = &dummy;
  data.iov_len  = sizeof(dummy);

  /* init everything to 0 */
  memset(&hdr, 0, sizeof(struct msghdr));
  memset(&data, 0, sizeof(struct iovec));
  memset(buf, 0, FD_CMSG_SPACE);

  /* set header values */ 
  hdr.msg_name       = NULL;
  hdr.msg_namelen    = 0;
  hdr.msg_iov        = &data;
  hdr.msg_iovlen     = 1;
  hdr.msg_control    = buf;
  hdr.msg_controllen = FD_CMSG_SPACE;
  hdr.msg_flags      = 0;
      
  /* recv file descriptor */
  n = recvmsg(sock, &hdr, 0);

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

void _send_fd_native(int sock, int fd) {
  struct msghdr hdr;
  struct iovec data;
  char buf[FD_CMSG_SPACE];
  struct cmsghdr *h;

  /* must send some msg, single byte will do */
  char dummy    = '\0';
  data.iov_base = &dummy;
  data.iov_len  = sizeof(dummy);

  /* init everything to 0 */
  memset(&hdr, 0, sizeof(struct msghdr));
  memset(&data, 0, sizeof(struct iovec));
  memset(buf, 0, FD_CMSG_SPACE);

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
  assert(sendmsg(sock, &hdr, 0) == 0);

  return;
}

/* ocaml wrappers */

CAMLprim value recv_fd_native(value v0) {
  int sock, fd;
  sock = Int_val(v0);
  fd = _recv_fd_native(sock);
  return Val_int(fd);
}

CAMLprim value send_fd_native(value v0, value v1) {
  int sock, fd;
  sock = Int_val(v0);
  fd = Int_val(v1);
  _send_fd_native(sock, fd);
  return Val_unit;
}
