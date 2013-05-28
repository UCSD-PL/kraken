#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <sys/select.h>
#include <sys/time.h>
#include <sys/types.h>
#include <fcntl.h>

void write_msg_id (int socket, char msg_id) {
  if (write(socket, &msg_id, 1) != 1) 
    return;
}

void write_param (int socket, char *param, int size) {
  //unsigned int size = strlen(param);
  if (write(socket, &size, 4) != 4) return;
  if(size > 0) {
    if (write(socket, param, size) != size) return;
  }
}

void write_msg(int socket, char msg_id,char *param, int size) {
  write_msg_id(socket, msg_id);
  write_param(socket, param, size);
}

char read_msg_id(int socket) {
  char c = 0;
  if (read(socket, &c, 1) != 1) return -1;
  return c;
}

int read_param(int socket, char *result, int len) {
  unsigned int size;
  int to_read, did_read, read_so_far;
  char buf[1024];
  int read_char = 0;

  //printf("read param started:%d\n", socket); fflush(stdout);
  read_char = read(socket, &size, 4);

  //printf("read param started:size:%d\n", size); fflush(stdout);

  if(size > len) {
    return; // bug
  }

  //printf("read param started size:%d, %d, %d\n", read_char, socket, size); fflush(stdout);

  read_char = read_char;
  read_so_far = 0;
  while (read_so_far < size) {
    //printf("must not be entered\n"); fflush(stdout);
    to_read = size - read_so_far;
      
    if (to_read >= 1024) {
      to_read = 1024;
    }

    //printf("to_read:%d\n", to_read); fflush(stdout);
    //printf("must not be entered:%d\n", to_read); fflush(stdout);
    did_read = read(socket, buf, to_read);
    //printf("result:%d\n", did_read); fflush(stdout);

    if (result) {
      if (read_so_far + did_read > len -1) {
	memcpy(result, buf, (len-1) - read_so_far);
	result[len-1] = 0;
	result = NULL;
      } else {
	memcpy(result, buf, did_read);
	result += did_read;
      }
    }
    read_so_far += did_read;
  }

  //printf("read param terminated:%d\n", socket);
  if (result) result[0] = 0;

  return size;
}

int read_msg(int socket, char msg_id, char* buf, int len) {

  char* param_ptr = NULL;
  char c;
  c = read_msg_id(socket);
  
  //printf("read msg id :%d, %d\n", socket, c);
  if (c < 0) {
    return -1;
  }

  while(c != msg_id) {
    //printf("received msg id is not what we expected %d %d\n", socket, c);
    read_param(socket, buf, len);
    c = read_msg_id(socket);
  }
  read_param(socket, buf, len);
}

#define CMSG_SIZE CMSG_SPACE(sizeof(int))

int _recvfd(int sock, size_t *len, void *buf) {
  struct iovec iov[1];
  struct msghdr msgh;
  char cmsgbuf[CMSG_SIZE];
  char extrabuf[4096];
  struct cmsghdr *h;
  int st, fd;

  if(*len < 1 || buf == NULL) {
    /* For some reason, again, one byte needs to be received. (it would not
     * block?) */
    iov[0].iov_base = extrabuf;
    iov[0].iov_len  = sizeof(extrabuf);
  } else {
    iov[0].iov_base = buf;
    iov[0].iov_len  = *len;
  }

  msgh.msg_name       = NULL;
  msgh.msg_namelen    = 0;

  msgh.msg_iov        = iov;
  msgh.msg_iovlen     = 1;

  msgh.msg_control    = cmsgbuf;
  msgh.msg_controllen = CMSG_SIZE;
  msgh.msg_flags      = 0;

  st = recvmsg(sock, &msgh, 0);

  if(st < 0) {
    return -1;
  }

  //printf("size_t:%d int:%d\n", sizeof(size_t), sizeof(int));
  *len = st;

  h = CMSG_FIRSTHDR(&msgh);
  /* Check if we received what we expected */
  if((h == NULL)
     || h->cmsg_len    != CMSG_LEN(sizeof(int))
     || h->cmsg_level  != SOL_SOCKET
     || h->cmsg_type   != SCM_RIGHTS) {
    return -2;
  }

  fd = ((int *)CMSG_DATA(h))[0];
  if(fd < 0)
    return -3;
  return fd;
}

int get_pty (int socket) {	
  char buf[1024];
  char *dummy = NULL;
  size_t len;
  int rsock;

  buf[0] = 0;
  write_msg(socket, (char) 0, buf, 0);

  if (read_msg(socket, 1, buf, 1024) == -1) {
    //fprintf(stderr, "SLV] read_msg failed\n"); fflush(stderr);
    return -1;
  }

  len = 0;
  rsock = _recvfd(socket, &len, NULL);

  //printf("SLV] rsock : %d\n", rsock); fflush(stdout);
	
  struct stat statbuf;
  fstat(rsock, &statbuf);
  /*
  if(!S_ISSOCK(statbuf.st_mode)) {
    fprintf(stderr, "SLV] this is not a socket\n"); fflush(stderr);
    return -1;
  }
  */

  return rsock;
}

int _sendfd(int socket, int fd) {
  struct iovec iov[1];
  struct msghdr msgh;
  char buf[CMSG_SIZE];
  struct cmsghdr *h;
  int ret;

  int len = 1;
  char* msg = "\0";

  /* At least one byte needs to be sent, for some reason (?) */
  if(len < 1) {
    return -1;
  }

  memset(&iov[0], 0, sizeof(struct iovec));
  memset(&msgh, 0, sizeof(struct msghdr));
  memset(buf, 0, CMSG_SIZE);

  msgh.msg_name       = NULL;
  msgh.msg_namelen    = 0;

  msgh.msg_iov        = iov;
  msgh.msg_iovlen     = 1;

  msgh.msg_control    = buf;
  msgh.msg_controllen = CMSG_SIZE;
  msgh.msg_flags      = 0;

  /* Message to be sent */
  iov[0].iov_base = (void *)msg;
  iov[0].iov_len  = len;

  /* Control data */
  h = CMSG_FIRSTHDR(&msgh);
  h->cmsg_len   = CMSG_LEN(sizeof(int));
  h->cmsg_level = SOL_SOCKET;
  h->cmsg_type  = SCM_RIGHTS;
  ((int *)CMSG_DATA(h))[0] = fd;

  ret = sendmsg(socket, &msgh, 0);
  return ret;
}

//#define INTERPROC_TEST 1
#ifdef INTERPROC_TEST

int main() {

  // DON:C:BEGIN
  int len = 0;
  int t_fd = 0;
  int msg_id;
  char buf[1024];
  pid_t pid; 
  int fd[2];
  static const int PSOCKET = 0;
  static const int CSOCKET = 1;
  // DON:C:END
  int slv_socket;
  int mon_socket;

  // DON:C:BEGIN
  //socketpair(PF_LOCAL, SOCK_STREAM, 0, fd);
  socketpair(PF_UNIX, SOCK_DGRAM, 0, fd);

  pid = fork();
  
  if (pid < 0) {
    exit(-1);
  }

  if (pid == 0) {
    //printf("SLV] slave is initiated\n"); fflush(stdout);
    /* Child:slave */
    /* TODO: drop the root privileges here */
    close(fd[PSOCKET]);
    slv_socket = fd[CSOCKET];
    
    /*
    t_fd = get_pty (slv_socket);
    printf("SLV] read char %d\n", read(t_fd, buf, 1024));
    //buf[read(t_fd, buf, 1024)] = 0;
    printf("SLV] read str : %s\n", buf);
    */

    buf[0] = 0;
    write_msg(slv_socket, 0, buf, 1024);
    read_msg(slv_socket, 1, buf, 1024);
    t_fd = _recvfd(slv_socket, &len, NULL);
    //printf("SLV] read char %d\n", read(t_fd, buf, 1024));
    //buf[read(t_fd, buf, 1024)] = 0;
    //printf("SLV] read str : %s\n", buf);

    /*
    t_fd = _recvfd(slv_socket, &len, buf);
    printf("SLV] read char %d\n", read(t_fd, buf, 1024));
    printf("SLV] read str : %s\n", buf);
    */
  } else {
    //printf("MON] monitor is initiated\n"); fflush(stdout);
    /* Parent:monitor */
    close(fd[CSOCKET]);
    mon_socket = fd[PSOCKET];

    msg_id = read_msg_id(mon_socket);
    read_param(mon_socket, buf, 1024);
    //printf("MON] read buf:%d %d\n", buf[0], buf[1]);
    write_msg_id(mon_socket, 1);
    //buf[0] = 11;
    //buf[1] = 0;
    buf[0] = 0;
    write_param(mon_socket, buf, 0);
    _sendfd(mon_socket, open("data", O_RDONLY));
    while(1) {}
    /*
    while(1) {
      msg_id = read_msg_id(mon_socket);
      if(msg_id == 0) {
	//read_param(mon_socket, buf, 1024);
	buf[0] = 0;
	write_msg(mon_socket, 0, buf);
	if(_sendfd(mon_socket, open("data", O_RDONLY)) < 0) {
	  fprintf(stderr, "MON] _sendfd failed on monitor\n"); fflush(stderr);
	}
      }
    }
    */
  }
  // DON:C:END
}
#endif
