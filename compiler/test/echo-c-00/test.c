#include <stdio.h>
#include <unistd.h>
#include "msg.c"

int
main(int argc, char **argv) {
  msg *m;
  char *s;
  
  msg_init(argv[1]);
  while(1) {
    m = mk_M_msg("Hello world!");
    send_msg(m);
    free_msg(m);

    m = recv_msg();
    s = string_of_msg(m);
    printf("%s\n", s);
    free(s);
    free_msg(m);

    sleep(1);
  }
}
