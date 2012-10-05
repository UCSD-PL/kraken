#include <stdio.h>
#include <unistd.h>
#include "msg.c"

int
main(int argc, char **argv) {
  msg *m;
  
  msg_init(argv[1]);
  while(1) {
    m = mk_M_msg("Hello world!");
    send_msg(m);
    free_msg(m);

    m = recv_msg();
    // TODO handle mem leak from string_of_msg
    printf("%s\n", string_of_msg(m));
    free_msg(m);

    sleep(1);
  }
}
