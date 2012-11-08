#include <stdio.h>
#include <unistd.h>
#include "msg.h"

int
main(int argc, char **argv) {
  msg *m;
  msg_init(argv[1]);

  while(TRUE) {
    m = recv_msg();
    print_msg(m);
    free_msg(m);

    sleep(1);
  }

  return 0;
}
