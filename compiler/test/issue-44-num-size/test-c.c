#include <stdio.h>
#include <unistd.h>
#include "msg.h"

int
main(int argc, char **argv) {
  msg *m;
  char *s;

  msg_init(argv[1]);

  while(TRUE) {
    m = recv_msg();
    s = string_of_msg(m);
    printf("%s\n", s);
    free(s);
    free_msg(m);

    sleep(1);
  }

  return 0;
}
