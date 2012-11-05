#include <stdio.h>
#include <unistd.h>
#include "msg.h"

#define N 10

int
main(int argc, char **argv) {
  msg *m;
  pstr *ps1, *ps2;
  char *s;
  int i;

  msg_init(argv[1]);
  ps1 = pstr_of_string("Hello world!");
  ps2 = mk_pstr(4, "\x00\x01\x02\x03");

  for(i=0; i<N; i++) {
    m = mk_M_msg(ps1);
    send_msg(m);
    free_msg(m);

    m = recv_msg();
    s = string_of_msg(m);
    printf("%s\n", s);
    free(s);
    free_msg(m);

    m = mk_M_msg(ps2);
    send_msg(m);
    free_msg(m);

    m = recv_msg();
    s = string_of_msg(m);
    printf("%s\n", s);
    free(s);
    free_msg(m);

    sleep(1);
  }

  free_pstr(ps1);
  free_pstr(ps2);
  return 0;
}
