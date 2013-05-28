#include <shadow.h>
#include <stdlib.h>
#include <stdio.h>
#include <pwd.h>
#include "kauth.h"

int check_login(char* user, char* passwd) {
  struct passwd *pw;
  char *epasswd;
  char *tty;

#ifdef USE_SHADOW
  struct spwd *spwd;
  struct spwd *getspnam();
#endif

  if ((pw = getpwnam(user)) == NULL) {
    return 1;
  }
    
#ifdef USE_SHADOW
  pw->pw_passwd = NULL;
  spwd = getspnam(user);
  if (spwd) {
    pw->pw_passwd = spwd->sp_pwdp;
  }
#endif
  /*
   * XXX If no passwd, let NOT them login without one.
   */
  if (pw->pw_passwd == '\0') {
    return 1;
  }
#ifdef HAS_SHADOW
  if ((pw->pw_passwd && pw->pw_passwd[0] == '@'
       && pw_auth (pw->pw_passwd+1, pw->pw_name, PW_LOGIN, NULL))
      || !valid (passwd, pw)) {
    return 1;
  }
#else
  epasswd = crypt(passwd, pw->pw_passwd);
  if (strcmp(epasswd, pw->pw_passwd)) {
    return 1;
  }
#endif
  return 0;
}
/*
int main() {
  printf("login:%d\n", login());
}
*/
