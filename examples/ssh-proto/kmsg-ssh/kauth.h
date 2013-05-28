#define USE_SHADOW 

/*
 * login - Check the user name and password against the system
 * password database.
 *
 * This function has been modified to support the Linux Shadow Password
 * Suite if USE_SHADOW is defined.
 *
 * returns:
 *      1: Checking failed.
 *      0: Cheking succeeded.
 */

int check_login(char* user, char* passwd);
