#define LOGIN_REQ 0
#define LOGIN_RES 1

#define REGENERATE_REQ 2
#define REGENERATE_RES_INIT 3

#define STATE_MIGRATION_REQ 4

#define KEY_SIGN_REQ 5
#define KEY_SIGN_RES 6

#define PUB_KEY_REQ 7
#define PUB_KEY_RES 8

void write_msg_id (int socket, char msg_id);
void write_param (int socket, char *param, int size);
void write_msg(int socket, char msg_id,char *param, int size);
char read_msg_id(int socket);
int read_param(int socket, char *result, int len);
int read_msg(int socket, char msg_id, char* buf, int len);
int _recvfd(int sock, size_t *len, void *buf);
int get_pty (int socket);
int _sendfd(int socket, int fd);

