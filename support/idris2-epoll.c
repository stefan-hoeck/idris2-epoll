#include <stdio.h>
#include <errno.h>
#include <sys/epoll.h>

//
// Error codes
//

int ep_eagain() {
  return EAGAIN;
}

//
// Operations
//

int ep_epoll_ctl_add() {
  return EPOLL_CTL_ADD;
}

int ep_epoll_ctl_mod() {
  return EPOLL_CTL_MOD;
}

int ep_epoll_ctl_del() {
  return EPOLL_CTL_DEL;
}
