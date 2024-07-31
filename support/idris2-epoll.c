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

//
// Events
//

int ep_epollin() {
  return EPOLLIN;
}

int ep_epollout() {
  return EPOLLOUT;
}

int ep_epollrdhup() {
  return EPOLLRDHUP;
}

int ep_epollpri() {
  return EPOLLPRI;
}

int ep_epollerr() {
  return EPOLLERR;
}

int ep_epollhup() {
  return EPOLLHUP;
}
