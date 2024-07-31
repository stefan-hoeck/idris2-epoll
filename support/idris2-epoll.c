#include <stdio.h>
#include <errno.h>
#include <sys/epoll.h>

//
// Error codes
//

int ep_eagain() {
  return EAGAIN;
}

int ep_ebadf() {
  return EBADF;
}

int ep_eexist() {
  return EEXIST;
}

int ep_einval() {
  return EINVAL;
}

int ep_eloop() {
  return ELOOP;
}

int ep_enoent() {
  return ENOENT;
}

int ep_enomem() {
  return ENOMEM;
}

int ep_enospc() {
  return ENOSPC;
}

int ep_eperm() {
  return EPERM;
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

//
// Flags
//

int ep_epollet() {
  return EPOLLET;
}

int ep_epolloneshot() {
  return EPOLLONESHOT;
}

int ep_epollwakeup() {
  return EPOLLWAKEUP;
}

int ep_epollexclusive() {
  return EPOLLEXCLUSIVE;
}
