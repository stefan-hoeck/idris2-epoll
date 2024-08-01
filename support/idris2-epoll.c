#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <unistd.h>

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

//
// Utilities
//

int ep_errno() {
  return errno;
}

struct epoll_event *ep_allocEvent(int n) {
  struct epoll_event *res = malloc(n * sizeof(struct epoll_event));
  return res;
}

void *ep_setEvent(struct epoll_event *ev, int events) {
  ev->events = events;
}

void *ep_setFile(struct epoll_event *ev, int file) {
  ev->data.fd = file;
}

int ep_getFile(struct epoll_event *ev) {
  return ev->data.fd;
}

struct epoll_event *ep_eventAt(struct epoll_event *ev, int ix) {
  return &ev[ix];
}

//
// Event Files
//

int ep_efd_cloexec() {
    return EFD_CLOEXEC;
}

int ep_efd_nonblock() {
    return EFD_NONBLOCK;
}

int ep_efd_semaphore() {
    return EFD_SEMAPHORE;
}

ssize_t ep_readEventFile (int efd, uint64_t *val) {
  return read(efd, val, 8);
}

ssize_t ep_writeEventFile (int efd, uint64_t *val) {
  return write(efd, val, 8);
}
