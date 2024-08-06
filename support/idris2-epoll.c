#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <sys/signalfd.h>
#include <sys/timerfd.h>
#include <signal.h>
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

struct epoll_event *ep_allocEvent() {
  struct epoll_event *res = malloc(sizeof(struct epoll_event));
  return res;
}

int ep_getFile(struct epoll_event *ev) {
  return ev->data.fd;
}

uint32_t ep_getEvents(struct epoll_event *ev) {
  return ev->events;
}

int ep_epoll_add(int epfd, uint32_t flags, int file, uint32_t events) {
  struct epoll_event ev;
  ev.events = events | flags;
  ev.data.fd = file;

  return epoll_ctl(epfd, EPOLL_CTL_ADD, file, &ev);
}

int ep_epoll_mod(int epfd, uint32_t flags, int file, uint32_t events) {
  struct epoll_event ev;
  ev.events = events | flags;
  ev.data.fd = file;

  return epoll_ctl(epfd, EPOLL_CTL_MOD, file, &ev);
}

int ep_epoll_del(int epfd, int file) {
  return epoll_ctl(epfd, EPOLL_CTL_DEL, file, NULL);
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

uint64_t ep_readEventFile (int efd) {
  uint64_t res = 0;
  ssize_t sz = read(efd, &res, 8);
  if (sz <= 0) {
    return 0;
  } else {
    return res;
  }
}

ssize_t ep_writeEventFile (int efd, uint64_t val) {
  return write(efd, &val, 8);
}

//
// Timer Files
//

int ep_clock_readltime () {
  return CLOCK_REALTIME;
}

int ep_clock_monotonic () {
  return CLOCK_MONOTONIC;
}

int ep_clock_boottime () {
  return CLOCK_BOOTTIME;
}

int ep_clock_realtime_alarm () {
  return CLOCK_REALTIME_ALARM;
}

int ep_clock_boottime_alarm () {
  return CLOCK_BOOTTIME_ALARM;
}

int ep_tfd_cloexec() {
    return TFD_CLOEXEC;
}

int ep_tfd_nonblock() {
    return TFD_NONBLOCK;
}

uint64_t ep_readTimer (int tfd) {
  uint64_t res = 0;
  ssize_t sz = read(tfd, &res, 8);
  if (sz <= 0) {
    return 0;
  } else {
    return res;
  }
}

void *ep_setTime (int tfd, time_t secs, uint32_t nanos) {
    struct itimerspec spec;
    spec.it_interval.tv_sec = 0;
    spec.it_interval.tv_nsec = 0;
    spec.it_value.tv_sec = secs;
    spec.it_value.tv_nsec = nanos;
    timerfd_settime(tfd, 0, &spec, NULL);
}

//
// Signal Files
//

int ep_sfd_cloexec() {
    return SFD_CLOEXEC;
}

int ep_sfd_nonblock() {
    return SFD_NONBLOCK;
}

sigset_t *ep_allocSignalset() {
    sigset_t *res = malloc(sizeof(sigset_t));
    sigemptyset(res);
    return res;
}

int ep_sigblock(const sigset_t *set) {
    return sigprocmask(SIG_BLOCK,set, NULL);
}

int ep_readSignal(int sfd) {
    struct signalfd_siginfo res;
    ssize_t sz = read(sfd, &res, sizeof(struct signalfd_siginfo));
    if (sz <= 0) {
      return 0;
    } else {
      return res.ssi_signo;
    }
}
