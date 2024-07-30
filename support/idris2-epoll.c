#include <stdio.h>
#include <errno.h>
#include <sys/epoll.h>

int ep_eagain() {
  return EAGAIN;
}
