# C-Bindings to epoll and related utilities on Linux

This is a small library providing FFI bindings to [epoll](https://www.man7.org/linux/man-pages/man7/epoll.7.html)
and some related utilities. They can be used to implement asynchronous event loops in
Idris.

This library only provides core functionality in `PrimIO` for performance reasons. Users
should write their own safe wrappers for the functions provided here. Still, we already
use simple wrapper types to increase type safety.
