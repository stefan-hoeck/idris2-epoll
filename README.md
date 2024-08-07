# C-Bindings to epoll and related utilities on Linux

This is a small library providing FFI bindings to [epoll](https://www.man7.org/linux/man-pages/man7/epoll.7.html)
and some related utilities. They can be used to implement asynchronous event loops in
Idris.

This library only provides core functionality in `PrimIO` for performance reasons. Users
should write their own safe wrappers for the functions provided here. Still, we already
use simple wrapper types to increase type safety.

```idris
module README

import System.Linux.Epoll
import System.Linux.TimerFD
import System

%default total
```

```idris
timerExample : EpollFD -> IO ()
timerExample efd = do
  tf  <- fromPrim (timerCreate MONOTONIC neutral)
  fromPrim (setTime tf 3.s)
  ignore $ fromPrim (epollAdd efd tf EPOLLIN EPOLLET)
  res <- fromPrim $ epollWait efd (-1)
  case res of
    NoEv       => putStrLn "Epoll returned with NoEv"
    Ev file ev => do
      putStrLn "Epoll returned with file: \{show file}, \{show ev}"
      res <- fromPrim $ readTimer tf
      putStrLn "Timer returned: \{show res}"
    Err x      => putStrLn "Epoll returned error: \{show x}"

stdinExample : EpollFD -> IO ()
stdinExample efd = do
  ignore $ fromPrim (epollAdd efd StdIn EPOLLIN EPOLLET)
  res <- fromPrim $ epollWait efd 5000
  case res of
    NoEv       => putStrLn "Epoll timed out."
    Ev file ev => do
      res <- fromPrim $ readBytes StdIn 0xffff
      case res of
        EOF   => putStrLn "Reached EOF"
        Again => putStrLn "Try again"
        (Bytes n x) => putStrLn "read \{show n} bytes"
        (Err x) => printLn x
    Err x  => putStrLn "Epoll returned error: \{show x}"

main : IO ()
main = do
  Right efd <- epollCreate | Left err => die "\{err}"
  stdinExample efd
```

<!-- vi: filetype=idris2:syntax=markdown
-->
