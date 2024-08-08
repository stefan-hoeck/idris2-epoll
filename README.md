# C-Bindings to epoll and related utilities on Linux

This is a small library providing FFI bindings to [epoll](https://www.man7.org/linux/man-pages/man7/epoll.7.html)
and some related utilities. They can be used to implement asynchronous event loops in
Idris.

This library only provides core functionality in `PrimIO` for performance reasons. Users
should write their own safe wrappers for the functions provided here. Still, we already
use simple wrapper types to increase type safety.

## Usage Examples

In this section, I show two usage examples of this library. A very simple one, and
one that is a bit involved. First, some imports:

```idris
module README

import System.Linux.Epoll
import System.Linux.SignalFD
import System.Linux.TimerFD
import System

%default total
```

The `epoll` C module is used to monitor several file descriptors at once
for being ready for input or output plus some other events.
With *file descriptors*, we are usually not talking about regular files
on you hard drive, but "special" files such as standard input and output,
streams, FIFOs, sockets, and so on. In addition, Linux allows us to create
file descriptors for timers and signal handlers. We will look at some of these
in the examples below.

Since `epoll` allows us to monitor several things at once, we can use it for
implementing an *event loop*: Block the current thread until something
interesting happens.

### A Simple Timer

The main ingredients for using this library are the following:

* Create an `epoll` file descriptor using `epollCreate`.
* Register some file descriptors for monitoring via `epollAdd`.
* Wait for something interesting to happen by calling
  `epollWait`. This can be done with or without specifying a
  timeout, or even without blocking (`epollNoWait`), in which case
  the function will immediately return `NoEv` in case none of the
  monitored file descriptors is ready yet.

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

covering
stdinExample : EpollFD -> IO ()
stdinExample efd = do
  fromPrim $ blockSignals [SigINT]
  fromPrim $ setNonBlocking StdIn
  sig <- fromPrim $ signalCreate [SigINT] neutral
  ignore $ fromPrim (epollAdd efd StdIn EPOLLIN EPOLLET)
  ignore $ fromPrim (epollAdd efd sig EPOLLIN EPOLLET)
  putStrLn "Hello. Please enter some text. Press 'Ctl-D' or wait for 15 seconds to quit"
  go sig 0
  fromPrim $ close sig

  where
    covering
    readIn,go : SignalFD -> Nat -> IO ()
    go sig tot = do
      res <- fromPrim $ epollWait efd 15000
      case res of
        NoEv    => putStrLn "Epoll timed out."
        Ev 0 ev => readIn sig tot
        Ev x ev =>
          when (x == fileDesc sig) $ do
            putStrLn "\nGot a SIGINT. This would normally stop the app, but we just keep going."
            putStrLn "Remember: Press 'Ctl-D' or wait for 15 seconds to quit."
            _ <- fromPrim $ readSignal sig
            go sig tot
        Err x  => putStrLn "Epoll returned error: \{show x}"

    readIn sig tot = do
      res <- fromPrim $ readBytes StdIn 0x10000
      case res of
        EOF       => putStrLn "Reached EOF after reading \{show tot} bytes"
        Again     => putStrLn "STDIN temporarily exhausted. Waiting for more input." >> go sig tot
        Bytes n b => putStrLn "read \{show n} bytes" >> readIn sig (tot + n)
        Err x     => putStrLn "Error when reading from stdin: \{show x}"

covering
main : IO ()
main = do
  Right efd <- epollCreate | Left err => die "\{err}"
  stdinExample efd
```

<!-- vi: filetype=idris2:syntax=markdown
-->
