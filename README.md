# C-Bindings to epoll and related utilities on Linux

This is a small library providing FFI bindings to [epoll](https://www.man7.org/linux/man-pages/man7/epoll.7.html)
and some related utilities. They can be used to implement asynchronous event loops in
Idris.

This library only provides core functionality in `PrimIO` for performance reasons. Users
should write their own safe wrappers for the functions provided here. Still, we already
use a few simple wrapper types and utility functions to increase type safety.

## Usage Examples

In this section, I show three usage examples of this library. A very simple one, and
two that are a bit more involved. First, some imports:

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
on the hard drive, but "special" files such as standard input and output,
streams, FIFOs, sockets, and so on. In addition, Linux allows us to create
file descriptors for timers and signal handlers. We will look at some of these
in the examples below.

Since `epoll` allows us to monitor several things at once, we can use it for
implementing *event loops*: Loops that block the current thread exactly
until something interesting happens.

### A Simple Timer

The main ingredients for using this library are the following:

* Create an `epoll` file descriptor using `epollCreate`.
* Register some file descriptors for monitoring via `epollAdd`.
* Wait for something interesting to happen by calling
  `epollWait`. This can be done with or without specifying a
  timeout, or even without blocking (`epollNoWait`), in which case
  the function will immediately return `NoEv` in case none of the
  monitored file descriptors is ready yet.

The example code below demonstrates how this works in practice:
We create a timer file descriptor based on the `MONOTONIC`
clock without additional flags. The timeout is then set to three
seconds. Just using `read` on such a timer file would block the
current thread until the time is up. This is not very useful: We
could just use `sleep` for this kind of behavior. However, we might
not just want to sleep but do some other stuff in the meantime.
Therefore, we register the timer at `epoll` with `epollAdd`
and wait for `epoll` to fire its next event (`epollWait`).

Here's the full example.

```idris
timerExample : EpollFD -> IO ()
timerExample efd = do
  -- create a timer file descriptor
  tf  <- fromPrim (timerCreate MONOTONIC neutral)

  -- set the timer at three seconds
  fromPrim (setTime tf 3.s)

  -- observe the timer with epoll
  ignore $ fromPrim (epollAdd efd tf EPOLLIN EPOLLET)

  -- infinitely await the next file event
  res <- fromPrim $ epollWait efd (-1)

  -- process the result and print what we got
  case res of
    Ev file ev => do
      putStrLn "Epoll returned with file: \{show file}, \{show ev}"
      res <- fromPrim $ readTimer tf
      putStrLn "Timer returned: \{show res}"
    Err x      => putStrLn "Epoll returned error: \{show x}"
    NoEv       => putStrLn "Epoll returned with NoEv"
```

### A Countdown that can be stopped

Let's do something more interesting: We create a countdown of twenty
seconds that can be aborted with `SIGINT`. This could be implemented
in several ways:

* A *busy loop* that keeps checking for the signal
  without doing anything else until the time is up. While such a loop is
  very easy to write, it will eat up *a lot* of CPU time while doing
  absolutely nothing!
* A loop with a fine grained amount of sleeping (one millisecond or so).
  This will free the CPU for doing work in other processes, but it will
  still mostly block the current thread. Since threads are a scarce resource,
  we do not want to ever block them unless there is *really* nothing else
  to do.
* Using `epoll` to listen on two or more file descriptors. This will also
  block the current thread, but it will allow us to register additional
  events from another thread, or even wake up the current thread via
  an *event file descriptor*.

Here is the annotated code:

```idris
countdownExample : EpollFD -> IO ()
countdownExample efd = do
  -- create a timer file descriptor
  tf  <- fromPrim (timerCreate MONOTONIC neutral)

  -- block normal processing for `[SigINT]`
  fromPrim $ blockSignals [SigINT]
  -- create a signal handler
  sig <- fromPrim $ signalCreate [SigINT] neutral

  -- observe the timer and signal with epoll
  ignore $ fromPrim (epollAdd efd tf EPOLLIN EPOLLET)
  ignore $ fromPrim (epollAdd efd sig EPOLLIN EPOLLET)

  -- loop for the countdown
  go 10 tf sig

  -- cleanup
  fromPrim $ close tf
  fromPrim $ close sig

  where
    go : Nat -> TimerFD -> SignalFD -> IO ()
    -- we are done. print a goodbye message.
    go 0     tf sig = putStrLn "Time's up. Goodbye!"

    -- we are done. print a goodbye message.
    go (S k) tf sig = do
      putStrLn "\{show $ S k} s left"
      --set the timer to 1 s.
      fromPrim (setTime tf 1.s)

      -- infinitely await the next file event, which will be either
      -- the timer or the signal handler
      res <- fromPrim $ epollWait efd (-1)

      -- process the result and print what we got
      case res of
        NoEv       => putStrLn "Epoll returned with NoEv"
        Ev file ev => case file == fileDesc tf of
          False => putStrLn "\nCountdown aborted by SIGINT. Goodbye!"
          True  => ignore (fromPrim $ readTimer tf) >> go k tf sig
        Err x      => putStrLn "Epoll returned error: \{show x}"
```

### Reading from `stdin`

In the example below, we are going to read input from `stdin` handling
`SIGINT` at the same time.

In this case, we use the `EPOLLET` flag for *edge-triggered* polling. In this mode,
`epoll` will create an event only when the readiness of a file descriptor *changes*.
For instance: When data becomes available on standard input, we will be notified.
If we then read from standard input, we must make sure to keep doing so until
no bytes are left before invoking `epollWait` again, otherwise, `epoll` will not
fire another event even though there is still data that could be read from standard
input.

The above means that we either need to be certain that a single read will
completely consume the data currently ready in a file descriptor (this works with
timers and signals, for instance), or the file must be used in *non-blocking* mode,
in which case a call to `readBytes` will return `Again` when there is currently
no data left and it is safe to use `epollWait` again.

Here's the code:

```idris
covering
stdinExample : EpollFD -> IO ()
stdinExample efd = do
  -- block `SigINT`, create the signal handler, and add it to `epoll`
  fromPrim $ blockSignals [SigINT]
  sig <- fromPrim $ signalCreate [SigINT] neutral
  ignore $ fromPrim (epollAdd efd sig EPOLLIN EPOLLET)

  -- set `StdIn` to non-blocking and add it to `epoll`
  fromPrim $ setNonBlocking StdIn
  ignore $ fromPrim (epollAdd efd StdIn EPOLLIN EPOLLET)

  -- print some text, loop, and cleanup
  putStrLn "Hello. Please enter some text. Press 'Ctl-D' or wait for 15 seconds to quit"
  go sig 0
  fromPrim $ close sig

  where
    covering
    readIn,go : SignalFD -> Nat -> IO ()

    -- wait for a file event with a timeout of 15 seconds
    go sig tot = do
      res <- fromPrim $ epollWait efd 15000
      case res of
        -- epoll timed out
        NoEv    => putStrLn "Epoll timed out."

        -- there is data available at standard input, let's see what we got
        Ev 0 ev => readIn sig tot

        -- we caught `SIGINT`. let's print some info and continue
        Ev x ev =>
          when (x == fileDesc sig) $ do
            putStrLn "\nGot SIGINT. This would normally stop the app, but we just keep going."
            putStrLn "Remember: Press 'Ctl-D' or wait for 15 seconds to quit."
            _ <- fromPrim $ readSignal sig
            go sig tot

        -- an error occured.
        Err x  => putStrLn "Epoll returned error: \{show x}"

    -- this reads until standard input is (temporarily) exhausted and `readBytes`
    -- returns `Again` or `EOF`.
    readIn sig tot = do
      res <- fromPrim $ readBytes StdIn 0x10000
      case res of
        EOF       => putStrLn "Reached EOF after reading \{show tot} bytes"
        Again     => putStrLn "STDIN temporarily exhausted. Waiting for more input." >> go sig tot
        Bytes n b => putStrLn "read \{show n} bytes" >> readIn sig (tot + n)
        Err x     => putStrLn "Error when reading from stdin: \{show x}"
```

Feel free to test the application above by piping several large files into it. It will be
very interesting to see the interplay between data production and consuption. Try adjusting
the buffer size and observe its effect on performance. It is safe to use this with
very large files. On my system, for instance, this can process 3 GB of data in about
two seconds.

As an example, run the app via pack:

```sh
pack run epoll-docs
```

Next, pipe some data into it:

```sh
cat ./**/*.idr | docs/build/exec/epoll-docs stdin
```

### The `main` function

```idris
covering
main : IO ()
main = do
  Right efd <- epollCreate | Left err => die "\{err}"
  [_,v] <- getArgs | _ => timerExample efd
  case v of
    "timer"     => timerExample efd
    "stdin"     => stdinExample efd
    "countdown" => countdownExample efd
    _           => timerExample efd
```

<!-- vi: filetype=idris2:syntax=markdown
-->
