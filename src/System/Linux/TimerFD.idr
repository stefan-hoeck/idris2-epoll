module System.Linux.TimerFD

import Data.Bits
import Derive.Finite
import Derive.Prelude
import System.Linux.Error
import System.Linux.File
import public System.Clock

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:ep_clock_realtime,epoll-idris"
ep_clock_realtime : Bits32

%foreign "C:ep_clock_monotonic,epoll-idris"
ep_clock_monotonic : Bits32

%foreign "C:ep_clock_boottime,epoll-idris"
ep_clock_boottime : Bits32

%foreign "C:ep_clock_realtime_alarm,epoll-idris"
ep_clock_realtime_alarm : Bits32

%foreign "C:ep_clock_boottime_alarm,epoll-idris"
ep_clock_boottime_alarm : Bits32

%foreign "C:ep_tfd_cloexec,epoll-idris"
ep_tfd_cloexec : Bits32

%foreign "C:ep_tfd_nonblock,epoll-idris"
ep_tfd_nonblock : Bits32

%foreign "C:timerfd_create,epoll-idris"
prim__timerfd_create : Bits32 -> Bits32 -> PrimIO Bits32

%foreign "C:ep_readTimer,epoll-idris"
prim__ep_readTimer : Bits32 -> PrimIO Bits64

%foreign "C:ep_setTime,epoll-idris"
prim__ep_setTime : Bits32 -> Int64 -> Bits32 -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

public export
data ClockTpe : Type where
  REALTIME       : ClockTpe
  MONOTONIC      : ClockTpe
  BOOTTIME       : ClockTpe
  REALTIME_ALARM : ClockTpe
  BOOTTIME_ALARM : ClockTpe

%runElab derive "ClockTpe" [Show,Eq,Finite]

export
clockCode : ClockTpe -> Bits32
clockCode REALTIME       = ep_clock_realtime
clockCode MONOTONIC      = ep_clock_monotonic
clockCode BOOTTIME       = ep_clock_boottime
clockCode REALTIME_ALARM = ep_clock_realtime_alarm
clockCode BOOTTIME_ALARM = ep_clock_boottime_alarm

||| Flags describing the behavior of an timer file descriptor.
|||
||| Several flags can be combined using `(<+>)`.
export
record Flags where
  constructor F
  value : Bits32

%runElab derive "Flags" [Show,Eq,Ord]

export %inline
flagCode : Flags -> Bits32
flagCode = value

export %inline
Semigroup Flags where
  F x <+> F y = F (x .|. y)

export %inline
Monoid Flags where neutral = F 0

export %inline
TFD_CLOEXEC : Flags
TFD_CLOEXEC = F ep_tfd_cloexec

||| Sets the file descriptor to non-blocking: Reading from
||| an `TimerFD` via `readTimer` will usually block the calling thread
||| unless the file descriptor's timer has already expired at least
||| once.
|||
||| With this flag being set, `readTimer` will never block but will return
||| `Left EAGAIN` in case of a still running timer.
export %inline
TFD_NONBLOCK : Flags
TFD_NONBLOCK = F ep_tfd_nonblock

||| A timer file descriptor that can be monitored via `epoll`.
public export
record TimerFD where
  constructor TFD
  file : Bits32

||| Creates a new `TimerFD` with the given initial value a flags set.
export %inline
timerCreate : ClockTpe -> Flags -> PrimIO TimerFD
timerCreate c (F f) w =
  let MkIORes file w := prim__timerfd_create (clockCode c) f w
   in MkIORes (TFD file) w

||| Reads the current value from a timer file descriptor, returning the
||| number of times the timer has expired since the last read.
|||
||| This will block the calling thread unless the `TFD_NONBLOCK` flag
||| was set.
export %inline
readTimer : TimerFD -> PrimIO (Either EpollErr Bits64)
readTimer (TFD f) w =
  let MkIORes v w := prim__ep_readTimer f w
   in case v of
        0 => getErr w
        n => MkIORes (Right n) w

export %inline
setTime : TimerFD -> Clock Duration -> PrimIO ()
setTime (TFD f) c =
  prim__ep_setTime f (cast $ seconds c) (cast $ nanoseconds c)

||| Closes an event file descriptor.
export %inline
closeTimer : TimerFD -> PrimIO ()
closeTimer = close . file

||| Creates and finally closes and event file descriptor.
export
withTimer :
     ClockTpe
  -> Clock Duration
  -> Flags
  -> (TimerFD -> PrimIO a)
  -> PrimIO a
withTimer ct dur fs f w =
  let MkIORes tf  w := timerCreate ct fs w
      MkIORes _   w := setTime tf dur w
      MkIORes res w := f tf w
      MkIORes _   w := closeTimer tf w
   in MkIORes res w

--------------------------------------------------------------------------------
-- Syntax
--------------------------------------------------------------------------------

||| The zero duration.
export %inline
zero : Clock Duration
zero = makeDuration 0 0

||| Creates a duration of `n` seconds
export
(.s) : (n : Nat) -> Clock Duration
n.s = makeDuration (cast n) 0

||| Creates a duration of `n` nanoseconds
export
(.ns) : (n : Nat) -> Clock Duration
n.ns = makeDuration 0 (cast n)

||| Creates a duration of `n` microseconds
export
(.us) : (n : Nat) -> Clock Duration
n.us = (n * 1_000).ns

||| Creates a duration of `n` milliseconds
export
(.ms) : (n : Nat) -> Clock Duration
n.ms = (n * 1_000_000).ns
