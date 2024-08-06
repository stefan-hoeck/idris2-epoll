||| This provides wrappers around the `sys/eventfd.h` module: An "event"
||| file descriptort that can be monitored via `epoll` and written to
||| programmatically to wake up a dormant thread.
|||
||| The file descriptor can work in `EFD_SEMAPHORE` mode, in which case it
||| can indeed be used liked a `System.Concurrent.Semaphore` or a
||| `System.Concurrent.Condition`.
module System.Linux.EventFD

import Data.Bits
import Derive.Prelude
import System.Linux.Error
import System.Linux.File

%language ElabReflection
%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:ep_readEventFile,epoll-idris"
prim__ep_readEventFile : Bits32 -> PrimIO Bits64

%foreign "C:ep_writeEventFile,epoll-idris"
prim__ep_writeEventFile : Bits32 -> Bits64 -> PrimIO ()

%foreign "C:ep_efd_cloexec,epoll-idris"
ep_efd_cloexec : Bits32

%foreign "C:ep_efd_nonblock,epoll-idris"
ep_efd_nonblock : Bits32

%foreign "C:ep_efd_semaphore,epoll-idris"
ep_efd_semaphore : Bits32

%foreign "C:eventfd,epoll-idris"
prim__eventfd : Bits64 -> Bits32 -> PrimIO Bits32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

||| Flags describing the behavior of an event file descriptor.
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
EFD_CLOEXEC : Flags
EFD_CLOEXEC = F ep_efd_cloexec

||| Sets the file descriptor to non-blocking: Reading from
||| an `EventFD` via `readEv` will usually block the calling thread
||| unless the file descriptor's stored value is greater than zero.
|||
||| With this flag being set, `readEv` will never block but will return
||| `Left EAGAIN` in case of an empty file descriptor.
export %inline
EFD_NONBLOCK : Flags
EFD_NONBLOCK = F ep_efd_nonblock

||| Changes the file descriptor to work in "semaphore mode": Usually,
||| `readEv` will return the whole 64-bit value currently stored in the
||| file descriptor. In semaphore mode, `readEv` will always return 1
||| (unliss the file descriptor is empty) and likewise reduce the stored
||| value by 1.
export %inline
EFD_SEMAPHORE : Flags
EFD_SEMAPHORE = F ep_efd_semaphore

||| An event file descriptor that can be monitored via `epoll`
||| and programmatically written to and read from.
public export
record EventFD where
  constructor EFD
  file : Bits32

export %inline
FileDesc EventFD where fileDesc = file

||| Creates a new `EventFD` with the given initial value a flags set.
export %inline
eventfd : (init : Bits64) -> Flags -> PrimIO EventFD
eventfd i (F f) w =
  let MkIORes file w := prim__eventfd i f w
   in MkIORes (EFD file) w

||| Writes (adds) the given 64-bit value to the value currently stored
||| in the given event file descriptor.
export %inline
writeEv : EventFD -> Bits64 -> PrimIO ()
writeEv (EFD f) v = prim__ep_writeEventFile f v

||| Reads the current value from an event file descriptor, setting the
||| stored value to 0.
|||
||| If the `EFD_SEMAPHORE` flag was set when creating the file descriptor,
||| this will always return 1 in case the event file is non-empty. Likewise,
||| the value stored in the event file will be reduced by one.
export %inline
readEv : EventFD -> PrimIO (Either EpollErr Bits64)
readEv (EFD f) w =
  let MkIORes v w := prim__ep_readEventFile f w
   in case v of
        0 => getErr w
        n => MkIORes (Right n) w

||| Creates and finally closes and event file descriptor.
export
withEv : Bits64 -> Flags -> (EventFD -> PrimIO a) -> PrimIO a
withEv i fs f w =
  let MkIORes ev  w := eventfd i fs w
      MkIORes res w := f ev w
      MkIORes _   w := close ev w
   in MkIORes res w
