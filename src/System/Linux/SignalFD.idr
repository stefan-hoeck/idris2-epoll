module System.Linux.SignalFD

import Data.Bits
import Derive.Finite
import Derive.Prelude
import System.FFI
import System.Linux.Error
import System.Linux.File

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

signalFFI : String -> String
signalFFI fn = "C:" ++ fn ++ ", libidris2_support, idris_signal.h"

%foreign "C:ep_sfd_cloexec,epoll-idris"
ep_sfd_cloexec : Bits32

%foreign "C:ep_sfd_nonblock,epoll-idris"
ep_sfd_nonblock : Bits32

%foreign "C:ep_allocSignalset,epoll-idris"
prim__allocSignalset : PrimIO AnyPtr

%foreign "C:signalfd,epoll-idris"
prim__signalfd : Int32 -> AnyPtr -> Bits32 -> PrimIO Bits32

%foreign "C:ep_readSignal,epoll-idris"
prim__ep_readSignal : Bits32 -> PrimIO Bits32

%foreign "C:raise,epoll-idris"
prim__raise : Bits32 -> PrimIO ()

%foreign "C:ep_sigblock,epoll-idris"
prim__sigblock : AnyPtr -> PrimIO ()

%foreign "C:sigaddset,epoll-idris"
prim__sigaddset : AnyPtr -> Bits32 -> PrimIO ()

%foreign signalFFI "sighup"
prim__sighup : Bits32

%foreign signalFFI "sigint"
prim__sigint : Bits32

%foreign signalFFI "sigabrt"
prim__sigabrt : Bits32

%foreign signalFFI "sigquit"
prim__sigquit : Bits32

%foreign signalFFI "sigill"
prim__sigill : Bits32

%foreign signalFFI "sigsegv"
prim__sigsegv : Bits32

%foreign signalFFI "sigtrap"
prim__sigtrap : Bits32

%foreign signalFFI "sigfpe"
prim__sigfpe : Bits32

%foreign signalFFI "sigusr1"
prim__sigusr1 : Bits32

%foreign signalFFI "sigusr2"
prim__sigusr2 : Bits32

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

public export
data Signal : Type where
  ||| Hangup (i.e. controlling terminal closed)
  SigHUP : Signal
  ||| Quit
  SigQUIT : Signal
  ||| Trap (as used by debuggers)
  SigTRAP : Signal
  SigUser1 : Signal
  SigUser2 : Signal
  ||| Interrupt (e.g. ctrl+c pressed)
  SigINT : Signal
  ||| Abnormal termination
  SigABRT : Signal
  ||| Ill-formed instruction
  SigILL : Signal
  ||| Segmentation fault
  SigSEGV : Signal
  ||| Floating-point error
  SigFPE : Signal

%runElab derive "Signal" [Show,Eq,Ord,Finite]

export
signalCode : Signal -> Bits32
signalCode SigHUP   = prim__sighup
signalCode SigQUIT  = prim__sigquit
signalCode SigTRAP  = prim__sigtrap
signalCode SigUser1 = prim__sigusr1
signalCode SigUser2 = prim__sigusr2
signalCode SigINT   = prim__sigint
signalCode SigABRT  = prim__sigabrt
signalCode SigILL   = prim__sigill
signalCode SigSEGV  = prim__sigsegv
signalCode SigFPE   = prim__sigfpe

||| Flags describing the behavior of an signal file descriptor.
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
SFD_CLOEXEC : Flags
SFD_CLOEXEC = F ep_sfd_cloexec

||| Sets the file descriptor to non-blocking: Reading from
||| a `SignalFD` via `readSignal` will usually block the calling thread
||| unless the file descriptor's signal has been caught.
|||
||| With this flag being set, `readSignal` will never block but will return
||| `Left EAGAIN` in case of a still running signal.
export %inline
SFD_NONBLOCK : Flags
SFD_NONBLOCK = F ep_sfd_nonblock

||| A signal file descriptor that can be monitored via `epoll`.
public export
record SignalFD where
  constructor SFD
  file : Bits32

export %inline
FileDesc SignalFD where fileDesc = file

addSignals : List Signal -> AnyPtr -> PrimIO ()
addSignals []        ptr w = MkIORes () w
addSignals (x :: xs) ptr w =
  let MkIORes _ w := prim__sigaddset ptr (signalCode x) w
   in addSignals xs ptr w

||| Creates a new `SignalFD`, observing the given signals
||| with the given flags set.
|||
||| Note: Make sure to block the given list of signals to prevent their
|||       default behavior. The easiest way to do so is by using
|||       `blockSignals` at the beginning of your application.
export
signalCreate : List Signal -> Flags -> PrimIO SignalFD
signalCreate ss (F f) w =
 let MkIORes ptr  w := prim__allocSignalset w
     MkIORes _    w := addSignals ss ptr w
     MkIORes file w := prim__signalfd (-1) ptr f w
     MkIORes _    w := toPrim (free ptr) w
  in MkIORes (SFD file) w

||| Block default handling for the given list of signals.
export
blockSignals : List Signal -> PrimIO ()
blockSignals ss w =
 let MkIORes ptr  w := prim__allocSignalset w
     MkIORes _    w := addSignals ss ptr w
     MkIORes _    w := prim__sigblock ptr w
  in toPrim (free ptr) w

||| Reads the next caught signal from a signal file descriptor.
export
readSignal : SignalFD -> PrimIO (Either EpollErr Bits32)
readSignal (SFD f) w =
  let MkIORes v w := prim__ep_readSignal f w
   in case v of
        0 => getErr w
        n => MkIORes (Right n) w

||| Creates and finally closes and event file descriptor.
export
withSignal : List Signal -> Flags -> (SignalFD -> PrimIO a) -> PrimIO a
withSignal ss fs f w =
  let MkIORes tf  w := signalCreate ss fs w
      MkIORes res w := f tf w
      MkIORes _   w := close tf w
   in MkIORes res w

export %inline
raise : Signal -> PrimIO ()
raise s = prim__raise (signalCode s)
