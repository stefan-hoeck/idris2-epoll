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

export %inline
EFD_NONBLOCK : Flags
EFD_NONBLOCK = F ep_efd_nonblock

export %inline
EFD_SEMAPHORE : Flags
EFD_SEMAPHORE = F ep_efd_semaphore

public export
record EventFD where
  constructor EFD
  file : Bits32

export %inline
eventfd : (init : Bits64) -> Flags -> PrimIO EventFD
eventfd i (F f) w =
  let MkIORes file w := prim__eventfd i f w
   in MkIORes (EFD file) w

export %inline
writeEv : EventFD -> Bits64 -> PrimIO ()
writeEv (EFD f) v = prim__ep_writeEventFile f v

export %inline
readEv : EventFD -> PrimIO (Either EpollErr Bits64)
readEv (EFD f) w =
  let MkIORes v w := prim__ep_readEventFile f w
   in case v of
        0 => getErr w
        n => MkIORes (Right n) w

export %inline
closeEv : EventFD -> PrimIO ()
closeEv = close . file

export
withEv : Bits64 -> Flags -> (EventFD -> PrimIO a) -> PrimIO a
withEv i fs f w =
  let MkIORes ev  w := eventfd i fs w
      MkIORes res w := f ev w
      MkIORes _   w := closeEv ev w
   in MkIORes res w
