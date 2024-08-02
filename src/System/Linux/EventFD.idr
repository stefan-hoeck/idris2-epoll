module System.Linux.EventFD

import Data.Bits
import Derive.Prelude
import System.Linux.Error

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

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

export
record Flag where
  constructor F
  value : Bits32

%runElab derive "Flag" [Show,Eq,Ord]

export %inline
flagCode : Flag -> Bits32
flagCode = value

export %inline
Semigroup Flag where
  F x <+> F y = F (x .|. y)

export %inline
EFD_CLOEXEC : Flag
EFD_CLOEXEC = F ep_efd_cloexec

export %inline
EFD_NONBLOCK : Flag
EFD_NONBLOCK = F ep_efd_nonblock

export %inline
EFD_SEMAPHORE : Flag
EFD_SEMAPHORE = F ep_efd_semaphore

public export
record EventFD where
  constructor EFD
  file : Bits32

export %inline
writeEv : EventFD -> Bits64 -> IO ()
writeEv (EFD f) v = fromPrim $ prim__ep_writeEventFile f v

export %inline
readEv : EventFD -> IO (Either EpollErr Bits64)
readEv (EFD f) =
  fromPrim $ \w =>
    let MkIORes v w := prim__ep_readEventFile f w
     in case v of
          0 => getErr w
          n => MkIORes (Right n) w

