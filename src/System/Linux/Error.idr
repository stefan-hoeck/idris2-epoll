module System.Linux.Error

import Data.Maybe
import Data.List
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

export %foreign "C:ep_eagain,epoll-idris"
eagain : Bits32

export %foreign "C:ep_ebadf,epoll-idris"
ebadf : Bits32

export %foreign "C:ep_eexist,epoll-idris"
eexist : Bits32

export %foreign "C:ep_efault,epoll-idris"
efault : Bits32

export %foreign "C:ep_einval,epoll-idris"
einval : Bits32

export %foreign "C:ep_eisdir,epoll-idris"
eisdir : Bits32

export %foreign "C:ep_eio,epoll-idris"
eio : Bits32

export %foreign "C:ep_eloop,epoll-idris"
eloop : Bits32

export %foreign "C:ep_enoent,epoll-idris"
enoent : Bits32

export %foreign "C:ep_enomem,epoll-idris"
enomem : Bits32

export %foreign "C:ep_enospc,epoll-idris"
enospc : Bits32

export %foreign "C:ep_eperm,epoll-idris"
eperm : Bits32

export %foreign "C:ep_ewouldblock,epoll-idris"
ewouldblock : Bits32

export %foreign "C:ep_eintr,epoll-idris"
eintr : Bits32

export %foreign "C:ep_edestaddrreq,epoll-idris"
edestaddrreq : Bits32

export %foreign "C:ep_efbig,epoll-idris"
efbig : Bits32

export %foreign "C:ep_edquot,epoll-idris"
edquot : Bits32

export %foreign "C:ep_epipe,epoll-idris"
epipe : Bits32

%foreign  "C:ep_errno,epoll-idris"
prim__errno : PrimIO Bits32

public export
data EpollErr : Type where
  EAGAIN       : EpollErr
  EBADF        : EpollErr
  EDESTADDRREQ : EpollErr
  EDQUOT       : EpollErr
  EEXIST       : EpollErr
  EFAULT       : EpollErr
  EFBIG        : EpollErr
  EINTR        : EpollErr
  EINVAL       : EpollErr
  EIO          : EpollErr
  EISDIR       : EpollErr
  ELOOP        : EpollErr
  ENOENT       : EpollErr
  ENOMEM       : EpollErr
  ENOSPC       : EpollErr
  EPERM        : EpollErr
  EPIPE        : EpollErr

%runElab derive "EpollErr" [Show,Eq,Finite]

export
Interpolation EpollErr where interpolate = show

export
errCode : EpollErr -> Bits32
errCode EAGAIN       = eagain
errCode EBADF        = ebadf
errCode EDQUOT       = edquot
errCode EDESTADDRREQ = edestaddrreq
errCode EEXIST       = eexist
errCode EFAULT       = efault
errCode EFBIG        = efbig
errCode EISDIR       = eisdir
errCode EINTR        = eintr
errCode EINVAL       = einval
errCode EIO          = eio
errCode ELOOP        = eloop
errCode ENOENT       = enoent
errCode ENOMEM       = enomem
errCode ENOSPC       = enospc
errCode EPERM        = eperm
errCode EPIPE        = epipe

pairs : List (Bits32,EpollErr)
pairs = (ewouldblock, EAGAIN) :: map (\x => (errCode x, x)) values

export
fromCode : Bits32 -> EpollErr
fromCode x = fromMaybe EINVAL $ lookup x pairs

export
getErr : PrimIO (Either EpollErr a)
getErr w =
  let MkIORes v w := prim__errno w
   in MkIORes (Left $ fromCode v) w

export
checkErr : Int32 -> PrimIO (Either EpollErr ())
checkErr n w = if n < 0 then getErr w else MkIORes (Right ()) w

export
checkSize : Int32 -> PrimIO (Either EpollErr Nat)
checkSize n w = if n < 0 then getErr w else MkIORes (Right $ cast n) w
