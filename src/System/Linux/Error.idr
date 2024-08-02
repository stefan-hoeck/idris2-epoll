module System.Linux.Error

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

export %foreign "C:ep_einval,epoll-idris"
einval : Bits32

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

%foreign  "C:ep_errno,epoll-idris"
prim__errno : PrimIO Bits32

public export
data EpollErr : Type where
  EAGAIN : EpollErr
  EBADF  : EpollErr
  EEXIST : EpollErr
  EINVAL : EpollErr
  ELOOP  : EpollErr
  ENOENT : EpollErr
  ENOMEM : EpollErr
  ENOSPC : EpollErr
  EPERM  : EpollErr

%runElab derive "EpollErr" [Show,Eq,Finite]

export
Interpolation EpollErr where interpolate = show

export
errCode : EpollErr -> Bits32
errCode EAGAIN = eagain
errCode EBADF  = ebadf
errCode EEXIST = eexist
errCode EINVAL = einval
errCode ELOOP  = eloop
errCode ENOENT = enoent
errCode ENOMEM = enomem
errCode ENOSPC = enospc
errCode EPERM  = eperm

export
fromCode : Bits32 -> EpollErr
fromCode x =
  if      x == eagain then EAGAIN
  else if x == ebadf  then EBADF
  else if x == eexist then EEXIST
  else if x == eloop  then ELOOP
  else if x == enoent then ENOENT
  else if x == enomem then ENOMEM
  else if x == enospc then ENOSPC
  else if x == eperm  then EPERM
  else EINVAL

export
getErr : PrimIO (Either EpollErr a)
getErr w =
  let MkIORes v w := prim__errno w
   in MkIORes (Left $ fromCode v) w
