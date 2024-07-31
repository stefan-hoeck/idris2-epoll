module System.Epoll

import Data.Bits
import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Errors
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

export %foreign "C:ep_epoll_ctl_add,epoll-idris"
epoll_ctl_add : Bits32

export %foreign "C:ep_epoll_ctl_mod,epoll-idris"
epoll_ctl_mod : Bits32

export %foreign "C:ep_epoll_ctl_del,epoll-idris"
epoll_ctl_del : Bits32

public export
data EpollOp = Add | Mod | Del

%runElab derive "EpollOp" [Show,Eq,Finite]

export
Interpolation EpollOp where interpolate = show

export
opCode : EpollOp -> Bits32
opCode Add = epoll_ctl_add
opCode Mod = epoll_ctl_mod
opCode Del = epoll_ctl_del

--------------------------------------------------------------------------------
-- Event
--------------------------------------------------------------------------------

export %foreign "C:ep_epollin,epoll-idris"
epollin : Bits32

export %foreign "C:ep_epollout,epoll-idris"
epollout : Bits32

export %foreign "C:ep_epollrdhup,epoll-idris"
epollrdhup : Bits32

export %foreign "C:ep_epollpri,epoll-idris"
epollpri : Bits32

export %foreign "C:ep_epollerr,epoll-idris"
epollerr : Bits32

export %foreign "C:ep_epollhup,epoll-idris"
epollhup : Bits32

export
record Event where
  constructor E
  value : Bits32

%runElab derive "Event" [Show,Eq,Ord]

export %inline
eventCode : Event -> Bits32
eventCode = value

export %inline
Semigroup Event where
  E x <+> E y = E (x .|. y)

export %inline
EPOLLIN : Event
EPOLLIN = E epollin

export %inline
EPOLLOUT : Event
EPOLLOUT = E epollout

export %inline
EPOLLRDHUP : Event
EPOLLRDHUP = E epollrdhup

export %inline
EPOLLPRI : Event
EPOLLPRI = E epollpri

export %inline
EPOLLERR : Event
EPOLLERR = E epollerr

export %inline
EPOLLHUP : Event
EPOLLHUP = E epollhup

--------------------------------------------------------------------------------
-- Flag
--------------------------------------------------------------------------------

export %foreign "C:ep_epollet,epoll-idris"
epollet : Bits32

export %foreign "C:ep_epolloneshot,epoll-idris"
epolloneshot : Bits32

export %foreign "C:ep_epollwakeup,epoll-idris"
epollwakeup : Bits32

export %foreign "C:ep_epollexclusive,epoll-idris"
epollexclusive : Bits32

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
EPOLLET : Flag
EPOLLET = F epollet

export %inline
EPOLLONESHOT : Flag
EPOLLONESHOT = F epolloneshot

export %inline
EPOLLWAKEUP : Flag
EPOLLWAKEUP = F epollwakeup

export %inline
EPOLLEXCLUSIVE : Flag
EPOLLEXCLUSIVE = F epollexclusive

--------------------------------------------------------------------------------
-- epoll utilities
--------------------------------------------------------------------------------

%foreign  "C:close,epoll-idris"
prim__close : Bits32 -> PrimIO ()

%foreign  "C:epoll_ctl,epoll-idris"
prim__epoll_ctl : Bits32 -> Bits32 -> Bits32 -> AnyPtr -> PrimIO Bits32

%foreign  "C:epoll_wait,epoll-idris"
prim__epoll_wait : Bits32 -> AnyPtr -> Bits32 -> Int32 -> PrimIO Bits32

%foreign  "C:epoll_create1,epoll-idris"
prim__epoll_create1 : Bits32 -> PrimIO Int32

%foreign  "C:epoll_errno,epoll-idris"
prim__errno : PrimIO Bits32

public export
record FileDesc where
  constructor FD
  file : Bits32

export
record EpollEvent where
  constructor EE
  ptr : AnyPtr

export
record EpollFD where
  constructor EFD
  fileDesc : Bits32

export %inline
epollCtl : EpollFD -> EpollOp -> FileDesc -> EpollEvent -> IO Bits32
epollCtl (EFD ef) o (FD f) (EE p) = fromPrim $ prim__epoll_ctl ef (opCode o) f p

export %inline
epollCreate : IO (Either EpollErr EpollFD)
epollCreate =
  fromPrim $ \w =>
    let MkIORes res w := prim__epoll_create1 0 w
     in case res of
          -1 => let MkIORes c w := prim__errno w
                 in MkIORes (Left $ fromCode c) w
          n  => MkIORes (Right $ EFD $ cast n) w
