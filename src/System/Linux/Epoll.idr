module System.Linux.Epoll

import Data.Bits
import Data.Nat
import Derive.Finite
import Derive.Prelude
import public System.Linux.Error
import System.FFI

%default total
%language ElabReflection

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

%foreign  "C:ep_allocEvents,epoll-idris"
prim__ep_allocEvent : Bits32 -> PrimIO AnyPtr

%foreign  "C:ep_setEvent,epoll-idris"
prim__ep_setEvent : AnyPtr -> Bits32 -> PrimIO ()

%foreign  "C:ep_setFile,epoll-idris"
prim__ep_setFile : AnyPtr -> Bits32 -> PrimIO ()

%foreign  "C:ep_getFile,epoll-idris"
prim__ep_getFile : AnyPtr -> PrimIO Bits32

%foreign  "C:ep_eventAt,epoll-idris"
prim__ep_eventAt : AnyPtr -> Bits32 -> PrimIO AnyPtr

public export
record FileDesc where
  constructor FD
  file : Bits32

export
record EpollEvent where
  constructor EE
  ptr : AnyPtr

export
record EpollEvents (n : Nat) where
  constructor EES
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
          -1 => getErr w
          n  => MkIORes (Right $ EFD $ cast n) w

export %inline
allocEvent : IO EpollEvent
allocEvent =
  fromPrim $ \w =>
    let MkIORes ev w := prim__ep_allocEvent 1 w
     in MkIORes (EE ev) w

export %inline
allocEvents : (n : Nat) -> IO (EpollEvents n)
allocEvents n =
  fromPrim $ \w =>
    let MkIORes ev w := prim__ep_allocEvent (cast n) w
     in MkIORes (EES ev) w

export %inline
freeEvent : EpollEvent -> IO ()
freeEvent (EE ev) = free ev

export %inline
freeEvents : EpollEvents n -> IO ()
freeEvents (EES ev) = free ev

export %inline
epollWaitTimeout :
     {n : Nat}
  -> EpollFD
  -> EpollEvents n
  -> {auto 0 prf : IsSucc n}
  -> (ms : Bits32)
  -> IO Bits32
epollWaitTimeout (EFD f) (EES p) ms =
  fromPrim $ prim__epoll_wait f p (cast n) (cast ms)

export %inline
epollNoWait :
     {n : Nat}
  -> EpollFD
  -> EpollEvents n
  -> {auto 0 prf : IsSucc n}
  -> IO Bits32
epollNoWait (EFD f) (EES p) = fromPrim $ prim__epoll_wait f p (cast n) 0
