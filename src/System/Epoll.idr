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
eagain : Int32

public export
data EpollErr : Type where
  EAGAIN : EpollErr

%runElab derive "EpollErr" [Show,Eq,Finite]

export
Interpolation EpollErr where interpolate = show

export
errCode : EpollErr -> Int32
errCode EAGAIN = eagain

--------------------------------------------------------------------------------
-- Operations
--------------------------------------------------------------------------------

export %foreign "C:ep_epoll_ctl_add,epoll-idris"
epoll_ctl_add : Int32

export %foreign "C:ep_epoll_ctl_mod,epoll-idris"
epoll_ctl_mod : Int32

export %foreign "C:ep_epoll_ctl_del,epoll-idris"
epoll_ctl_del : Int32

public export
data EpollCtl = Add | Mod | Del

%runElab derive "EpollCtl" [Show,Eq,Finite]

export
Interpolation EpollCtl where interpolate = show

export
ctlCode : EpollCtl -> Int32
ctlCode Add = epoll_ctl_add
ctlCode Mod = epoll_ctl_mod
ctlCode Del = epoll_ctl_del

--------------------------------------------------------------------------------
-- Event
--------------------------------------------------------------------------------

export %foreign "C:ep_epollin,epoll-idris"
epollin : Int32

export %foreign "C:ep_epollout,epoll-idris"
epollout : Int32

export %foreign "C:ep_epollrdhup,epoll-idris"
epollrdhup : Int32

export %foreign "C:ep_epollpri,epoll-idris"
epollpri : Int32

export %foreign "C:ep_epollerr,epoll-idris"
epollerr : Int32

export %foreign "C:ep_epollhup,epoll-idris"
epollhup : Int32

export
record Event where
  constructor E
  value : Int32

%runElab derive "Event" [Show,Eq,Ord]

export %inline
eventCode : Event -> Int32
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
