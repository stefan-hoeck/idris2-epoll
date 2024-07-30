module System.Epoll

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
