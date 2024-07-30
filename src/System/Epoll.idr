module System.Epoll

import Derive.Finite
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
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
code : EpollErr -> Int32
code EAGAIN = eagain
