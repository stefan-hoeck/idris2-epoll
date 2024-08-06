module System.Linux.File

import Data.Buffer

%default total

%foreign "read,epoll-idris"
prim__read : Bits32 -> (buf : Buffer) -> Bits32 -> PrimIO Int32

%foreign "C:write,epoll-idris"
prim__write : Bits32 -> Buffer -> Bits32 -> PrimIO Int32

%foreign "C:close,epoll-idris"
prim__close : Bits32 -> PrimIO ()

export %inline
close : (file : Bits32) -> PrimIO ()
close = prim__close

public export
interface EpollFile a where
  descriptor : a -> Bits32
