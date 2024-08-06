module System.Linux.File

import Data.Buffer
import Data.Buffer.Core
import System.Linux.Error

%default total

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "scheme:(lambda (n) (make-bytevector n 0))"
         "javascript:lambda:s=>new Uint8Array(s)"
prim__newBuf : Bits32 -> PrimIO Buffer

%foreign "C:ep_read,epoll-idris"
prim__read : Bits32 -> (buf : Buffer) -> (offset,max : Bits32) -> PrimIO Int32

%foreign "C:write,epoll-idris"
prim__write : Bits32 -> Buffer -> Bits32 -> PrimIO Int32

%foreign "C:close,epoll-idris"
prim__close : Bits32 -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

public export
interface FileDesc  a where
  fileDesc : a -> Bits32

||| Result of reading from a file descriptor
public export
data ReadRes : Type where
  ||| End of file has been reached
  EOF   : ReadRes

  ||| This occurs when reading from a file descriptor in non-blocking mode
  ||| and there is currently no data ready.
  Again : ReadRes

  ||| The given numbers have been read into an immutable buffer
  Bytes : (n : Nat) -> IBuffer n -> ReadRes

  ||| An error occured
  Err   : EpollErr -> ReadRes

toReadRes : Either EpollErr Nat -> Buffer -> ReadRes
toReadRes (Left EAGAIN) _   = Again
toReadRes (Left x)      _   = Err x
toReadRes (Right 0)     _   = EOF
toReadRes (Right n)     buf = Bytes n (unsafeMakeBuffer buf)

parameters {0 a : Type}
           {auto fd : FileDesc a}

  ||| Close a file descriptor.
  export %inline
  close : a -> PrimIO ()
  close = prim__close . fileDesc

  ||| Low-level reading of at most `max` bytes from a file into a buffer
  ||| starting at buffer offset `offset`.
  |||
  ||| See `readBytes` for a higher-level function that allocates a new buffer and
  ||| correctly interprets the result.
  export
  read : a -> Buffer -> (offset,max : Nat) -> PrimIO (Either EpollErr Nat)
  read fi buf offset max w =
    let MkIORes res w :=prim__read (fileDesc fi) buf (cast offset) (cast max) w
     in checkSize res w

  export
  write : a -> Buffer -> (offset,max : Nat) -> PrimIO (Either EpollErr Nat)
  -- write = prim__read . fileDesc

  export
  readBytes : a -> (max : Nat) -> PrimIO ReadRes
  readBytes fi max w =
    let MkIORes buf w := prim__newBuf (cast max) w
        MkIORes res w := read fi buf 0 max w
     in MkIORes (toReadRes res buf) w
