module System.Linux.File

import Derive.Finite
import Derive.Prelude
import Data.Buffer
import Data.Buffer.Core
import System.Linux.Error

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- FFI
--------------------------------------------------------------------------------

%foreign "C:ep_read,epoll-idris"
prim__read : Bits32 -> (buf : Buffer) -> (offset,max : Bits32) -> PrimIO Int32

%foreign "C:ep_write,epoll-idris"
prim__write : Bits32 -> (buf : Buffer) -> (offset,max : Bits32) -> PrimIO Int32

%foreign "C:close,epoll-idris"
prim__close : Bits32 -> PrimIO ()

%foreign "C:ep_set_nonblocking,epoll-idris"
prim__setNonBlocking : Bits32 -> PrimIO ()

--------------------------------------------------------------------------------
-- API
--------------------------------------------------------------------------------

public export
interface FileDesc  a where
  fileDesc : a -> Bits32

export %inline
FileDesc Bits32 where fileDesc x = x

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
toReadRes (Left EAGAIN)      _   = Again
toReadRes (Left x)           _   = Err x
toReadRes (Right 0)          _   = EOF
toReadRes (Right n)          buf = Bytes n (unsafeMakeBuffer buf)

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
  write fi buf offset max w =
    let MkIORes res w :=prim__write (fileDesc fi) buf (cast offset) (cast max) w
     in checkSize res w

  ||| A higher-level alternative to `read`: It allocates a new buffer of the
  ||| given size and returns it wrapped in a `ReadRes`.
  |||
  ||| Use `read` if you want to avoid allocating a new buffer for every
  ||| data package.
  export
  readBytes : a -> (max : Nat) -> PrimIO ReadRes
  readBytes fi max w =
    let MkIORes buf w := prim__newBuf (cast max) w
        MkIORes res w := read fi buf 0 max w
     in MkIORes (toReadRes res buf) w

  ||| Changes a file descriptor's mode to `O_NONBLOCK`.
  |||
  ||| This will not block when trying to read from a stream such as a pipe, socket, or
  ||| stdin. Instead, `readBytes` will return `Again` in case no data is currently
  ||| available. Use this in combination with `EPOLLET` to keep reading from a data
  ||| source until it is temporarily exhausted.
  export
  setNonBlocking : a -> PrimIO ()
  setNonBlocking = prim__setNonBlocking . fileDesc

public export
data StdFile : Type where
  StdIn  : StdFile
  StdOut : StdFile
  StdErr : StdFile

%runElab derive "StdFile" [Show,Eq,Ord,Finite]

export %inline
FileDesc StdFile where fileDesc = cast . conIndexStdFile
