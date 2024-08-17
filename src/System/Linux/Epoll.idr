module System.Linux.Epoll

import Data.Bits
import Data.Nat
import Derive.Finite
import Derive.Prelude
import public System.Linux.Error
import public System.Linux.File
import System.FFI

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Events
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

||| Type of events epoll can wait for.
|||
||| For every file descriptor observed by epoll a
||| combination of events can be watched for. Events
||| can be combined via `(<+>)`.
export
record Events where
  constructor E
  value : Bits32

%runElab derive "Events" [Show,Eq,Ord]

export %inline
eventCode : Events -> Bits32
eventCode = value

export %inline
Semigroup Events where
  E x <+> E y = E (x .|. y)

||| Event for observing if a file is ready for input, that is,
||| `read` invoked with that file will not block.
export %inline
EPOLLIN : Events
EPOLLIN = E epollin

||| Event for observing if a file is ready for output, that is,
||| `write` invoked with that file will not block.
export %inline
EPOLLOUT : Events
EPOLLOUT = E epollout

export %inline
EPOLLRDHUP : Events
EPOLLRDHUP = E epollrdhup

export %inline
EPOLLPRI : Events
EPOLLPRI = E epollpri

export %inline
EPOLLERR : Events
EPOLLERR = E epollerr

export %inline
EPOLLHUP : Events
EPOLLHUP = E epollhup

--------------------------------------------------------------------------------
-- Flags
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
record Flags where
  constructor F
  value : Bits32

%runElab derive "Flags" [Show,Eq,Ord]

export %inline
flagCode : Flags -> Bits32
flagCode = value

export %inline
Semigroup Flags where
  F x <+> F y = F (x .|. y)

export %inline
Monoid Flags where
  neutral = F 0

export %inline
EPOLLET : Flags
EPOLLET = F epollet

export %inline
EPOLLONESHOT : Flags
EPOLLONESHOT = F epolloneshot

export %inline
EPOLLWAKEUP : Flags
EPOLLWAKEUP = F epollwakeup

export %inline
EPOLLEXCLUSIVE : Flags
EPOLLEXCLUSIVE = F epollexclusive

--------------------------------------------------------------------------------
-- epoll utilities
--------------------------------------------------------------------------------

%foreign  "C:close,epoll-idris"
prim__close : Bits32 -> PrimIO ()

%foreign  "C:ep_epoll_add,epoll-idris"
prim__epoll_add : Bits32 -> Bits32 -> Bits32 -> Bits32 -> PrimIO Int32

%foreign  "C:ep_epoll_mod,epoll-idris"
prim__epoll_mod : Bits32 -> Bits32 -> Bits32 -> Bits32 -> PrimIO Int32

%foreign  "C:ep_epoll_del,epoll-idris"
prim__epoll_del : Bits32 -> Bits32 -> PrimIO Int32

%foreign  "C__collect_safe:epoll_wait,epoll-idris"
prim__epoll_wait : Bits32 -> AnyPtr -> Bits32 -> Int32 -> PrimIO Int32

%foreign  "C:epoll_create1,epoll-idris"
prim__epoll_create1 : Bits32 -> PrimIO Int32

%foreign  "C:ep_allocEvent,epoll-idris"
prim__ep_allocEvent : PrimIO AnyPtr

%foreign  "C:ep_getFile,epoll-idris"
prim__ep_getFile : AnyPtr -> PrimIO Bits32

%foreign  "C:ep_getEvents,epoll-idris"
prim__ep_getEvents : AnyPtr -> PrimIO Bits32

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
  file  : Bits32
  event : AnyPtr

export
Show EpollFD where show = show . file

parameters {0 a : Type}
           {auto ef : FileDesc a}

  ||| Adds, modifies, or removes interest in the given file descriptor
  ||| at an epoll instance.
  export %inline
  epollAdd : EpollFD -> a -> Events -> Flags -> PrimIO (Either EpollErr ())
  epollAdd (EFD ef _) f (E e) (F fl) w =
    let MkIORes n w := prim__epoll_add ef fl (fileDesc f) e w
     in checkErr n w

  ||| Adds, modifies, or removes interest in the given file descriptor
  ||| at an epoll instance.
  export %inline
  epollMod : EpollFD -> a -> Events -> Flags -> PrimIO (Either EpollErr ())
  epollMod (EFD ef _) f (E e) (F fl) w =
    let MkIORes n w := prim__epoll_mod ef fl (fileDesc f) e w
     in checkErr n w

  ||| Adds, modifies, or removes interest in the given file descriptor
  ||| at an epoll instance.
  export %inline
  epollDel : EpollFD -> a -> PrimIO (Either EpollErr ())
  epollDel (EFD ef _) f w =
    let MkIORes n w := prim__epoll_del ef (fileDesc f) w
     in checkErr n w

||| Creates a new epoll file descriptor that can be used to monitor
||| other file descriptors for readiness.
export
epollCreate : IO (Either EpollErr EpollFD)
epollCreate =
  fromPrim $ \w =>
    let MkIORes res w := prim__epoll_create1 0 w
     in case res of
          -1 => getErr w
          n  =>
            let MkIORes ptr w := prim__ep_allocEvent w
             in MkIORes (Right $ EFD (cast n) ptr) w

public export
data EpollRes : Type where
  NoEv : EpollRes
  Ev   : (file : Bits32) -> (ev : Events) -> EpollRes
  Err  : EpollErr -> EpollRes

%runElab derive "EpollRes" [Show,Eq]

fromLeft : Either EpollErr Void -> EpollRes
fromLeft (Left e) = Err e
fromLeft (Right v) impossible

export %inline
epollClose : EpollFD -> PrimIO ()
epollClose e = close e.file

export
epollWait : EpollFD -> (timeout : Int32) -> PrimIO EpollRes
epollWait (EFD f p) timeout w=
  let MkIORes n w := prim__epoll_wait f p 1 timeout w
   in case n of
        0 => MkIORes NoEv w
        1 =>
          let MkIORes f w := prim__ep_getFile p w
              MkIORes e w := prim__ep_getEvents p w
           in MkIORes (Ev f $ E e) w
        _ =>
          let MkIORes e w := getErr w
           in MkIORes (fromLeft e) w

export %inline
epollWaitTimeout : EpollFD -> (ms : Bits32) -> PrimIO EpollRes
epollWaitTimeout fd = epollWait fd . cast

export %inline
epollNoWait : EpollFD -> PrimIO EpollRes
epollNoWait fd = epollWait fd 0
