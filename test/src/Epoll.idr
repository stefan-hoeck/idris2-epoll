module Epoll

import EventFD
import Hedgehog
import System.Linux.Epoll
import System.Linux.EventFD

%default total

private infixl 1 >>>, ?>>, >>?

(>>>) : EpollRes -> EpollRes -> EpollRes
(>>>) (Err x) y = Err x
(>>>) _       y = y

(?>>) : Either EpollErr a -> EpollRes -> EpollRes
(?>>) (Left err) y = Err err
(?>>) _          y = y

(>>?) : EpollRes -> Either EpollErr a -> EpollRes
(>>?) y (Left err) = Err err
(>>?) y _          = y

parameters (efd : EpollFD)

  withFile : EpollFile a => PrimIO a -> (a -> PrimIO b) -> b
  withFile mkFile f =
    runPrim $ \w =>
      let MkIORes file w := mkFile w
          MkIORes vb   w := f file w
          MkIORes _    w := close (descriptor file) w
       in MkIORes vb w

  addDel : EpollFile a => PrimIO a -> Either EpollErr ()
  addDel mkFile =
    withFile mkFile $ \file,w =>
      let MkIORes res1 w := epollAdd efd file EPOLLIN neutral w
          MkIORes res2 w := epollDel efd file w
       in MkIORes (res1 >> res2) w

  delOnly : EpollFile a => PrimIO a -> Either EpollErr ()
  delOnly mkFile = withFile mkFile $ epollDel efd

  addTwice : EpollFile a => PrimIO a -> Either EpollErr ()
  addTwice mkFile =
    withFile mkFile $ \file,w =>
      let MkIORes res1 w := epollAdd efd file EPOLLIN neutral w
          MkIORes res2 w := epollAdd efd file EPOLLOUT neutral w
       in MkIORes res2 w

  testEpoll :
       {auto epf : EpollFile a}
    -> PrimIO a
    -> Events
    -> Epoll.Flags
    -> (timeout : Int32)
    -> EpollRes
  testEpoll mkFile evs fs timeout =
    withFile mkFile $ \file,w =>
      let MkIORes res1 w := epollAdd efd file evs fs w
          MkIORes res2 w := epollWait efd timeout w
          MkIORes res3 w := epollDel efd file w
       in MkIORes (res1 ?>> res2 >>? res3)  w

  testEpollIn : EpollFile a => PrimIO a -> (timeout : Int32) -> EpollRes
  testEpollIn mkFile timeout = testEpoll mkFile EPOLLIN neutral timeout

  testEpollInET : EpollFile a => PrimIO a -> (timeout : Int32) -> EpollRes
  testEpollInET mkFile timeout = testEpoll mkFile EPOLLIN EPOLLET timeout

--------------------------------------------------------------------------------
-- Core Functionality
--------------------------------------------------------------------------------

  prop_addDel : Property
  prop_addDel =
    property $ do
      n <- forAll (bits64 $ linear 0 0xffff)
      addDel (eventfd n neutral) === Right ()

  prop_delOnly : Property
  prop_delOnly =
    property $ do
      n <- forAll (bits64 $ linear 0 0xffff)
      delOnly (eventfd n neutral) === Left ENOENT

  prop_addTwice : Property
  prop_addTwice =
    property $ do
      n <- forAll (bits64 $ linear 0 0xffff)
      addTwice (eventfd n neutral) === Left EEXIST

--------------------------------------------------------------------------------
-- Polling Event Files
--------------------------------------------------------------------------------

  prop_emptyEv : Property
  prop_emptyEv =
    property $ do
      n <- forAll (int32 $ linear 0 10)
      testEpollIn (eventfd 0 neutral) n === NoEv

  export
  props : Group
  props =
    MkGroup "Epoll"
      [ ("prop_addDel", prop_addDel)
      , ("prop_delOnly", prop_delOnly)
      , ("prop_addTwice", prop_addTwice)
      , ("prop_emptyEv", prop_emptyEv)
      ]
