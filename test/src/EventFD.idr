module EventFD

import System.Linux.Error
import System.Linux.EventFD
import System.Linux.File
import Hedgehog

%default total

export
runPrim : PrimIO a -> a
runPrim f = let MkIORes v w := f %MkWorld in v

writeRead : Bits64 -> Flags -> Either EpollErr Bits64
writeRead i fs =
  runPrim $ withEv 0 fs $ \ev,w =>
    let MkIORes _ w := writeEv ev i w
     in readEv ev w

prop_initRead : Property
prop_initRead =
  property $ do
    v <- forAll (bits64 $ linear 1 0xffff)
    runPrim (withEv v neutral readEv) === Right v

prop_initReadSemaphore : Property
prop_initReadSemaphore =
  property $ do
    v <- forAll (bits64 $ linear 1 0xffff)
    runPrim (withEv v EFD_SEMAPHORE readEv) === Right 1

prop_writeRead : Property
prop_writeRead =
  property $ do
    v <- forAll (bits64 $ linear 1 0xffff)
    writeRead v neutral === Right v

prop_writeReadSemaphore : Property
prop_writeReadSemaphore =
  property $ do
    v <- forAll (bits64 $ linear 1 0xffff)
    writeRead v EFD_SEMAPHORE === Right 1

prop_read0NonBlocking : Property
prop_read0NonBlocking =
  property1 $
    runPrim (withEv 0 EFD_NONBLOCK readEv) === Left EAGAIN

export
props : Group
props =
  MkGroup "EventFD"
    [ ("prop_initRead", prop_initRead)
    , ("prop_initReadSemaphore", prop_initReadSemaphore)
    , ("prop_writeRead", prop_writeRead)
    , ("prop_writeReadSemaphore", prop_writeReadSemaphore)
    , ("prop_read0NonBlocking", prop_read0NonBlocking)
    ]

