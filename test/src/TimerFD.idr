module TimerFD

import Debug.Trace
import EventFD
import Hedgehog
import System.Linux.Error
import System.Linux.File
import System.Linux.TimerFD

%default total

justRead : Clock Duration -> Flags -> Either EpollErr Bits64
justRead dur fs = runPrim $ withTimer MONOTONIC dur fs readTimer

readBlockingRes : Clock Duration -> Either EpollErr Bits64
readBlockingRes dur = justRead dur neutral

readNonblockingRes : Clock Duration -> Either EpollErr Bits64
readNonblockingRes dur = justRead dur TFD_NONBLOCK

prop_readBlocking : Property
prop_readBlocking =
  property $ do
    n <- forAll (nat $ linear 1 1000)
    readBlockingRes n.us === Right 1

prop_readNonblocking : Property
prop_readNonblocking =
  property $ do
    n <- forAll (nat $ linear 1 1000)
    readNonblockingRes n.ms === Left EAGAIN

export
props : Group
props =
  MkGroup "TimerFD"
    [("prop_readBlocking", prop_readBlocking)
    ,("prop_readNonblocking", prop_readNonblocking)
    ]
