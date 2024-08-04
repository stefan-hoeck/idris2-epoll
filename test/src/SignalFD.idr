module SignalFD

import Data.Finite
import Data.Vect
import EventFD
import Hedgehog
import System.Linux.Error
import System.Linux.File
import System.Linux.SignalFD

%default total

signals : Gen Signal
signals = element $ fromList values

justRead : Signal -> Flags -> Either EpollErr Bits32
justRead s fs = runPrim $ withSignal [s] fs readSignal

readBlockingRes : Signal -> Either EpollErr Bits32
readBlockingRes s =
  runPrim $ withSignal [s] neutral $ \fs,w =>
    let MkIORes _ w := raise s w
     in readSignal fs w

prop_readBlocking : Property
prop_readBlocking =
  property $ do
    s <- forAll signals
    readBlockingRes s === Right (signalCode s)

readNonblockingRes : Signal -> Either EpollErr Bits32
readNonblockingRes s = justRead s SFD_NONBLOCK

readNonblockingAfterraise : Signal -> Either EpollErr Bits32
readNonblockingAfterraise s =
  runPrim $ withSignal [s] SFD_NONBLOCK $ \fs,w =>
    let MkIORes _ w := raise s w
     in readSignal fs w

prop_readNonblocking : Property
prop_readNonblocking =
  property $ do
    s <- forAll signals
    readNonblockingRes s === Left EAGAIN

prop_readNonblockingAfterraise : Property
prop_readNonblockingAfterraise =
  property $ do
    s <- forAll signals
    readNonblockingAfterraise s === Right (signalCode s)

export
props : Group
props =
  MkGroup "SignalFD"
    [ ("prop_readBlocking", prop_readBlocking)
    , ("prop_readNonblocking", prop_readNonblocking)
    , ("prop_readNonblockingAfterraise", prop_readNonblockingAfterraise)
    ]
