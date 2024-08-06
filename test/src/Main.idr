module Main

import Data.Finite
import Epoll
import EventFD
import Hedgehog
import SignalFD
import System
import System.Linux.Epoll
import System.Linux.SignalFD
import TimerFD

%default total

printItm : Show a => (a -> Bits32) -> a -> IO ()
printItm code e = putStrLn "  \{show e} (code: \{show $ code e})"

main : IO ()
main = do
  putStrLn "Errors:"
  traverse_ (printItm errCode) values

  putStrLn "\nEvents:"
  traverse_ (printItm eventCode)
    [EPOLLIN,EPOLLOUT,EPOLLRDHUP,EPOLLPRI,EPOLLERR,EPOLLHUP]

  putStrLn "\nFlags:"
  traverse_ (printItm flagCode)
    [EPOLLET,EPOLLONESHOT,EPOLLWAKEUP,EPOLLEXCLUSIVE]

  fromPrim (blockSignals values)

  Right efd <- epollCreate | Left err => die "Epoll error: \{show err}"

  test
    [ EventFD.props
    , TimerFD.props
    , SignalFD.props
    , Epoll.props efd
    ]
