module Main

import Data.Finite
import System.Epoll

%default total

printItm : Show a => (a -> Bits32) -> a -> IO ()
printItm code e = putStrLn "  \{show e} (code: \{show $ code e})"

main : IO ()
main = do
  putStrLn "Errors:"
  traverse_ (printItm errCode) values

  putStrLn "\nOperations:"
  traverse_ (printItm ctlCode) values

  putStrLn "\nEvents:"
  traverse_ (printItm eventCode)
    [EPOLLIN,EPOLLOUT,EPOLLRDHUP,EPOLLPRI,EPOLLERR,EPOLLHUP]

  putStrLn "\nFlags:"
  traverse_ (printItm flagCode)
    [EPOLLET,EPOLLONESHOT,EPOLLWAKEUP,EPOLLEXCLUSIVE]
