module Main

import Data.Finite
import System.Epoll

%default total

printErr : EpollErr -> IO ()
printErr e = putStrLn "\{e} (code: \{show $ code e})"

main : IO ()
main = do
  traverse_ printErr values
