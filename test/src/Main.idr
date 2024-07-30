module Main

import Data.Finite
import System.Epoll

%default total

printItm : Interpolation a => (a -> Int32) -> a -> IO ()
printItm code e = putStrLn "  \{e} (code: \{show $ code e})"

main : IO ()
main = do
  putStrLn "Errors:"
  traverse_ (printItm errCode) values

  putStrLn "\nOperations:"
  traverse_ (printItm ctlCode) values
