module Error

import Data.Finite
import Data.Vect
import System.Linux.Error
import Hedgehog

%default total

prop_roundTrip : Property
prop_roundTrip =
  property1 $ for_ values $ \v => v === fromCode (errCode v)

export
props : Group
props =
  MkGroup "Error"
    [ ("prop_roundTrip", prop_roundTrip) ]
