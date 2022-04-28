module Examples.Isomorphism

import Prelude
import Isomorphism
import Category
import Examples.Category

data Confirmation : Type where
  Yes : Confirmation
  No : Confirmation

public export
interface FunExt where
  0 funExt : {0 f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

namespace BoolConfirmationIso
  forward : Bool -> Confirmation
  forward False = No
  forward True = Yes

  backward : Confirmation -> Bool
  backward Yes = True
  backward No = False

  fInverse : FunExt => BoolConfirmationIso.forward . BoolConfirmationIso.backward = TYPE .id
  fInverse = irrelevantEq $ funExt $ \x => case x of
    Yes => Refl
    No => Refl

  gInverse : FunExt => BoolConfirmationIso.backward . BoolConfirmationIso.forward = TYPE .id
  gInverse = irrelevantEq $ funExt $ \x => case x of
    False => Refl
    True => Refl

  export
  iso : FunExt => Isomorphism TYPE Bool Confirmation
  iso = Iso
    BoolConfirmationIso.forward
    BoolConfirmationIso.backward
    BoolConfirmationIso.fInverse
    BoolConfirmationIso.gInverse


