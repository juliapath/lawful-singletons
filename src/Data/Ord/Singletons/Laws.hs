{-# language UndecidableInstances #-}
module Data.Ord.Singletons.Laws where

import Prelude
import Prelude.Singletons

import Data.Constraint

import Data.Ord.Singletons
import Data.Singletons.TH
import Data.Eq.Singletons.Laws

------------------------------------------------------------------------
-- * Ord
------------------------------------------------------------------------

singletons [d|
  flipOrdering :: Ordering -> Ordering
  flipOrdering LT = GT
  flipOrdering EQ = EQ
  flipOrdering GT = LT
  |]

class (SOrd k, LawfulEq k) => LawfulOrd k where
  sOrdTrans
    :: forall (a :: k) b c 
     . ((a <= b) ~ 'True,
        (b <= c) ~ 'True) 
    => Sing a -> Sing b -> Sing c
    -> Dict ((a <= c) ~ 'True)

  sOrdCompare
    :: forall (a :: k) b
     . Sing a -> Sing b
    -> Dict (
         FlipOrdering (Compare a b) ~ Compare b a,
         (Compare a b == 'EQ) ~ (a == b),
         (Compare a b <= 'EQ) ~ (a <= b),
         (Compare a b >= 'EQ) ~ (a >= b),
         (Compare a b == 'LT) ~ (a < b),
         (Compare a b == 'GT) ~ (a > b),
         (Compare a b <= 'EQ) ~ (Min a b == a),
         (Compare a b >= 'EQ) ~ (Max a b == a)
       )

type OrdComps2' :: k -> k -> Constraint
type OrdComps2' a b = (
    FlipOrdering (Compare a b) ~ Compare b a,
    (Compare a b == 'EQ) ~ (a == b),
    (Compare a b <= 'EQ) ~ (a <= b),
    (Compare a b >= 'EQ) ~ (a >= b),
    (Compare a b == 'LT) ~ (a <  b),
    (Compare a b == 'GT) ~ (a >  b),
    Not (a <= b) ~ (a >  b),
    (a <= b) ~ Not (a > b),
    Not (a >= b) ~ (a < b),
    (a >= b) ~ Not (a < b),
    (Min a b == a) ~ (a <= b),
    (Max a b == a) ~ (a >= b),
    (Min a b == a || Max a b == a) ~ 'True,
    (a <= b || b <= a) ~ 'True,
    (a <= b && b <= a) ~ (a == b)
  )

type OrdComps2 :: k -> k -> Constraint
type OrdComps2 a b = (
    OrdComps2' a b,
    OrdComps2' b a,
    OrdComps1 a,
    OrdComps1 b,
    EqComps2 a b
  )

type OrdComps1 :: k -> Constraint
type OrdComps1 a =
  ((a <= a) ~ 'True,
   (a >= a) ~ 'True,
   (a <  a) ~ 'False,
   (a >  a) ~ 'False,
   (Compare a a) ~ 'EQ,
   ((Min a a) == a) ~ 'True,
   ((Max a a) == a) ~ 'True,
   EqComps1 a)

ordComps1
  :: forall {k} (a :: k)
   . (LawfulOrd k, SingI a)
  => Dict (OrdComps1 a)
ordComps1 = 
  withDict (eqComps1 @a) $
  withDict (sOrdCompare (sing @a) (sing @a)) $
  case sing @a `sCompare` sing @a of
    SEQ -> Dict

ordComps2
  :: forall {k} (a :: k) b
   . (LawfulOrd k, SingI a, SingI b)
  => Dict (OrdComps2 a b)
ordComps2 =
  withDict (ordComps1 @a) $
  withDict (ordComps1 @b) $
  withDict (eqComps2 @a @b) $
  withDict (sOrdCompare (sing @a) (sing @b)) $ 
  withDict (sOrdCompare (sing @b) (sing @a)) $ 
  case (sing @a `sCompare` sing @a, 
        sing @a `sCompare` sing @b,
        sing @b `sCompare` sing @b) of
    (SEQ, SLT, SEQ) -> Dict
    (SEQ, SEQ, SEQ) -> Dict
    (SEQ, SGT, SEQ) -> Dict

ordTotal
  :: forall k (a :: k) b
    . (LawfulOrd k, SingI a, SingI b, (a <= b) ~ 'False)
  => Dict ((b <= a) ~ 'True)
ordTotal =
  withDict (ordComps2 @a @b) $ 
  case sing @a `sCompare` sing @b of
    SGT -> Dict

------------------------------------------------------------------------
-- * Bounded
------------------------------------------------------------------------

-- We define this here, instead of in Data.Singletons.Base.Enum.Laws
-- as it makes some instance declarations for LawfulOrd shorter.

class (LawfulOrd k, SBounded k) => LawfulBounded k where
  sBounded
    :: forall (a :: k)
     . Sing a
    -> Dict ((a <= MaxBound) ~ 'True, (MinBound <= a) ~ 'True)


------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

instance LawfulOrd Bool where
  sOrdTrans sa sb sc = case (sa, sb, sc) of
    (SFalse, _, _    ) -> withDict (sBounded sc) $ Dict
    (_     , _, STrue) -> withDict (sBounded sa) $ Dict

  sOrdCompare sa sb = case (sa, sb) of
    (STrue,  STrue ) -> Dict
    (STrue,  SFalse) -> Dict
    (SFalse, STrue ) -> Dict
    (SFalse, SFalse) -> Dict

instance LawfulBounded Bool where
  sBounded STrue = Dict
  sBounded SFalse = Dict