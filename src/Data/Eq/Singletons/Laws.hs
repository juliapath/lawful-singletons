module Data.Eq.Singletons.Laws where

import Prelude
import Prelude.Singletons

import Data.Constraint

import Data.Eq.Singletons
import Data.Singletons.TH

------------------------------------------------------------------------
-- ** Eq
------------------------------------------------------------------------

class SEq k => LawfulEq k where
  sEqRefl 
    :: forall (a :: k) 
     . Sing a
    -> Dict ((a == a) ~ 'True)

  sEqTrans
    :: forall (a :: k) b c
     . ((a == b) ~ 'True,
        (b == c) ~ 'True) 
    => Sing a -> Sing b -> Sing c
    -> Dict ((a == c) ~ 'True)
  default sEqTrans 
    :: forall (a :: k) b c
     . (TrivialEq k,
        (a == b) ~ 'True,
        (b == c) ~ 'True) 
    => Sing a -> Sing b -> Sing c 
    -> Dict ((a == c) ~ 'True)
  sEqTrans sa sb _ = withDict (sEqUnrefl sa sb) $ Dict

  sEqSym 
    :: forall (a :: k) b
     . Sing a -> Sing b 
    -> Dict ((a == b) ~ (b == a))
  default sEqSym 
    :: forall (a :: k) b
     . TrivialEq k
    => Sing a -> Sing b
    -> Dict ((a == b) ~ (b == a))
  sEqSym sa sb = case (sa %== sb, sb %== sa) of
    (STrue, _) -> withDict (sEqUnrefl sa sb) $ Dict
    (_, STrue) -> withDict (sEqUnrefl sb sa) $ Dict
    (SFalse, SFalse) -> Dict
  
  sEqNeg
    :: forall (a :: k) b
     . Sing a -> Sing b
    -> Dict (Not (a == b) ~ (a /= b))

type EqComps1 :: k -> Constraint
type EqComps1 a = (
    (a == a) ~ 'True,
    (a /= a) ~ 'False
  )

type EqComps2' :: k -> k -> Constraint
type EqComps2' a b = (
    (a == b) ~ (b == a),
    Not (a == b) ~ (a /= b),
    Not (a /= b) ~ (a == b)
  )

type EqComps2 :: k -> k -> Constraint
type EqComps2 a b = (
    EqComps2' a b,
    EqComps2' b a,
    EqComps1 a,
    EqComps1 b
  )

eqComps1
  :: forall {k} (a :: k)
   . (LawfulEq k, SingI a)
  => Dict (EqComps1 a)
eqComps1 =
  withDict (sEqRefl $ sing @a) $
  withDict (sEqNeg (sing @a) (sing @a)) $
  Dict 

eqComps2
  :: forall {k} (a :: k) b
   . (LawfulEq k, SingI a, SingI b)
  => Dict (EqComps2 a b)
eqComps2 =
  withDict (eqComps1 @a) $
  withDict (eqComps1 @b) $
  withDict (sEqNeg (sing @a) (sing @b)) $
  withDict (sEqNeg (sing @b) (sing @a)) $
  withDict (sEqSym (sing @a) (sing @b)) $
  case sing @a %== sing @b of
    STrue  -> Dict
    SFalse -> Dict


------------------------------------------------------------------------
-- ** TrivialEq
------------------------------------------------------------------------

class LawfulEq k => TrivialEq k where
  sEqUnrefl
    :: forall (a :: k) b 
     . ((a == b) ~ 'True) 
    => Sing a -> Sing b -> Dict (a ~ b)


------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

instance LawfulEq Bool where
  sEqRefl sa = case sa of
    STrue -> Dict
    SFalse -> Dict
  sEqNeg sa sb = case sa %== sb of
    STrue -> Dict
    SFalse -> Dict

instance TrivialEq Bool where
  sEqUnrefl STrue STrue = Dict
  sEqUnrefl SFalse SFalse = Dict
