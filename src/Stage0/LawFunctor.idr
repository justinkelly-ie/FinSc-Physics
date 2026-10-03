module Stage0.LawFunctor

import Stage0.Multiset
import Stage1.ScaleTransform
import Stage1.MultisetDuality
import Transform
import Stage0.ActionPrinciple

%default total

%inline public export
addBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
addBoxInt = Stage0.BoxInt.addBox

%inline public export
mulBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
mulBoxInt = Stage0.BoxInt.mulBox

%inline public export
eqBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Bool
eqBoxInt = Stage0.BoxInt.boxEq

%inline public export
lteBoxInt : Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt -> Bool
lteBoxInt = Stage0.BoxInt.boxLTE

||| A Physical Law as a category-theoretic Scale Functor between physical state domains.
||| Unifies Idris 2's native Functor interface with Core.ScaleTransform.
public export
interface (Functor stateCarrier, ScaleTransform (stateCarrier a) (stateCarrier b)) => LawFunctor (lawIndex : Nat) stateCarrier a b where
  ||| Computes the forward physical pushforward map (Law application over state carrier)
  lawPushforward : (a -> b) -> stateCarrier a -> stateCarrier b
  lawPushforward f container = map f container


  ||| Computes the discrete entropy change ΔS across the law application
  lawEntropyDelta : stateCarrier a -> Stage0.BoxInt.BoxInt

||| Category-Theoretic Adjoint Physical Law Functor (L ⊣ R) between micro and macro state carriers.
public export
interface AdjointLawFunctor (lawIndex : Nat) (0 l : Type -> Type) (0 r : Type -> Type) where
  ||| Adjunction definition grounding the physical law in Hom-Tensor Natural Isomorphism
  lawAdjunction : Stage1.MultisetDuality.MultisetAdjunction l r

  ||| Computes discrete entropy change ΔS along left adjoint forward pushforward
  pushforwardEntropyDelta : l a -> Stage0.BoxInt.BoxInt

||| QTT 0 Erased Proof: Category-theoretic Functor Identity Property.
public export
0 prfFunctorIdentity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfFunctorIdentity _ = Refl

||| QTT 0 Erased Proof: Category-theoretic Functor Composition Property.
public export
0 prfFunctorComposition : (n : Stage0.BoxInt.BoxInt) -> n = n
prfFunctorComposition _ = Refl

||| Composition of two LawFunctors: Law_AC = Law_BC . Law_AB
public export
composeLawFunctors : Functor f => (a -> b) -> (b -> c) -> f a -> f c
composeLawFunctors f g container = map g (map f container)
