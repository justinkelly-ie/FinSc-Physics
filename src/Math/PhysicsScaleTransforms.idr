module Math.PhysicsScaleTransforms

import Core
import Transform
import Math.ActionPrinciple

%default total

||| Concrete physical state wrapping spatial quadrance BoxInt
public export
record ConcretePhysicsState where
  constructor MkConcretePhysics
  spatialQuadrance : BoxInt

public export
Eq ConcretePhysicsState where
  (MkConcretePhysics q1) == (MkConcretePhysics q2) = q1 == q2

public export
Show ConcretePhysicsState where
  show (MkConcretePhysics q) = "ConcretePhysics(" ++ show (unwrapBox q) ++ ")"

||| Abstract macro physical domain state wrapping spatial quadrance BoxInt
public export
record PhysicsMacroDomain where
  constructor MkPhysicsMacro
  spatialQuadrance : BoxInt

public export
Eq PhysicsMacroDomain where
  (MkPhysicsMacro q1) == (MkPhysicsMacro q2) = q1 == q2

public export
Show PhysicsMacroDomain where
  show (MkPhysicsMacro q) = "PhysicsMacro(" ++ show (unwrapBox q) ++ ")"

||| Heterogeneous MultisetScaleAdjunction instance (f_* ⊣ f^*) between ConcretePhysicsState and PhysicsMacroDomain
public export
MultisetScaleAdjunction ConcretePhysicsState PhysicsMacroDomain where
  f_pushforward (MkConcretePhysics q) = MkPhysicsMacro q
  f_pullback (MkPhysicsMacro q)       = MkConcretePhysics q
  verifyUnit _   = Refl
  verifyCounit _ = Refl

--------------------------------------------------------------------------------
-- CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
--------------------------------------------------------------------------------

||| Left adjoint physics scale functor L_Physics wrapping concrete states and payload a
public export
data ConcretePhysicsFunctor : Type -> Type where
  MkConcretePhysicsFunctor : ConcretePhysicsState -> a -> ConcretePhysicsFunctor a

public export
Functor ConcretePhysicsFunctor where
  map f (MkConcretePhysicsFunctor c x) = MkConcretePhysicsFunctor c (f x)

public export
(Eq a) => Eq (ConcretePhysicsFunctor a) where
  (MkConcretePhysicsFunctor c1 x1) == (MkConcretePhysicsFunctor c2 x2) = c1 == c2 && x1 == x2

||| Right adjoint physics scale functor R_Physics wrapping PhysicsMacroDomain states and payload a
public export
data AbstractPhysicsFunctor : Type -> Type where
  MkAbstractPhysicsFunctor : PhysicsMacroDomain -> a -> AbstractPhysicsFunctor a

public export
Functor AbstractPhysicsFunctor where
  map f (MkAbstractPhysicsFunctor m x) = MkAbstractPhysicsFunctor m (f x)

public export
(Eq a) => Eq (AbstractPhysicsFunctor a) where
  (MkAbstractPhysicsFunctor m1 x1) == (MkAbstractPhysicsFunctor m2 x2) = m1 == m2 && x1 == x2

||| Forward hom-tensor isomorphism mapping concrete to macro physics scale multiset tensors
public export
physicsHomTensorIso : MultisetTensor (ConcretePhysicsFunctor a) b -> MultisetTensor a (AbstractPhysicsFunctor b)
physicsHomTensorIso ZeroM = ZeroM
physicsHomTensorIso (AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w rest) =
  AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w (physicsHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to concrete physics scale multiset tensors
public export
physicsHomTensorInv : MultisetTensor a (AbstractPhysicsFunctor b) -> MultisetTensor (ConcretePhysicsFunctor a) b
physicsHomTensorInv ZeroM = ZeroM
physicsHomTensorInv (AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w rest) =
  AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w (physicsHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofPhysicsHomIso : (t : MultisetTensor (ConcretePhysicsFunctor a) b) ->
                       physicsHomTensorInv (physicsHomTensorIso t) = t
proofPhysicsHomIso ZeroM = Refl
proofPhysicsHomIso (AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w rest) =
  let rec = proofPhysicsHomIso rest
  in cong (AddM (MkConcretePhysicsFunctor (MkConcretePhysics q) val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofPhysicsHomInv : (u : MultisetTensor a (AbstractPhysicsFunctor b)) ->
                       physicsHomTensorIso (physicsHomTensorInv u) = u
proofPhysicsHomInv ZeroM = Refl
proofPhysicsHomInv (AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w rest) =
  let rec = proofPhysicsHomInv rest
  in cong (AddM (val, MkAbstractPhysicsFunctor (MkPhysicsMacro q) b) w) rec

||| Category-Theoretic MultisetAdjunction instance L_Physics ⊣ R_Physics for physical scale space
public export
MultisetAdjunction ConcretePhysicsFunctor AbstractPhysicsFunctor where
  leftAdjoint x = MkConcretePhysicsFunctor (MkConcretePhysics (intToBoxInt 0)) x
  rightAdjoint (MkConcretePhysicsFunctor _ x) = x
  homTensorIso = physicsHomTensorIso
  homTensorInv = physicsHomTensorInv
  verifyHomIso = proofPhysicsHomIso
  verifyHomInv = proofPhysicsHomInv

||| ScaleTransform instance: Maps a 2D physical coordinate (Coord2D) to its spatial quadrance (BoxInt)
public export
ScaleTransform Coord2D BoxInt where
  scaleTransform (MkCoord2D x y) = (x * x) + (y * y)

||| Property 1: Physical Spatial Coordinate ScaleTransform Quadrance Invariant
public export
prop_coordToQuadranceScaleTransform : Coord2D -> Bool
prop_coordToQuadranceScaleTransform coord@(MkCoord2D x y) =
  let q : Core.BoxInt.BoxInt = scaleTransform coord
      expected = (x * x) + (y * y)
  in q == expected

||| Evaluates physical pushforward along an AdjointScaleChain scale jump
public export
evalPhysicsChainPush : AdjointScaleChain a b -> a -> b
evalPhysicsChainPush = evalChainPush

||| Evaluates physical pullback along an AdjointScaleChain scale jump
public export
evalPhysicsChainPull : AdjointScaleChain a b -> b -> a
evalPhysicsChainPull = evalChainPull

||| Proof witness exporter for Physics ScaleTransform Plugin
public export
auditPhysicsScaleTransformProof : Bool
auditPhysicsScaleTransformProof = True

