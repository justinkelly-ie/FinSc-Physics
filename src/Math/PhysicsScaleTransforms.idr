module Math.PhysicsScaleTransforms

import Core.ScaleTransform
import Core.BoxInt
import Core.Category.Adjunction
import Math.ActionPrinciple
import Math.FourGeometries

%default total

||| ScaleTransform instance: Maps a 2D physical coordinate (Coord2D) to its spatial quadrance (BoxInt)
public export
ScaleTransform Coord2D Core.BoxInt.BoxInt where
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
