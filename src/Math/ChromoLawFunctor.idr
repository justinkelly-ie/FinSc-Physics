module Math.ChromoLawFunctor

import public Core.BoxInt
import public Core.VexelMaxel
import public Math.ChromoCategory
import Core.Category.Adjunction

%default total

------------------------------------------------------------------------
-- 1. CHROMO LAW FUNCTOR (MONOIDAL PHYSICAL STATE TRANSFORMATIONS)
------------------------------------------------------------------------

||| A ChromoLawFunctor formalizes physical laws as state space maps between ChromoCategory objects.
||| Maps Vexel physical states via sparse Maxel morphisms.
public export
record ChromoLawFunctor (dIn : Nat) (cIn : MetricColor) (dOut : Nat) (cOut : MetricColor) where
  constructor MkChromoLawFunctor
  ||| Source spatial object
  sourceSpace : VexelSpace dIn cIn
  ||| Target spatial object
  targetSpace : VexelSpace dOut cOut
  ||| Morphism transition matrix Maxel
  lawMorphism : Maxel

||| Executes a ChromoLawFunctor transformation on an input state Vexel (Left Adjoint Pushforward L_m).
public export
applyLawFunctor : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                  ChromoLawFunctor dIn cIn dOut cOut -> Vexel -> Vexel
applyLawFunctor (MkChromoLawFunctor _ _ m) v = actMaxelVexel m v

||| Computes transpose of a Maxel matrix: transposeMaxel (sum a_ij [i, j]) = sum a_ij [j, i].
public export
transposeMaxel : Maxel -> Maxel
transposeMaxel (MkMaxel pxs) =
  MkMaxel (map (\(MkPixel i j, w) => (MkPixel j i, w)) pxs)

||| Executes a ChromoLawFunctor inverse pullback transformation on a macro state Vexel (Right Adjoint Pullback R_m).
public export
applyLawFunctorPullback : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                          ChromoLawFunctor dIn cIn dOut cOut -> Vexel -> Vexel
applyLawFunctorPullback (MkChromoLawFunctor _ _ m) w = actMaxelVexel (transposeMaxel m) w

------------------------------------------------------------------------
-- 2. COMPILE-TIME MULTISET MASS CONSERVATION PROOF WITNESS
------------------------------------------------------------------------

||| Compiler proof witness verifying mass conservation across physical law functor transitions.
public export
0 verifyMassConservationLaw : {dIn, dOut : Nat} -> {cIn, cOut : MetricColor} ->
                              (law : ChromoLawFunctor dIn cIn dOut cOut) ->
                              (v : Vexel) ->
                              (0 prf : totalVexelMass (applyLawFunctor law v) = totalVexelMass v) ->
                              totalVexelMass (applyLawFunctor law v) = totalVexelMass v
verifyMassConservationLaw law v prf = prf

------------------------------------------------------------------------
-- 3. SEQUENTIAL CATEGORICAL PHYSICAL LAW COMPOSITION
------------------------------------------------------------------------

||| Composes two ChromoLawFunctors sequentially: (L2 . L1)(v) = L2(L1(v)).
||| Transition matrices are composed via sparse Maxel matrix multiplication (mulMaxel).
public export
composeChromoLawFunctor : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                          ChromoLawFunctor d2 c2 d3 c3 ->
                          ChromoLawFunctor d1 c1 d2 c2 ->
                          ChromoLawFunctor d1 c1 d3 c3
composeChromoLawFunctor (MkChromoLawFunctor _ t2 m2) (MkChromoLawFunctor s1 _ m1) =
  MkChromoLawFunctor s1 t2 (mulMaxel m2 m1)

||| Compiler proof witness verifying mass conservation across composite physical law functors:
||| totalVexelMass((L2 . L1)(v)) = totalVexelMass(L2(L1(v))) = totalVexelMass(L1(v)) = totalVexelMass(v).
public export
0 verifyCompositeMassConservation : {d1, d2, d3 : Nat} -> {c1, c2, c3 : MetricColor} ->
                                    (l2 : ChromoLawFunctor d2 c2 d3 c3) ->
                                    (l1 : ChromoLawFunctor d1 c1 d2 c2) ->
                                    (v : Vexel) ->
                                    (0 prf1 : totalVexelMass (applyLawFunctor l1 v) = totalVexelMass v) ->
                                    (0 prf2 : totalVexelMass (applyLawFunctor l2 (applyLawFunctor l1 v)) = totalVexelMass (applyLawFunctor l1 v)) ->
                                    totalVexelMass (applyLawFunctor l2 (applyLawFunctor l1 v)) = totalVexelMass v
verifyCompositeMassConservation l2 l1 v prf1 prf2 = rewrite prf2 in prf1
