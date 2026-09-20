module Math.RenormalizationInformationFlow

import Core.BoxInt
import Core.Multiset
import Core.VexelMaxel
import Core.UnixelFraction
import Math.FourGeometries
import Math.TopologicalChernNumber
import Data.List

%default total

------------------------------------------------------------------------
-- 1. DISCRETE CALLAN-SYMANZIK BETA FUNCTION & RG FLOW
------------------------------------------------------------------------

||| Discrete Callan-Symanzik beta function evaluating step-change in effective coupling:
||| beta(g) = Delta g_k = - (drag_k * g) / (1 + drag_k)
public export
discreteBetaStep : (coupling : UnixelFraction) -> (dragNat : Nat) -> UnixelFraction
discreteBetaStep (MkUnixelFraction (MkBoxInt numVal) (MkUnixel denVal)) drag =
  let dragInt = natToInteger drag
      newNum = - (numVal * dragInt)
      newDen = denVal * (1 + drag)
  in MkUnixelFraction (MkBoxInt newNum) (MkUnixel (if newDen == 0 then 1 else newDen))

------------------------------------------------------------------------
-- 2. DISCRETE FISHER INFORMATION METRIC ON PROBABILITY SIMPLICES
--    I_F(P, Q) = sum_k (P_k - Q_k)^2 / P_k
------------------------------------------------------------------------

||| Evaluates discrete Fisher information quadrance between two 1-particle state weights:
||| I_F = (w1 - w2)^2 / w1 (as a UnixelFraction).
public export
discreteFisherQuadrance : (w1 : Nat) -> (w2 : Nat) -> UnixelFraction
discreteFisherQuadrance w1 w2 =
  let diff = (natToInteger w1) - (natToInteger w2)
      sqDiff = diff * diff
      den = if w1 == 0 then 1 else w1
  in MkUnixelFraction (Core.BoxInt.intToBoxInt sqDiff) (MkUnixel den)

------------------------------------------------------------------------
-- 3. TOPOLOGICAL RG FIXED POINT COARSE-GRAINING
------------------------------------------------------------------------

||| Coarse-graining decimation operator on 2D Berry curvature grid:
||| Aggregates 2x2 fine plaquettes into 1 coarse plaquette while preserving total First Chern Number.
public export
decimateBerryCurvature : (finePlaquettes : List Core.BoxInt.BoxInt) -> Core.BoxInt.BoxInt
decimateBerryCurvature = foldl (+) (Core.BoxInt.intToBoxInt 0)

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Multi-Scale Renormalization & Information Geometry)
------------------------------------------------------------------------

||| Audits Discrete Beta Function Running:
||| Proves beta(1/1, 3) = -(3) / 4 = -3/4.
public export
auditDiscreteBetaFlowProof : Bool
auditDiscreteBetaFlowProof =
  case discreteBetaStep (MkUnixelFraction (Core.BoxInt.intToBoxInt 1) (MkUnixel 1)) 3 of
    MkUnixelFraction bNum (MkUnixel bDen) =>
      (bNum == Core.BoxInt.intToBoxInt (-3)) && natEq bDen 4

||| Audits Discrete Fisher Information Metric Positivity:
||| Proves I_F(w1=10, w2=6) = (10 - 6)^2 / 10 = 16/10 >= 0, and I_F(w, w) == 0.
public export
auditDiscreteFisherMetricProof : Bool
auditDiscreteFisherMetricProof =
  case (discreteFisherQuadrance 10 6, discreteFisherQuadrance 10 10) of
    (MkUnixelFraction f1Num (MkUnixel f1Den), MkUnixelFraction f0Num (MkUnixel f0Den)) =>
      (f1Num == Core.BoxInt.intToBoxInt 16) && natEq f1Den 10 &&
      (f0Num == Core.BoxInt.intToBoxInt 0) && natEq f0Den 10

||| Audits Scale-Invariance of Topological First Chern Number under RG Decimation:
||| Proves that a 4-cell fine Berry grid with fluxes [1, 2, -1, 1] (sum = 3)
||| coarse-grains to single macrocell with invariant topological charge C_1 = 3.
public export
auditTopologicalRGFixedPointProof : Bool
auditTopologicalRGFixedPointProof =
  let fineGrid = [Core.BoxInt.intToBoxInt 1, Core.BoxInt.intToBoxInt 2, Core.BoxInt.intToBoxInt (-1), Core.BoxInt.intToBoxInt 1]
      cFine = foldl (+) (Core.BoxInt.intToBoxInt 0) fineGrid
      cMacro = decimateBerryCurvature fineGrid
  in cFine == cMacro && unwrapBox cMacro == 3
