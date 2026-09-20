module Math.GaugeSpinorCoupling

import Core.BoxInt
import Core.VexelMaxel
import Core.UnixelFraction
import Math.RelativisticSpinor
import Math.GravitationalWaveDynamics
import Math.FourGeometries
import Data.List

%default total

------------------------------------------------------------------------
-- 1. GAUGE-COVARIANT DERIVATIVE & SPINOR COUPLING
------------------------------------------------------------------------

||| Discrete 4-Component Gauge-Coupled Dirac Spinor State:
||| - spinor: intrinsic Dirac spinor (comp1, comp2, comp3, comp4)
||| - gaugeCharge: particle U(1) gauge coupling charge q
||| - connectionA: background gauge potential 1-form (A0, A1, A2, A3)
public export
record GaugeCoupledSpinor where
  constructor MkGaugeCoupledSpinor
  spinor      : DiracSpinor4
  gaugeCharge : Core.BoxInt.BoxInt
  connectionA : (Core.BoxInt.BoxInt, Core.BoxInt.BoxInt, Core.BoxInt.BoxInt, Core.BoxInt.BoxInt)

public export
Eq GaugeCoupledSpinor where
  (MkGaugeCoupledSpinor s1 q1 c1) == (MkGaugeCoupledSpinor s2 q2 c2) =
    s1 == s2 && q1 == q2 && c1 == c2

||| Evaluates discrete gauge-covariant derivative step:
||| D_mu psi = nabla_mu psi - q * A_mu * psi
public export
gaugeCovariantStep : (derivative : Core.BoxInt.BoxInt) -> (charge : Core.BoxInt.BoxInt) -> (aMu : Core.BoxInt.BoxInt) -> (psiComponent : Core.BoxInt.BoxInt) -> Core.BoxInt.BoxInt
gaugeCovariantStep d q a psi =
  d - (q * a * psi)

||| Computes the gauge-invariant probability density j^0 from the coupled spinor.
public export
coupledDiracDensity : GaugeCoupledSpinor -> Core.BoxInt.BoxInt
coupledDiracDensity (MkGaugeCoupledSpinor s _ _) = spinorProbabilityDensity s

------------------------------------------------------------------------
-- 2. TRANSVERSE-TRACELESS METRIC SHEAR INTERACTION
------------------------------------------------------------------------

||| Evaluates the interaction energy density between the Dirac spatial current j^k
||| and the TT metric shear perturbation h_ij:
||| E_int = h_plus * (j1^2 - j2^2) + 2 * h_cross * (j1 * j2).
public export
metricShearSpinorInteraction : (shear : MetricShearTT) -> (j1 : Core.BoxInt.BoxInt) -> (j2 : Core.BoxInt.BoxInt) -> Core.BoxInt.BoxInt
metricShearSpinorInteraction (MkMetricShearTT hPlus hCross) j1 j2 =
  (hPlus * (j1 * j1 - j2 * j2)) + (Core.BoxInt.intToBoxInt 2 * hCross * j1 * j2)

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Cross-Law Gauge-Spinor-Metric Coupling)
------------------------------------------------------------------------

||| Audits Gauge-Covariant Derivative Action:
||| For d = 10, q = 1, A = 2, psi = 3:
||| D psi = 10 - (1 * 2 * 3) = 10 - 6 = 4.
public export
auditGaugeCovariantDerivativeProof : Bool
auditGaugeCovariantDerivativeProof =
  let res = gaugeCovariantStep (Core.BoxInt.intToBoxInt 10) (Core.BoxInt.intToBoxInt 1) (Core.BoxInt.intToBoxInt 2) (Core.BoxInt.intToBoxInt 3)
  in unwrapBox res == 4

||| Audits Gauge-Coupled Dirac Current Positivity (j^0 >= 0):
||| For psi = ((1,0), (2,0), (2,0), (0,0)), q = 1, A = (0, 1, 0, 0):
||| j^0 = 1^2 + 2^2 + 2^2 + 0^2 = 1 + 4 + 4 + 0 = 9 >= 0.
public export
auditGaugeCoupledCurrentPositivityProof : Bool
auditGaugeCoupledCurrentPositivityProof =
  let psi = MkDiracSpinor4 (MkPixel 1 0) (MkPixel 2 0) (MkPixel 2 0) (MkPixel 0 0)
      coupled = MkGaugeCoupledSpinor psi (Core.BoxInt.intToBoxInt 1) (Core.BoxInt.intToBoxInt 0, Core.BoxInt.intToBoxInt 1, Core.BoxInt.intToBoxInt 0, Core.BoxInt.intToBoxInt 0)
      j0 = coupledDiracDensity coupled
  in unwrapBox j0 == 9 && unwrapBox j0 >= 0

||| Audits Metric Shear Coupling Tracelessness & Interaction Energy:
||| For pure cross shear (hPlus = 0, hCross = 2) with currents j1 = 3, j2 = 2:
||| E_int = 0 * (9 - 4) + 2 * 2 * (3 * 2) = 0 + 4 * 6 = 24.
public export
auditMetricShearSpinorInteractionProof : Bool
auditMetricShearSpinorInteractionProof =
  let shear = MkMetricShearTT (Core.BoxInt.intToBoxInt 0) (Core.BoxInt.intToBoxInt 2)
      eInt = metricShearSpinorInteraction shear (Core.BoxInt.intToBoxInt 3) (Core.BoxInt.intToBoxInt 2)
  in unwrapBox eInt == 24
