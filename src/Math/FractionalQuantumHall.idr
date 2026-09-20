module Math.FractionalQuantumHall

import Core.BoxInt
import Core.VexelMaxel
import Core.UnixelFraction
import Core.Multiset
import Core

%default total

------------------------------------------------------------------------
-- 1. FRACTIONAL QUANTUM HALL FLUID & ANYONIC BRAIDING
------------------------------------------------------------------------

||| Represents a Fractional Quantum Hall Laughlin / Jain state with filling factor ν = p / q:
public export
record LaughlinState where
  constructor MkLaughlinState
  fillingNumerator : Nat
  fillingDenominator : Nat

public export
Eq LaughlinState where
  (MkLaughlinState p1 q1) == (MkLaughlinState p2 q2) =
    p1 == p2 && q1 == q2

||| Computes the fractional charge of a Laughlin quasiparticle excitation e* = (p/q) * e:
public export
fractionalQuasiparticleCharge : LaughlinState -> UnixelFraction
fractionalQuasiparticleCharge (MkLaughlinState p q) =
  MkUnixelFraction (natToBoxInt p) (MkUnixel (if natEq q 0 then 1 else q))

||| Computes the anyonic statistical exchange angle denominator:
||| Exchanging two anyons yields topological phase θ = π / q.
||| Full 2π cycle corresponds to 2 * q fractional step subdivisions.
public export
anyonicExchangePeriod : LaughlinState -> Nat
anyonicExchangePeriod (MkLaughlinState _ q) = 2 * q

||| Computes the Quantized Fractional Hall Conductance:
||| σ_{xy} = (p / q) * (e^2 / h).
public export
fractionalHallConductance : LaughlinState -> UnixelFraction
fractionalHallConductance = fractionalQuasiparticleCharge

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 14: Fractional Quantum Hall & Anyonic Statistics)
------------------------------------------------------------------------

||| Audits Quasiparticle Fractional Charge Quantization:
||| For Laughlin state ν = 1/3, quasiparticle excitation has fractional charge e* = 1/3 * e.
public export
auditFractionalChargeQuantizationProof : Bool
auditFractionalChargeQuantizationProof =
  case fractionalQuasiparticleCharge (MkLaughlinState 1 3) of
    MkUnixelFraction n (MkUnixel d) =>
      (n == intToBoxInt 1) && natEq d 3

||| Audits Anyonic Topological Braiding Phase:
||| For Laughlin state ν = 1/3, exchanging two quasiparticles incurs phase θ = π / 3,
||| with topological cycle period = 2 * 3 = 6.
public export
auditAnyonicBraidingPhaseProof : Bool
auditAnyonicBraidingPhaseProof =
  let state13 = MkLaughlinState 1 3
      period = anyonicExchangePeriod state13
  in natEq period 6

||| Audits Fractional Hall Conductance:
||| Proves σ_{xy}(1/3) = 1/3 and σ_{xy}(2/5) = 2/5 on exact UnixelFractions.
public export
auditFractionalHallConductanceProof : Bool
auditFractionalHallConductanceProof =
  case (fractionalHallConductance (MkLaughlinState 1 3), fractionalHallConductance (MkLaughlinState 2 5)) of
    (MkUnixelFraction n1 (MkUnixel d1), MkUnixelFraction n2 (MkUnixel d2)) =>
      (n1 == intToBoxInt 1) && natEq d1 3 &&
      (n2 == intToBoxInt 2) && natEq d2 5

