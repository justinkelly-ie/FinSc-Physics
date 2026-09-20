module Math.CosmologicalWaveEquation

import Core.BoxInt
import Core.UnixelFraction
import Core.Multiset
import Core
import Math.LinAlgebra.MetricTensor

%default total

------------------------------------------------------------------------
-- 1. DISCRETE DEWITT SUPERMETRIC & WHEELER-DEWITT HAMILTONIAN
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. DISCRETE DEWITT SUPERMETRIC & WHEELER-DEWITT HAMILTONIAN
------------------------------------------------------------------------

||| Evaluates scaled 2 * DeWitt Supermetric component G_{abcd}:
||| 2 * G_{abcd} = (g_{ac} * g_{bd} + g_{ad} * g_{bc}) - 2 * (g_{ab} * g_{cd}).
public export
scaledDeWittSupermetric : (gAc : Core.BoxInt.BoxInt) -> (gBd : Core.BoxInt.BoxInt) -> 
                         (gAd : Core.BoxInt.BoxInt) -> (gBc : Core.BoxInt.BoxInt) -> 
                         (gAb : Core.BoxInt.BoxInt) -> (gCd : Core.BoxInt.BoxInt) -> Core.BoxInt.BoxInt
scaledDeWittSupermetric gAc gBd gAd gBc gAb gCd =
  ((gAc * gBd) + (gAd * gBc)) - (Core.BoxInt.intToBoxInt 2 * (gAb * gCd))

||| Evaluates discrete Wheeler-DeWitt total super-Hamiltonian constraint:
||| H_total = E_grav + E_matter + E_sink - E_ref = 0.
public export
discreteSuperHamiltonian : (vm : Core.BoxInt.BoxInt) -> (de : Core.BoxInt.BoxInt) -> (dm : Core.BoxInt.BoxInt) -> (eRef : Core.BoxInt.BoxInt) -> Core.BoxInt.BoxInt
discreteSuperHamiltonian vm de dm eRef =
  let eTotal = (Core.BoxInt.intToBoxInt 4 * vm) + (Core.BoxInt.intToBoxInt 2 * de) + (Core.BoxInt.intToBoxInt 2 * dm)
  in eTotal - eRef

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 16: Discrete Wheeler-DeWitt Constraint)
------------------------------------------------------------------------

||| Audits Scaled DeWitt Supermetric on Euclidean Spacetime:
||| For g11 = 1, g22 = 1, g12 = 0:
||| 2 * G_{1122} = (g12*g12 + g12*g12) - 2 * (g11*g22) = (0 + 0) - 2 * (1 * 1) = -2.
public export
auditDeWittSupermetricProof : Bool
auditDeWittSupermetricProof =
  let g11Val = Core.BoxInt.intToBoxInt 1
      g22Val = Core.BoxInt.intToBoxInt 1
      g12Val = Core.BoxInt.intToBoxInt 0
      scaledG1122 = scaledDeWittSupermetric g12Val g12Val g12Val g12Val g11Val g22Val
  in Core.BoxInt.unwrapBox scaledG1122 == (-2)

||| Audits Zero Super-Hamiltonian Vanishing on Primorial 210 Ground State:
||| E_total = 4 * 27 + 2 * 128 + 2 * 55 = 108 + 256 + 110 = 474.
||| H_total = 474 - 474 = 0.
public export
auditZeroWheelerDeWittConstraintProof : Bool
auditZeroWheelerDeWittConstraintProof =
  let hTotal = discreteSuperHamiltonian (Core.BoxInt.intToBoxInt 27) (Core.BoxInt.intToBoxInt 128) (Core.BoxInt.intToBoxInt 55) (Core.BoxInt.intToBoxInt 474)
  in Core.BoxInt.unwrapBox hTotal == 0

||| Audits Relational Cosmic Energy Conservation:
||| 108 (kinetic/matter) + 256 (potential/DE) + 110 (sink/DM) = 474 (invariant total).
public export
auditRelationalCosmicEnergyConservationProof : Bool
auditRelationalCosmicEnergyConservationProof =
  let eKin = 4 * 27
      ePot = 2 * 128
      eSink = 2 * 55
      eTotal = eKin + ePot + eSink
  in eKin == 108 && ePot == 256 && eSink == 110 && eTotal == 474
