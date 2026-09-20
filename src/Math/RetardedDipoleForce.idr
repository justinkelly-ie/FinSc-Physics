module Math.RetardedDipoleForce

import Core.BoxInt
import Core.Multiset
import Core.VexelMaxel
import Core.UnixelFraction
import Math.FourGeometries
import Math.VacuumDispersion
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 26: DISCRETE CASIMIR-POLDER & LONDON DISPERSION FORCES
------------------------------------------------------------------------

||| Computes the short-range non-retarded London dispersion potential:
||| V_London(Q) = - C6 / Q^3 (in exact UnixelFraction units)
public export
discreteLondonPotential : (c6 : Core.BoxInt.BoxInt) -> (quadranceQ : Nat) -> UnixelFraction
discreteLondonPotential c6 q =
  let c6Val = unwrapBox c6
      denom = if q == 0 then 1 else q * q * q
  in MkUnixelFraction (Core.BoxInt.intToBoxInt (- c6Val)) (MkUnixel denom)

||| Computes the long-range retarded Casimir-Polder potential:
||| V_CP(Q) = - C7 / Q^4 (in exact UnixelFraction units)
public export
discreteCasimirPolderPotential : (c7 : Core.BoxInt.BoxInt) -> (quadranceQ : Nat) -> UnixelFraction
discreteCasimirPolderPotential c7 q =
  let c7Val = unwrapBox c7
      denom = if q == 0 then 1 else q * q * q * q
  in MkUnixelFraction (Core.BoxInt.intToBoxInt (- c7Val)) (MkUnixel denom)

||| Validates that both London and Casimir-Polder forces are strictly attractive (negative potential):
public export
isAttractiveDispersion : UnixelFraction -> Bool
isAttractiveDispersion (MkUnixelFraction n _) = boxNegative n

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 26: Discrete Casimir-Polder Force)
------------------------------------------------------------------------

||| Audits Law 26 across intermolecular dispersion regimes:
||| 1. London dispersion at quadrance Q = 2 with C6 = 8:
|||    V_London = -8 / 2^3 = -8 / 8 = -1.
||| 2. Casimir-Polder retarded potential at quadrance Q = 3 with C7 = 81:
|||    V_CP = -81 / 3^4 = -81 / 81 = -1.
||| 3. Both forces are strictly attractive: V < 0.
public export
auditRetardedDipoleForceProof : Bool
auditRetardedDipoleForceProof =
  case (discreteLondonPotential (Core.BoxInt.intToBoxInt 8) 2, discreteCasimirPolderPotential (Core.BoxInt.intToBoxInt 81) 3) of
    (MkUnixelFraction n1 (MkUnixel d1), MkUnixelFraction n2 (MkUnixel d2)) =>
      (n1 == Core.BoxInt.intToBoxInt (-8)) && natEq d1 8 &&
      (n2 == Core.BoxInt.intToBoxInt (-81)) && natEq d2 81 &&
      boxNegative n1 && boxNegative n2
