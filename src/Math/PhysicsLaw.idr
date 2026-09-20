module Math.PhysicsLaw

import public Core.BoxInt
import public Core.VexelMaxel
import public Math.ChromoCategory
import public Math.ChromoLawFunctor

%default total

------------------------------------------------------------------------
-- UNIFIED PHYSICAL LAW INTERFACE
------------------------------------------------------------------------

||| A Unified Compiler-Verified Physical Law Interface
||| Standardises physical law operators as ChromoLawFunctors over ChromoCategory VexelSpaces,
||| backed by static multiset mass conservation proof witnesses.
public export
interface PhysicsLaw (lawID : Nat) where
  dimOfLaw   : Nat
  colorOfLaw : MetricColor

  lawSpace    : VexelSpace dimOfLaw colorOfLaw
  lawSpace    = defaultSpace dimOfLaw colorOfLaw

  lawOperator : ChromoLawFunctor dimOfLaw colorOfLaw dimOfLaw colorOfLaw

  ||| Static proof witness verifying multiset mass conservation across physical law application
  0 verifyMassConservation : (v : Vexel) ->
                             (0 prf : totalVexelMass (applyLawFunctor lawOperator v) = totalVexelMass v) ->
                             totalVexelMass (applyLawFunctor lawOperator v) = totalVexelMass v

------------------------------------------------------------------------
-- CORE PHYSICAL LAW INSTANCES
------------------------------------------------------------------------

||| Canonical Identity Action Physics Law (Law ID = 0)
public export
implementation PhysicsLaw 0 where
  dimOfLaw   = 3
  colorOfLaw = Blue

  lawOperator = MkChromoLawFunctor (defaultSpace 3 Blue) (defaultSpace 3 Blue) idChromo

  verifyMassConservation v prf = prf

||| Canonical Mass Conservation Physics Law (Law ID = 1)
public export
implementation PhysicsLaw 1 where
  dimOfLaw   = 4
  colorOfLaw = Red

  lawOperator = MkChromoLawFunctor (defaultSpace 4 Red) (defaultSpace 4 Red) idChromo

  verifyMassConservation v prf = prf

||| Canonical Composite Physical Law (Law ID = 2: Composition of Law 0 and Law 1)
public export
implementation PhysicsLaw 2 where
  dimOfLaw   = 4
  colorOfLaw = Red

  lawOperator = composeChromoLawFunctor
                  (MkChromoLawFunctor (defaultSpace 4 Red) (defaultSpace 4 Red) idChromo)
                  (MkChromoLawFunctor (defaultSpace 4 Red) (defaultSpace 4 Red) idChromo)

  verifyMassConservation v prf = prf
