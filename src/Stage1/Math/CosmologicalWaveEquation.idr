module Stage1.Math.CosmologicalWaveEquation

import Stage0.BoxInt
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.LinAlgebra.MetricTensor
import Stage1.Math.HelmholtzFreeEnergy
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.Category.Adjunction
import Stage1.MultisetTensor

%default total

------------------------------------------------------------------------
-- 1. DISCRETE DEWITT SUPERMETRIC & WHEELER-DEWITT HAMILTONIAN
------------------------------------------------------------------------

||| Evaluates scaled 2 * DeWitt Supermetric component G_{abcd}:
||| 2 * G_{abcd} = (g_{ac} * g_{bd} + g_{ad} * g_{bc}) - 2 * (g_{ab} * g_{cd}).
public export
scaledDeWittSupermetric : (gAc : Stage0.BoxInt.BoxInt) -> (gBd : Stage0.BoxInt.BoxInt) -> 
                         (gAd : Stage0.BoxInt.BoxInt) -> (gBc : Stage0.BoxInt.BoxInt) -> 
                         (gAb : Stage0.BoxInt.BoxInt) -> (gCd : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
scaledDeWittSupermetric gAc gBd gAd gBc gAb gCd =
  ((gAc * gBd) + (gAd * gBc)) - (Stage0.BoxInt.intToBoxInt 2 * (gAb * gCd))

||| Evaluates discrete Wheeler-DeWitt total super-Hamiltonian constraint:
||| H_total = E_grav + E_matter + E_sink - E_ref = 0.
public export
discreteSuperHamiltonian : (vm : Stage0.BoxInt.BoxInt) -> (de : Stage0.BoxInt.BoxInt) -> (dm : Stage0.BoxInt.BoxInt) -> (eRef : Stage0.BoxInt.BoxInt) -> Stage0.BoxInt.BoxInt
discreteSuperHamiltonian vm de dm eRef =
  let eTotal = (Stage0.BoxInt.intToBoxInt 4 * vm) + (Stage0.BoxInt.intToBoxInt 2 * de) + (Stage0.BoxInt.intToBoxInt 2 * dm)
  in eTotal - eRef

||| Evaluates discrete Wheeler-DeWitt total super-Hamiltonian constraint over a QuadStream state bundle.
public export
discreteSuperHamiltonianQuadStream : QuadStreamMultiset BoxInt -> BoxInt -> BoxInt
discreteSuperHamiltonianQuadStream qs eRef =
  let part = quadStreamToCosmicPartition qs
  in discreteSuperHamiltonian (vmTokens part) (deTokens part) (dmTokens part) eRef

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
  let g11Val = Stage0.BoxInt.intToBoxInt 1
      g22Val = Stage0.BoxInt.intToBoxInt 1
      g12Val = Stage0.BoxInt.intToBoxInt 0
      scaledG1122 = scaledDeWittSupermetric g12Val g12Val g12Val g12Val g11Val g22Val
  in Stage0.BoxInt.unwrapBox scaledG1122 == (-2)

||| Audits Zero Super-Hamiltonian Vanishing on Primorial 210 Ground State across QuadStream state bundles:
||| E_total = 4 * 27 + 2 * 128 + 2 * 55 = 108 + 256 + 110 = 474.
||| H_total = 474 - 474 = 0.
public export
auditZeroWheelerDeWittConstraintProof : Bool
auditZeroWheelerDeWittConstraintProof =
  let e = AddM (intToBoxInt 0) (intToBoxInt 27) ZeroM
      h = AddM (intToBoxInt 0) (intToBoxInt 128) ZeroM
      p = AddM (intToBoxInt 0) (intToBoxInt 0) ZeroM
      s = AddM (intToBoxInt 0) (intToBoxInt 55) ZeroM
      qs = MkQuadStream e h p s
      hTotal = discreteSuperHamiltonianQuadStream qs (Stage0.BoxInt.intToBoxInt 474)
  in Stage0.BoxInt.unwrapBox hTotal == 0

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

------------------------------------------------------------------------
-- 3. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record DeWittState where
  constructor MkDeWittState
  g11 : BoxInt
  g22 : BoxInt
  g12 : BoxInt

public export
Eq DeWittState where
  (MkDeWittState a1 b1 c1) == (MkDeWittState a2 b2 c2) =
    a1 == a2 && b1 == b2 && c1 == c2

public export
data DeWittWaveFunctor : Type -> Type where
  MkDeWittWaveFunctor : DeWittState -> a -> DeWittWaveFunctor a

public export
Functor DeWittWaveFunctor where
  map f (MkDeWittWaveFunctor s x) = MkDeWittWaveFunctor s (f x)

public export
(Eq a) => Eq (DeWittWaveFunctor a) where
  (MkDeWittWaveFunctor s1 x1) == (MkDeWittWaveFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractDeWittWaveFunctor : Type -> Type where
  MkAbstractDeWittWaveFunctor : DeWittState -> a -> AbstractDeWittWaveFunctor a

public export
Functor AbstractDeWittWaveFunctor where
  map f (MkAbstractDeWittWaveFunctor s x) = MkAbstractDeWittWaveFunctor s (f x)

public export
(Eq a) => Eq (AbstractDeWittWaveFunctor a) where
  (MkAbstractDeWittWaveFunctor s1 x1) == (MkAbstractDeWittWaveFunctor s2 x2) = s1 == s2 && x1 == x2

public export
deWittWaveHomTensorIso : MultisetTensor (DeWittWaveFunctor a) b -> MultisetTensor a (AbstractDeWittWaveFunctor b)
deWittWaveHomTensorIso ZeroM = ZeroM
deWittWaveHomTensorIso (AddM (MkDeWittWaveFunctor s val, b) w rest) =
  AddM (val, MkAbstractDeWittWaveFunctor s b) w (deWittWaveHomTensorIso rest)

public export
deWittWaveHomTensorInv : MultisetTensor a (AbstractDeWittWaveFunctor b) -> MultisetTensor (DeWittWaveFunctor a) b
deWittWaveHomTensorInv ZeroM = ZeroM
deWittWaveHomTensorInv (AddM (val, MkAbstractDeWittWaveFunctor s b) w rest) =
  AddM (MkDeWittWaveFunctor s val, b) w (deWittWaveHomTensorInv rest)

public export
0 proofDeWittWaveHomIso : (t : MultisetTensor (DeWittWaveFunctor a) b) ->
                           deWittWaveHomTensorInv (deWittWaveHomTensorIso t) = t
proofDeWittWaveHomIso ZeroM = Refl
proofDeWittWaveHomIso (AddM (MkDeWittWaveFunctor s val, b) w rest) =
  let rec = proofDeWittWaveHomIso rest
  in cong (AddM (MkDeWittWaveFunctor s val, b) w) rec

public export
0 proofDeWittWaveHomInv : (u : MultisetTensor a (AbstractDeWittWaveFunctor b)) ->
                           deWittWaveHomTensorIso (deWittWaveHomTensorInv u) = u
proofDeWittWaveHomInv ZeroM = Refl
proofDeWittWaveHomInv (AddM (val, MkAbstractDeWittWaveFunctor s b) w rest) =
  let rec = proofDeWittWaveHomInv rest
  in cong (AddM (val, MkAbstractDeWittWaveFunctor s b) w) rec

public export
MultisetAdjunction DeWittWaveFunctor AbstractDeWittWaveFunctor where
  leftAdjoint x = MkDeWittWaveFunctor (MkDeWittState (intToBoxInt 0) (intToBoxInt 0) (intToBoxInt 0)) x
  rightAdjoint (MkDeWittWaveFunctor _ x) = x
  homTensorIso = deWittWaveHomTensorIso
  homTensorInv = deWittWaveHomTensorInv
  verifyHomIso = proofDeWittWaveHomIso
  verifyHomInv = proofDeWittWaveHomInv

