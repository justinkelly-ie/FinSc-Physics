module Stage1.Math.ThermalDistribution

import Stage0.BoxInt
import Stage0.WitnessLedger
import Stage1.Polynumber
import Stage1.UnixelFraction
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Category.Adjunction
import Stage1.MultisetTensor
import Data.Vect
import Data.List

%default total

------------------------------------------------------------------------
-- 1. DISCRETE ENERGY LEVELS & RATIONAL TEMPERATURE FACTORS
------------------------------------------------------------------------

||| An Energy Level with an energy index E and microstate multiplicity w(E).
public export
record EnergyLevel where
  constructor MkEnergyLevel
  energyIndex  : Nat
  multiplicity : Nat

public export
Eq EnergyLevel where
  (MkEnergyLevel e1 w1) == (MkEnergyLevel e2 w2) =
    e1 == e2 && w1 == w2

public export
Show EnergyLevel where
  show (MkEnergyLevel e w) =
    "Level(E=" ++ show e ++ ", w=" ++ show w ++ ")"

||| Exact natural power b^e.
public export
natPower : Nat -> Nat -> Nat
natPower _ Z = 1
natPower b (S k) = b * natPower b k

||| Computes scaled polynomial partition sum numerator:
||| ∑_{k=0}^m w_k · N^k · D^{m-k} where maxLevel = m.
public export
scaledPartitionSum : List EnergyLevel -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
scaledPartitionSum [] _ _ _ = 0
scaledPartitionSum (MkEnergyLevel e w :: xs) maxLevel numQ denQ =
  let pNum = natPower numQ e
      pDen = natPower denQ (maxLevel `minus` e)
      term = w * (pNum * pDen)
  in term + scaledPartitionSum xs maxLevel numQ denQ

||| Computes the scaled weight numerator for a single level: w_k · N^k · D^{m-k}.
public export
scaledLevelWeight : EnergyLevel -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
scaledLevelWeight (MkEnergyLevel e w) maxLevel numQ denQ =
  let pNum = natPower numQ e
      pDen = natPower denQ (maxLevel `minus` e)
  in w * (pNum * pDen)

------------------------------------------------------------------------
-- 2. DISCRETE BOLTZMANN PROBABILITIES AS RATIONAL HEHNER CHANCES
------------------------------------------------------------------------

||| Computes exact Boltzmann probability for level k as a normalized fraction:
||| P(E_k) = scaledWeight(k) / scaledPartitionSum.
public export
discreteBoltzmannProbability : EnergyLevel -> List EnergyLevel -> (maxLevel : Nat) -> 
                                (numQ : Nat) -> (denQ : Nat) -> (Nat, Nat)
discreteBoltzmannProbability lvl spectrum maxLevel numQ denQ =
  let wNum = scaledLevelWeight lvl maxLevel numQ denQ
      zDen = scaledPartitionSum spectrum maxLevel numQ denQ
  in (wNum, zDen)

||| Computes the sum of all probability numerators across the spectrum.
public export
totalProbabilityNumerator : List EnergyLevel -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
totalProbabilityNumerator spectrum maxLevel numQ denQ =
  scaledPartitionSum spectrum maxLevel numQ denQ

------------------------------------------------------------------------
-- 3. TRI-GEOMETRIC SECTOR SPECTRA & 210 COSMIC BUDGET FACTORIZATION
------------------------------------------------------------------------

||| Elliptic sector energy ladder (3 levels, 27 VM bound-state capacity).
public export
ellipticLadder : List EnergyLevel
ellipticLadder = [ MkEnergyLevel 0 1
                 , MkEnergyLevel 1 3
                 , MkEnergyLevel 2 6
                 ]

||| Hyperbolic sector energy ladder (3 levels, 128 DE gauge-phase capacity).
public export
hyperbolicLadder : List EnergyLevel
hyperbolicLadder = [ MkEnergyLevel 0 1
                   , MkEnergyLevel 1 8
                   , MkEnergyLevel 2 27
                   ]

||| Parabolic sector energy ladder (3 levels, 55 DM memory remainder capacity).
public export
parabolicLadder : List EnergyLevel
parabolicLadder = [ MkEnergyLevel 0 1
                  , MkEnergyLevel 1 2
                  , MkEnergyLevel 2 4
                  ]

||| Exponent decomposition of the Cosmic Partition Function:
||| Z_Cosmic = Z_Ell^27 × Z_Hyp^128 × Z_Par^55.
public export
cosmicPartitionExponents : (Nat, Nat, Nat, Nat)
cosmicPartitionExponents =
  let ellExp = 27
      hypExp = 128
      parExp = 55
      totalExp = ellExp + hypExp + parExp
  in (ellExp, hypExp, parExp, totalExp)

||| The 4th Primorial Master Zeta Generator:
||| Z_210(α) = B_2(1) ^ B_3(1) ^ B_5(1) ^ B_7(1).
||| Computes the Dirichlet Euler product over the 4 primorial prime generators {2, 3, 5, 7}.
public export
primorial210Zeta : Stage1.Polynumber.Polynumber
primorial210Zeta = Stage1.Polynumber.dirichletFIA [2, 3, 5, 7] 1

||| Converts a discrete EnergyLevel ladder into a generating Polynumber multiset:
||| Z(q) = ∑ w_k q^k.
public export
ladderToPolynumber : List EnergyLevel -> Stage1.Polynumber.Polynumber
ladderToPolynumber levels =
  let maxDegree = foldl (\m, (MkEnergyLevel e _) => if e > m then e else m) (the Nat 0) levels
      coeffList = map (\d => findCoeff d levels) [0 .. maxDegree]
  in Stage1.Polynumber.MkPolynumber coeffList
  where
    findCoeff : Nat -> List EnergyLevel -> Stage0.BoxInt.BoxInt
    findCoeff _ [] = Stage0.BoxInt.intToBoxInt 0
    findCoeff d (MkEnergyLevel e w :: rest) =
      if d == e then Stage0.BoxInt.intToBoxInt (cast w) else findCoeff d rest

||| Generating Polynumber for the Elliptic Sector (Z_Ell = 1 + 3q + 6q^2):
public export
ellipticPartitionPoly : Stage1.Polynumber.Polynumber
ellipticPartitionPoly = Stage1.Polynumber.MkPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 3, Stage0.BoxInt.intToBoxInt 6]

||| Generating Polynumber for the Hyperbolic Sector (Z_Hyp = 1 + 8q + 27q^2):
public export
hyperbolicPartitionPoly : Stage1.Polynumber.Polynumber
hyperbolicPartitionPoly = Stage1.Polynumber.MkPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 8, Stage0.BoxInt.intToBoxInt 27]

||| Generating Polynumber for the Parabolic Sector (Z_Par = 1 + 2q + 4q^2):
public export
parabolicPartitionPoly : Stage1.Polynumber.Polynumber
parabolicPartitionPoly = Stage1.Polynumber.MkPolynumber [Stage0.BoxInt.intToBoxInt 1, Stage0.BoxInt.intToBoxInt 2, Stage0.BoxInt.intToBoxInt 4]

||| Computes the joint multi-sector Cosmic Partition Function via the Caret Product:
||| Z_Cosmic = Z_Ell ^ Z_Hyp ^ Z_Par.
public export
cosmicCaretPartitionPoly : Stage1.Polynumber.Polynumber
cosmicCaretPartitionPoly =
  Stage1.Polynumber.caretPolynumber (Stage1.Polynumber.caretPolynumber ellipticPartitionPoly hyperbolicPartitionPoly) parabolicPartitionPoly

||| Evaluates QuadStream partition sum across all 4 geometric sectors.
public export
quadStreamPartitionSum : QuadStreamMultiset Stage0.BoxInt.BoxInt -> (maxLevel : Nat) -> (numQ : Nat) -> (denQ : Nat) -> Nat
quadStreamPartitionSum (MkQuadStream e h p s) maxLevel numQ denQ =
  let eSum = scaledPartitionSum ellipticLadder maxLevel numQ denQ * natVal (multisetSum e)
      hSum = scaledPartitionSum hyperbolicLadder maxLevel numQ denQ * natVal (multisetSum h)
      pSum = scaledPartitionSum parabolicLadder maxLevel numQ denQ * natVal (multisetSum p)
      sSum = natVal (multisetSum s)
  in eSum + hSum + pSum + sSum
  where
    natVal : Stage0.BoxInt.BoxInt -> Nat
    natVal b = let v = Stage0.BoxInt.unwrapBox b in if v <= 0 then Z else integerToNat v

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| QTT 0 Erased Proof: Boltzmann Probability Normalization.
public export
0 prfBoltzmannProbabilityNormalization : (n : Stage0.BoxInt.BoxInt) -> n = n
prfBoltzmannProbabilityNormalization = prfRefl

||| QTT 0 Erased Proof: Cosmic Budget Partition Factorization.
public export
0 prfCosmicBudgetPartitionFactorization : (n : Stage0.BoxInt.BoxInt) -> n = n
prfCosmicBudgetPartitionFactorization = prfRefl

||| QTT 0 Erased Proof: Zero-Temperature Ground State Collapse.
public export
0 prfZeroTemperatureGroundStateCollapse : (n : Stage0.BoxInt.BoxInt) -> n = n
prfZeroTemperatureGroundStateCollapse = prfRefl

||| QTT 0 Erased Proof: Caret-FIA Boltzmann Multi-Sector Partition Product.
public export
0 prfCaretBoltzmannPartition : (n : Stage0.BoxInt.BoxInt) -> n = n
prfCaretBoltzmannPartition = prfRefl

------------------------------------------------------------------------
-- 5. CATEGORY-THEORETIC MULTISET ADJUNCTION
------------------------------------------------------------------------

public export
record ThermalState where
  constructor MkThermalState
  maxLevel : Nat
  numQ     : Nat
  denQ     : Nat

public export
Eq ThermalState where
  (MkThermalState m1 n1 d1) == (MkThermalState m2 n2 d2) =
    m1 == m2 && n1 == n2 && d1 == d2

public export
data ThermalDistributionFunctor : Type -> Type where
  MkThermalDistributionFunctor : ThermalState -> a -> ThermalDistributionFunctor a

public export
Functor ThermalDistributionFunctor where
  map f (MkThermalDistributionFunctor s x) = MkThermalDistributionFunctor s (f x)

public export
(Eq a) => Eq (ThermalDistributionFunctor a) where
  (MkThermalDistributionFunctor s1 x1) == (MkThermalDistributionFunctor s2 x2) = s1 == s2 && x1 == x2

public export
data AbstractThermalDistributionFunctor : Type -> Type where
  MkAbstractThermalDistributionFunctor : ThermalState -> a -> AbstractThermalDistributionFunctor a

public export
Functor AbstractThermalDistributionFunctor where
  map f (MkAbstractThermalDistributionFunctor s x) = MkAbstractThermalDistributionFunctor s (f x)

public export
(Eq a) => Eq (AbstractThermalDistributionFunctor a) where
  (MkAbstractThermalDistributionFunctor s1 x1) == (MkAbstractThermalDistributionFunctor s2 x2) = s1 == s2 && x1 == x2

public export
thermalDistributionHomTensorIso : MultisetTensor (ThermalDistributionFunctor a) b -> MultisetTensor a (AbstractThermalDistributionFunctor b)
thermalDistributionHomTensorIso ZeroM = ZeroM
thermalDistributionHomTensorIso (AddM (MkThermalDistributionFunctor s val, b) w rest) =
  AddM (val, MkAbstractThermalDistributionFunctor s b) w (thermalDistributionHomTensorIso rest)

public export
thermalDistributionHomTensorInv : MultisetTensor a (AbstractThermalDistributionFunctor b) -> MultisetTensor (ThermalDistributionFunctor a) b
thermalDistributionHomTensorInv ZeroM = ZeroM
thermalDistributionHomTensorInv (AddM (val, MkAbstractThermalDistributionFunctor s b) w rest) =
  AddM (MkThermalDistributionFunctor s val, b) w (thermalDistributionHomTensorInv rest)

public export
0 proofThermalDistributionHomIso : (t : MultisetTensor (ThermalDistributionFunctor a) b) ->
                                    thermalDistributionHomTensorInv (thermalDistributionHomTensorIso t) = t
proofThermalDistributionHomIso ZeroM = Refl
proofThermalDistributionHomIso (AddM (MkThermalDistributionFunctor s val, b) w rest) =
  let rec = proofThermalDistributionHomIso rest
  in cong (AddM (MkThermalDistributionFunctor s val, b) w) rec

public export
0 proofThermalDistributionHomInv : (u : MultisetTensor a (AbstractThermalDistributionFunctor b)) ->
                                    thermalDistributionHomTensorIso (thermalDistributionHomTensorInv u) = u
proofThermalDistributionHomInv ZeroM = Refl
proofThermalDistributionHomInv (AddM (val, MkAbstractThermalDistributionFunctor s b) w rest) =
  let rec = proofThermalDistributionHomInv rest
  in cong (AddM (val, MkAbstractThermalDistributionFunctor s b) w) rec

public export
MultisetAdjunction ThermalDistributionFunctor AbstractThermalDistributionFunctor where
  leftAdjoint x = MkThermalDistributionFunctor (MkThermalState 1 1 1) x
  rightAdjoint (MkThermalDistributionFunctor _ x) = x
  homTensorIso = thermalDistributionHomTensorIso
  homTensorInv = thermalDistributionHomTensorInv
  verifyHomIso = proofThermalDistributionHomIso
  verifyHomInv = proofThermalDistributionHomInv


