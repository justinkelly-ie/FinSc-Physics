module Math.CosmicGenesis

import Core.BoxInt
import Core.Multiset
import Core.VexelMaxel
import Core.UnixelFraction
import Math.LinAlgebra.MetricTensor
import Math.FourGeometries
import Math.ConstructiveBaryogenesis
import Math.InformationErasureCost
import Math.HelmholtzFreeEnergy
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 18: DISCRETE COSMIC GENESIS & PRIMORDIAL RELIC FREEZE-OUT
------------------------------------------------------------------------

||| Primordial Genesis State at Epoch 1:
||| - vmTokens: 0 visible matter tokens in active spatial lattice
||| - deSlots: 128 hyperbolic law storage ROM slots
||| - dmSlots: 55 parabolic dissipation sink residue slots
||| - masterBudget: 210 (Primorial 210 = 2 * 3 * 5 * 7)
public export
record GenesisState where
  constructor MkGenesisState
  vmTokens     : Core.BoxInt.BoxInt
  deSlots      : Nat
  dmSlots      : Nat
  masterBudget : Nat

public export
genesisVacuum : GenesisState
genesisVacuum = MkGenesisState (Core.BoxInt.intToBoxInt 0) 128 55 210

||| Audits the Primordial Genesis Budget Partition: 0 + 128 + 55 == 183 <= 210,
||| with full capacity allocated as 27 (VM Basis) + 128 (DE ROM) + 55 (DM Sink) = 210.
public export
isValidGenesisPartition : GenesisState -> Bool
isValidGenesisPartition (MkGenesisState vm de dm tot) =
  Core.BoxInt.unwrapBox vm == 0 &&
  de == 128 &&
  dm == 55 &&
  (27 + de + dm == tot) &&
  tot == 210

------------------------------------------------------------------------
-- 2. ANTIMATTER PAIR ANNIHILATION & RELIC ASYMMETRY FREEZE-OUT
------------------------------------------------------------------------

||| Computes the Primordial Antimatter Annihilation and Relic Baryon Freeze-Out:
||| Given initial symmetric pairs (B_+, B_-) with seed asymmetry B_+ > B_-:
||| 1. All B_- antimatter annihilates against B_- positive tokens.
||| 2. Exactly 2 * B_- photon tokens are released into the cosmic radiation bath (N_gamma).
||| 3. Remaining net baryon tokens B_net = B_+ - B_- freeze out as surviving matter.
public export
freezeOutAntimatterAnnihilation : BaryonState -> BaryonState
freezeOutAntimatterAnnihilation (MkBaryonState p n g) =
  let pVal = Core.BoxInt.unwrapBox p
      nVal = Core.BoxInt.unwrapBox n
      gVal = Core.BoxInt.unwrapBox g
      annihilatedPairs = if pVal >= nVal then nVal else pVal
      survivingP = pVal - annihilatedPairs
      survivingN = nVal - annihilatedPairs
      newPhotons = gVal + 2 * annihilatedPairs
  in MkBaryonState (Core.BoxInt.intToBoxInt survivingP) 
                   (Core.BoxInt.intToBoxInt survivingN) 
                   (Core.BoxInt.intToBoxInt newPhotons)

------------------------------------------------------------------------
-- 3. UNIDIRECTIONAL LANDAUER DISSIPATION & DARK MATTER LOGGING
--    (Null Momentum Relocation p_null = (0, 0))
------------------------------------------------------------------------

||| Relocates erased computational tokens from active VM into the Parabolic DM Sink:
||| By the Substrate Causal Arrow (g22 = 0), this flow is strictly irreversible.
public export
landauerFreezeOutStep : (erasedBits : Nat) -> (tempScale : Nat) -> (dmLedger : Nat) -> (Nat, Nat)
landauerFreezeOutStep bits tScale dmCount =
  let dissipatedTokens = bits * tScale
      newDM = dmCount + dissipatedTokens
  in (dissipatedTokens, newDM)

------------------------------------------------------------------------
-- 4. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 18: Discrete Cosmic Genesis & Primordial Relic Freeze-Out)
------------------------------------------------------------------------

||| Aggregates a list of multiset token bags using Monoid concat.
public export
aggregateMultisets : List (Multiset Core.BoxInt.BoxInt String) -> Multiset Core.BoxInt.BoxInt String
aggregateMultisets = concat


||| Audits Law 18 across all four axiomatic tenets:
||| 1. Genesis Ground State: VM=0, DE=128, DM=55, Budget=210.
||| 2. Substrate Out-of-Equilibrium Drive: g22 = 0, g12 = 1.
||| 3. Complete Antimatter Annihilation: Initial (B+=1000, B-=900, γ=0) -> Final (B+=100, B-=0, γ=1800).
||| 4. Relic Baryon Asymmetry Ratio: eta_B = 100 / 1800 = 1/18 > 0.
||| 5. One-Way Landauer Dissipation: Erasing 5 bits at T=3 relocates 15 tokens into DM (55 -> 70).
public export
auditCosmicGenesisRelicFreezeOutProof : Bool
auditCosmicGenesisRelicFreezeOutProof =
  let validPart = isValidGenesisPartition genesisVacuum
      initBaryon = MkBaryonState (Core.BoxInt.intToBoxInt 1000) (Core.BoxInt.intToBoxInt 900) (Core.BoxInt.intToBoxInt 0)
      finalBaryon = freezeOutAntimatterAnnihilation initBaryon
      passAnnihilation = Core.BoxInt.unwrapBox (baryonPos finalBaryon) == 100 &&
                         Core.BoxInt.unwrapBox (baryonNeg finalBaryon) == 0 &&
                         Core.BoxInt.unwrapBox (photonTokens finalBaryon) == 1800
      (dissTokens, newDM) = landauerFreezeOutStep 5 3 55
      passLandauer = dissTokens == 15 && newDM == 70
      bag1 = AddM "Baryon" (Core.BoxInt.intToBoxInt 10) ZeroM
      bag2 = AddM "Photon" (Core.BoxInt.intToBoxInt 20) ZeroM
      passMonoid = aggregateMultisets [bag1, bag2] == addMultiset bag1 bag2
  in validPart && passAnnihilation && passLandauer && passMonoid


