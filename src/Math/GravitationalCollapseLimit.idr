module Math.GravitationalCollapseLimit

import Core.BoxInt
import Core.Multiset
import Core.VexelMaxel
import Core.UnixelFraction
import Core
import Math.ExclusionPrinciple
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 24: DISCRETE TOLMAN-OPPENHEIMER-VOLKOFF (TOV) GRAVITATIONAL MASS LIMIT
------------------------------------------------------------------------

||| Maximum stable discrete mass capacity for a compact degenerate core
||| before gravitational shear exceeds Pauli degeneracy pressure.
||| Equal to the Alpha Cluster Capacity: M_TOV = 108 tokens.
public export
maxTOVMassLimit : Nat
maxTOVMassLimit = 108

||| Checks whether a degenerate core with token mass M is gravitationally stable:
||| Stable: M <= M_TOV (108)
||| Collapsed: M > M_TOV (collapses to a holographic boundary Area=54)
public export
isTOVGravitationallyStable : (coreMass : Nat) -> Bool
isTOVGravitationallyStable m = m <= maxTOVMassLimit

||| Discrete Core Evolution State under gravitational accretion:
public export
record StellarCore where
  constructor MkStellarCore
  coreMass     : Nat
  isCollapsed  : Bool
  boundaryArea : Nat

public export
Eq StellarCore where
  (MkStellarCore m1 c1 a1) == (MkStellarCore m2 c2 a2) =
    m1 == m2 && c1 == c2 && a1 == a2

||| Executes one accretion step of dM = 1:
public export
stepCoreAccretion : StellarCore -> StellarCore
stepCoreAccretion (MkStellarCore m _ _) =
  let newM = m + 1
      collapsed = not (isTOVGravitationallyStable newM)
      area = if collapsed then 54 else 0
  in MkStellarCore newM collapsed area

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 24: Discrete TOV Limit)
------------------------------------------------------------------------

||| Audits Law 24 across stellar core stability:
||| 1. Stable Neutron Core at M = 108 (isCollapsed = False).
||| 2. Critical Super-TOV Accretion at M = 109 triggers immediate horizon collapse (isCollapsed = True, boundaryArea = 54).
||| 3. Sub-TOV stability holds for M = 50.
public export
auditGravitationalCollapseLimitProof : Bool
auditGravitationalCollapseLimitProof =
  let core108 = MkStellarCore 108 False 0
      core109 = stepCoreAccretion core108
  in isTOVGravitationallyStable 50 &&
     isTOVGravitationallyStable 108 &&
     not (isTOVGravitationallyStable 109) &&
     isCollapsed core109 &&
     boundaryArea core109 == 54
