module Math.MultiTerminalConduction

import Core.BoxInt
import Core.Multiset
import Core.VexelMaxel
import Core.UnixelFraction
import Math.FourGeometries
import Data.List
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. LAW 28: DISCRETE LANDAUER-BÜTTIKER MULTI-TERMINAL CONDUCTION
------------------------------------------------------------------------

||| 3-Terminal Conductance Matrix G_pq (in units of e^2/h):
||| Terminal 1, 2, 3
public export
record ConductanceMatrix3x3 where
  constructor MkConductanceMatrix3x3
  g12 : Nat
  g13 : Nat
  g21 : Nat
  g23 : Nat
  g31 : Nat
  g32 : Nat

public export
Eq ConductanceMatrix3x3 where
  (MkConductanceMatrix3x3 a1 b1 c1 d1 e1 f1) == (MkConductanceMatrix3x3 a2 b2 c2 d2 e2 f2) =
    a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2 && e1 == e2 && f1 == f2

||| Validates Time-Reversal Microscopic Reciprocity: G_pq == G_qp.
public export
isBuettikerReciprocal : ConductanceMatrix3x3 -> Bool
isBuettikerReciprocal (MkConductanceMatrix3x3 g12 g13 g21 g23 g31 g32) =
  g12 == g21 && g13 == g31 && g23 == g32

||| Computes Terminal Currents I_1, I_2, I_3 given Terminal Voltages V_1, V_2, V_3:
||| I_p = sum_{q != p} G_pq * (V_p - V_q)
public export
terminalCurrents : ConductanceMatrix3x3 -> (v1 : Core.BoxInt.BoxInt) -> (v2 : Core.BoxInt.BoxInt) -> (v3 : Core.BoxInt.BoxInt) -> (Core.BoxInt.BoxInt, Core.BoxInt.BoxInt, Core.BoxInt.BoxInt)
terminalCurrents (MkConductanceMatrix3x3 g12 g13 g21 g23 g31 g32) v1 v2 v3 =
  let u1 = unwrapBox v1
      u2 = unwrapBox v2
      u3 = unwrapBox v3
      i1 = (cast g12) * (u1 - u2) + (cast g13) * (u1 - u3)
      i2 = (cast g21) * (u2 - u1) + (cast g23) * (u2 - u3)
      i3 = (cast g31) * (u3 - u1) + (cast g32) * (u3 - u2)
  in (Core.BoxInt.intToBoxInt i1, Core.BoxInt.intToBoxInt i2, Core.BoxInt.intToBoxInt i3)

||| Validates Kirchhoff Total Current Conservation: I_1 + I_2 + I_3 == 0.
public export
isKirchhoffConserved : (Core.BoxInt.BoxInt, Core.BoxInt.BoxInt, Core.BoxInt.BoxInt) -> Bool
isKirchhoffConserved (i1, i2, i3) =
  unwrapBox i1 + unwrapBox i2 + unwrapBox i3 == 0

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Law 28: Discrete Landauer-Büttiker Conduction)
------------------------------------------------------------------------

||| Audits Law 28 across multi-terminal quantum transport:
||| 1. Matrix G = {g12=2, g13=1, g21=2, g23=3, g31=1, g32=3} is reciprocal (G_pq = G_qp).
||| 2. Voltages V = (10, 5, 2):
|||    I_1 = 2*(10-5) + 1*(10-2) = 2*5 + 1*8 = 18
|||    I_2 = 2*(5-10) + 3*(5-2) = 2*(-5) + 3*3 = -10 + 9 = -1
|||    I_3 = 1*(2-10) + 3*(2-5) = 1*(-8) + 3*(-3) = -8 - 9 = -17
||| 3. Kirchhoff Loop Conservation: 18 + (-1) + (-17) = 0.
public export
auditMultiTerminalConductionProof : Bool
auditMultiTerminalConductionProof =
  let gMat = MkConductanceMatrix3x3 2 1 2 3 1 3
      v1 = Core.BoxInt.intToBoxInt 10
      v2 = Core.BoxInt.intToBoxInt 5
      v3 = Core.BoxInt.intToBoxInt 2
      currs = terminalCurrents gMat v1 v2 v3
      (i1, i2, i3) = currs
  in isBuettikerReciprocal gMat &&
     unwrapBox i1 == 18 &&
     unwrapBox i2 == -1 &&
     unwrapBox i3 == -17 &&
     isKirchhoffConserved currs
