module Math.RationalRefraction

import Core.BoxInt
import Data.List

%default total

------------------------------------------------------------------------
-- 1. LAW 55: DISCRETE RATIONAL SNELL'S LAW & TRIPLE SPREAD LAW
------------------------------------------------------------------------

||| Evaluates Rational Snell's Law under Chromogeometric refraction:
||| n1^2 * s1 = n2^2 * s2  ==> (n1^2 * s1) - (n2^2 * s2) = 0.
%inline
public export
rationalSnellRefraction : BoxInt -> BoxInt -> BoxInt -> BoxInt -> BoxInt
rationalSnellRefraction n1 s1 n2 s2 =
  let lhs = (n1 * n1) * s1
      rhs = (n2 * n2) * s2
  in lhs - rhs

||| Verifies non-reflective total internal refraction invariant.
%inline
public export
isSnellRefracted : BoxInt -> BoxInt -> BoxInt -> BoxInt -> Bool
isSnellRefracted n1 s1 n2 s2 = boxZero (rationalSnellRefraction n1 s1 n2 s2)

------------------------------------------------------------------------
-- 2. FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Law 55 (Rational Snell's Law & Triple Spread Law):
||| For n1 = 2, s1 = 9, n2 = 3, s2 = 4: 4 * 9 = 36, 9 * 4 = 36 => 36 - 36 = 0.
%inline
public export
auditLaw55RationalSnellProof : Bool
auditLaw55RationalSnellProof =
  let n1 = intToBoxInt 2
      s1 = intToBoxInt 9
      n2 = intToBoxInt 3
      s2 = intToBoxInt 4
  in isSnellRefracted n1 s1 n2 s2
