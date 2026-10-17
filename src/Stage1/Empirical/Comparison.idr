module Stage1.Empirical.Comparison

import public Stage1.Empirical.Ratio
import public Stage0.Measurements

%default total

------------------------------------------------------------------------
-- CONSTRUCTIST EMPIRICAL RATIO COMPARISON & AUDIT ENGINE
------------------------------------------------------------------------

||| Audits whether a theoretical model ratio falls strictly within experimental confidence interval bounds:
||| lowerBound <= modelValue <= upperBound.
public export
auditRatioWithinConfidenceInterval : UnixelFraction -> EmpiricalRatio -> Bool
auditRatioWithinConfidenceInterval modelVal emp =
  rationalLTE (lowerBound emp) modelVal && rationalLTE modelVal (upperBound emp)

||| Computes the exact Relative Rational Error E_rel = |modelVal - nominalRatio| / nominalRatio.
public export
relativeRationalError : UnixelFraction -> EmpiricalRatio -> UnixelFraction
relativeRationalError modelVal emp =
  let nom = nominalRatio emp
      diff = subUnixelFraction modelVal nom
      absNum = absBox (num diff)
      absDiff = mkUnixelFraction absNum (unwrapUnixel (den diff))
  in divUnixelFraction absDiff nom


||| Computes the Wildberger Quadrance Error Q_err = (modelVal - nominalRatio)^2.
public export
quadranceError : UnixelFraction -> EmpiricalRatio -> UnixelFraction
quadranceError modelVal emp =
  let nom = nominalRatio emp
      diff = subUnixelFraction modelVal nom
  in mulUnixelFraction diff diff

||| Audits that a theoretical value matches the empirical nominal value within a given error tolerance epsilon.
public export
auditRatioMatchesWithinTolerance : UnixelFraction -> EmpiricalRatio -> UnixelFraction -> Bool
auditRatioMatchesWithinTolerance modelVal emp eps =
  rationalLTE (relativeRationalError modelVal emp) eps

||| Converts a Unixel denominator to an exact BoxInt.
public export
unixelToBoxInt : Unixel -> BoxInt
unixelToBoxInt u = natToBoxInt (unwrapUnixel u)

||| Audits whether a model ratio matches empirical nominal within a given percentage error fraction (e.g. 1/10000 = 0.01%).
public export
auditRatioMatchesWithinPercentError : UnixelFraction -> EmpiricalRatio -> UnixelFraction -> Bool
auditRatioMatchesWithinPercentError modelVal emp maxRelError =
  rationalLTE (relativeRationalError modelVal emp) maxRelError



