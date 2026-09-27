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
  let low  = lowerBound emp
      high = upperBound emp
      tLow  = rationalEquiv modelVal low || rationalEquiv (subUnixelFraction modelVal low) (mkUnixelFraction 0 1) || (let diff = subUnixelFraction modelVal low in not (unwrapBox (num diff) < 0))
      tHigh = rationalEquiv modelVal high || (let diff = subUnixelFraction high modelVal in not (unwrapBox (num diff) < 0))
  in tLow && tHigh

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
  let err = relativeRationalError modelVal emp
      diff = subUnixelFraction eps err
  in not (unwrapBox (num diff) < 0)

||| Converts a Unixel denominator to an exact Integer.
public export
unixelToInteger : Unixel -> Integer
unixelToInteger (MkUnixel Z) = 0
unixelToInteger (MkUnixel (S k)) = 1 + unixelToInteger (MkUnixel k)

||| Audits whether a model ratio matches empirical nominal within a given percentage error fraction (e.g. 1/10000 = 0.01%).
public export
auditRatioMatchesWithinPercentError : UnixelFraction -> EmpiricalRatio -> UnixelFraction -> Bool
auditRatioMatchesWithinPercentError modelVal emp maxRelError =
  let err = relativeRationalError modelVal emp
      errDen = unixelToInteger (den err)
      maxDen = unixelToInteger (den maxRelError)
      lhs = unwrapBox (num err) * maxDen
      rhs = unwrapBox (num maxRelError) * errDen
  in lhs <= rhs



