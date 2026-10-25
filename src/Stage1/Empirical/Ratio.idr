module Stage1.Empirical.Ratio

import public Stage0.BoxInt
import public Stage1.Basis.Coordinate
import public Stage1.UnixelFraction

%default total



------------------------------------------------------------------------
-- EMPIRICAL PHYSICAL MEASUREMENT & RATIONAL CONFIDENCE INTERVAL TYPES
------------------------------------------------------------------------

||| An empirical physical measurement from CERN / CODATA / PDG with rational error bounds.
public export
record EmpiricalMeasurement where
  constructor MkEmpiricalMeasurement
  value         : UnixelFraction  -- Nominal measurement p / q
  uncertainty   : UnixelFraction  -- Standard uncertainty δA
  unitLabel     : String          -- e.g. "kg", "eV", "MHz", "m/s"
  datasetSource : String          -- e.g. "CODATA 2022", "CERN LHC 2024", "Planck 2018"

||| An empirical dimensionless ratio with exact rational confidence interval bounds [R_min, R_max].
public export
record EmpiricalRatio where
  constructor MkEmpiricalRatio
  nominalRatio  : UnixelFraction  -- R_nominal = A / B
  lowerBound    : UnixelFraction  -- R_min = (A - δA) / (B + δB)
  upperBound    : UnixelFraction  -- R_max = (A + δA) / (B - δB)
  ratioName     : String          -- e.g. "m_p / m_e"
  datasetSource : String          -- e.g. "CODATA 2022"

||| Helper to construct an exact EmpiricalRatio directly from nominal value and error bounds.
public export
mkEmpiricalRatioDirect : String -> UnixelFraction -> UnixelFraction -> UnixelFraction -> String -> EmpiricalRatio
mkEmpiricalRatioDirect name nom low high source =
  MkEmpiricalRatio nom low high name source

||| Constructs an exact EmpiricalRatio from two EmpiricalMeasurements A and B.
public export
mkEmpiricalRatioFromMeasurements : String -> EmpiricalMeasurement -> EmpiricalMeasurement -> EmpiricalRatio
mkEmpiricalRatioFromMeasurements name measA measB =
  let nomA = value measA
      errA = uncertainty measA
      nomB = value measB
      errB = uncertainty measB
      
      minA = subUnixelFraction nomA errA
      maxA = addUnixelFraction nomA errA
      minB = subUnixelFraction nomB errB
      maxB = addUnixelFraction nomB errB
      
      nominalVal = divUnixelFraction nomA nomB
      lowerVal   = divUnixelFraction minA maxB
      upperVal   = divUnixelFraction maxA minB
  in MkEmpiricalRatio nominalVal lowerVal upperVal name (datasetSource measA ++ " / " ++ datasetSource measB)
