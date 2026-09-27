module Stage0.Measurements

import public Stage1.Empirical.Ratio

%default total

------------------------------------------------------------------------
-- EXPERIMENTAL CERN / CODATA / PDG / PLANCK DIMENSIONLESS RATIO CATALOG
------------------------------------------------------------------------

||| CODATA 2022 Proton-to-Electron Mass Ratio: m_p / m_e = 1836.15267343(11).
public export
protonElectronMassRatio : EmpiricalRatio
protonElectronMassRatio =
  mkEmpiricalRatioDirect
    "m_p / m_e"
    (mkUnixelFraction (intToBoxInt 183615267343) 100000000)
    (mkUnixelFraction (intToBoxInt 183615267232) 100000000)
    (mkUnixelFraction (intToBoxInt 183615267454) 100000000)
    "CODATA 2022"

||| CODATA 2022 Muon-to-Electron Mass Ratio: m_μ / m_e = 206.7682830(46).
public export
muonElectronMassRatio : EmpiricalRatio
muonElectronMassRatio =
  mkEmpiricalRatioDirect
    "m_μ / m_e"
    (mkUnixelFraction (intToBoxInt 2067682830) 10000000)
    (mkUnixelFraction (intToBoxInt 2067682784) 10000000)
    (mkUnixelFraction (intToBoxInt 2067682876) 10000000)
    "CODATA 2022"

||| CODATA 2022 Inverse Fine Structure Constant: α^-1 = 137.035999084(21).
public export
inverseFineStructureConstant : EmpiricalRatio
inverseFineStructureConstant =
  mkEmpiricalRatioDirect
    "α^-1"
    (mkUnixelFraction (intToBoxInt 137035999084) 1000000000)
    (mkUnixelFraction (intToBoxInt 137035999063) 1000000000)
    (mkUnixelFraction (intToBoxInt 137035999105) 1000000000)
    "CODATA 2022"

||| CERN LHC / PDG 2024 Electroweak Boson Mass Ratio: m_W / m_Z = 0.881446(16).
public export
electroweakBosonMassRatio : EmpiricalRatio
electroweakBosonMassRatio =
  mkEmpiricalRatioDirect
    "m_W / m_Z"
    (mkUnixelFraction (intToBoxInt 881446) 1000000)
    (mkUnixelFraction (intToBoxInt 881280) 1000000)
    (mkUnixelFraction (intToBoxInt 881600) 1000000)
    "CERN LHC / PDG 2024"

||| Planck 2018 Primordial Cosmic Inflation Scalar Spectral Index: n_s = 0.9649(42).
public export
cosmicInflationSpectralIndex : EmpiricalRatio
cosmicInflationSpectralIndex =
  mkEmpiricalRatioDirect
    "n_s"
    (mkUnixelFraction (intToBoxInt 9649) 10000)
    (mkUnixelFraction (intToBoxInt 9607) 10000)
    (mkUnixelFraction (intToBoxInt 9691) 10000)
    "Planck 2018"
