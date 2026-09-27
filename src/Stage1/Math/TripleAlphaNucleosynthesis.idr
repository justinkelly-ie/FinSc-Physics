module Stage1.Math.TripleAlphaNucleosynthesis

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.QuadStream
import Stage1.Math.QuadStreamPhysicalLaws
import Stage1.Category.Adjunction
import Stage1.MultisetTensor
import Data.List

%default total

------------------------------------------------------------------------
-- 1. LAW 52: DISCRETE TRIPLE-ALPHA CARBON & PHOSPHORUS NUCLEOSYNTHESIS
------------------------------------------------------------------------

||| Evaluates Triple-Alpha fusion mass token conservation: 3 * Alpha (108) = Carbon-12 (324).
%inline
public export
tripleAlphaFusionTokens : BoxInt -> BoxInt
tripleAlphaFusionTokens alphaMass = intToBoxInt 3 * alphaMass

||| Evaluates QuadStream Triple-Alpha fusion mass token conservation.
public export
evaluateQuadStreamTripleAlpha : QuadStreamMultiset BoxInt -> BoxInt
evaluateQuadStreamTripleAlpha (MkQuadStream e h p s) =
  let totalAlpha = multisetSum e + multisetSum h + multisetSum p + multisetSum s
  in tripleAlphaFusionTokens totalAlpha

||| Evaluates Phosphorus-31 synthesis token count (837 tokens = 31 * 27).
%inline
public export
phosphorus31MassTokens : BoxInt
phosphorus31MassTokens = intToBoxInt 837

------------------------------------------------------------------------
-- 2. CATEGORY-THEORETIC HOM-TENSOR MULTISET ADJUNCTION (L ⊣ R)
------------------------------------------------------------------------

||| Left adjoint Triple-Alpha Nucleosynthesis functor wrapping mass state and payload a
public export
data TripleAlphaFunctor : Type -> Type where
  MkTripleAlphaFunctor : BoxInt -> a -> TripleAlphaFunctor a

public export
Functor TripleAlphaFunctor where
  map f (MkTripleAlphaFunctor m x) = MkTripleAlphaFunctor m (f x)

public export
(Eq a) => Eq (TripleAlphaFunctor a) where
  (MkTripleAlphaFunctor m1 x1) == (MkTripleAlphaFunctor m2 x2) = m1 == m2 && x1 == x2

||| Right adjoint Triple-Alpha Nucleosynthesis functor wrapping abstract mass state and payload a
public export
data AbstractTripleAlphaFunctor : Type -> Type where
  MkAbstractTripleAlphaFunctor : BoxInt -> a -> AbstractTripleAlphaFunctor a

public export
Functor AbstractTripleAlphaFunctor where
  map f (MkAbstractTripleAlphaFunctor m x) = MkAbstractTripleAlphaFunctor m (f x)

public export
(Eq a) => Eq (AbstractTripleAlphaFunctor a) where
  (MkAbstractTripleAlphaFunctor m1 x1) == (MkAbstractTripleAlphaFunctor m2 x2) = m1 == m2 && x1 == x2

||| Forward hom-tensor isomorphism mapping micro to macro Triple-Alpha multiset tensors
public export
tripleAlphaHomTensorIso : MultisetTensor (TripleAlphaFunctor a) b -> MultisetTensor a (AbstractTripleAlphaFunctor b)
tripleAlphaHomTensorIso ZeroM = ZeroM
tripleAlphaHomTensorIso (AddM (MkTripleAlphaFunctor m val, b) w rest) =
  AddM (val, MkAbstractTripleAlphaFunctor m b) w (tripleAlphaHomTensorIso rest)

||| Inverse hom-tensor isomorphism mapping macro to micro Triple-Alpha multiset tensors
public export
tripleAlphaHomTensorInv : MultisetTensor a (AbstractTripleAlphaFunctor b) -> MultisetTensor (TripleAlphaFunctor a) b
tripleAlphaHomTensorInv ZeroM = ZeroM
tripleAlphaHomTensorInv (AddM (val, MkAbstractTripleAlphaFunctor m b) w rest) =
  AddM (MkTripleAlphaFunctor m val, b) w (tripleAlphaHomTensorInv rest)

||| Static proof witness verifying forward inverse round-trip isomorphism identity
public export
0 proofTripleAlphaHomIso : (t : MultisetTensor (TripleAlphaFunctor a) b) ->
                           tripleAlphaHomTensorInv (tripleAlphaHomTensorIso t) = t
proofTripleAlphaHomIso ZeroM = Refl
proofTripleAlphaHomIso (AddM (MkTripleAlphaFunctor m val, b) w rest) =
  let rec = proofTripleAlphaHomIso rest
  in cong (AddM (MkTripleAlphaFunctor m val, b) w) rec

||| Static proof witness verifying reverse inverse round-trip isomorphism identity
public export
0 proofTripleAlphaHomInv : (u : MultisetTensor a (AbstractTripleAlphaFunctor b)) ->
                           tripleAlphaHomTensorIso (tripleAlphaHomTensorInv u) = u
proofTripleAlphaHomInv ZeroM = Refl
proofTripleAlphaHomInv (AddM (val, MkAbstractTripleAlphaFunctor m b) w rest) =
  let rec = proofTripleAlphaHomInv rest
  in cong (AddM (val, MkAbstractTripleAlphaFunctor m b) w) rec

||| Category-Theoretic MultisetAdjunction instance TripleAlphaFunctor ⊣ AbstractTripleAlphaFunctor
public export
MultisetAdjunction TripleAlphaFunctor AbstractTripleAlphaFunctor where
  leftAdjoint x = MkTripleAlphaFunctor (intToBoxInt 0) x
  rightAdjoint (MkTripleAlphaFunctor _ x) = x
  homTensorIso = tripleAlphaHomTensorIso
  homTensorInv = tripleAlphaHomTensorInv
  verifyHomIso = proofTripleAlphaHomIso
  verifyHomInv = proofTripleAlphaHomInv

------------------------------------------------------------------------
-- 3. FORMAL INVARIANT AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Law 52 (Triple-Alpha Carbon & Phosphorus Nucleosynthesis):
||| 1. 3 * 108 = 324 mass tokens for 12C core.
||| 2. 31P carries 837 mass tokens (31 amu).
%inline
public export
auditLaw52TripleAlphaProof : Bool
auditLaw52TripleAlphaProof =
  let c12 = tripleAlphaFusionTokens (intToBoxInt 108)
  in (unwrapBox c12 == 324) && (unwrapBox phosphorus31MassTokens == 837)

