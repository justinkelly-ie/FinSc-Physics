module Math.ApplicativeHomomorphism

import Core.BoxInt
import Core.ScaleTransform
import Math.Multiset

import Data.Vect

%default total

||| An Applicative Homomorphism natural transformation morphing applicative context `f` to `g`.
||| Preserves `pure` and application `(<*>)` across scale and state domain transformations.
public export
interface (Applicative f, Applicative g) => ApplicativeHomomorphism (0 f : Type -> Type) (0 g : Type -> Type) where
  ||| The underlying natural transformation
  morph : {0 a : Type} -> f a -> g a

  ||| Proof 1: Pure preservation law: morph (pure x) === pure x
  0 purePreserved : {0 a : Type} -> (x : a) -> morph (pure {f} x) = pure {f=g} x

  ||| Proof 2: Application preservation law: morph (h <*> x) === morph h <*> morph x
  0 appPreserved : {0 a, b : Type} -> (h : f (a -> b)) -> (x : f a) -> morph (h <*> x) = morph h <*> morph x

-----------------------------------------------------------------------
-- DOMAIN HOMOMORPHISM INSTANCES (LIST & MULTISET)
-----------------------------------------------------------------------


||| Converts a Maybe passband context into a Non-deterministic List bag context.
public export
maybeToList : Maybe a -> List a
maybeToList Nothing  = []
maybeToList (Just x) = [x]

public export
ApplicativeHomomorphism Maybe List where
  morph = maybeToList

  purePreserved x = Refl

  appPreserved Nothing  _          = Refl
  appPreserved (Just f) Nothing    = Refl
  appPreserved (Just f) (Just x)   = Refl

||| Converts a Maybe passband state context directly into a Constructivist Multiset BoxInt Token Bag.
public export
maybeToMultiset : Maybe a -> Multiset BoxInt a
maybeToMultiset Nothing  = ZeroM
maybeToMultiset (Just x) = AddM x (intToBoxInt 1) ZeroM

public export
ApplicativeHomomorphism Maybe (Multiset BoxInt) where
  morph = maybeToMultiset

  purePreserved x = Refl

  appPreserved Nothing  _          = Refl
  appPreserved (Just f) Nothing    = Refl
  appPreserved (Just f) (Just x)   = Refl

||| Simple Identity functor wrapper.
public export
record Id a where
  constructor MkId
  runId : a

public export
Functor Id where
  map f (MkId x) = MkId (f x)

public export
Applicative Id where
  pure x = MkId x
  (MkId f) <*> (MkId x) = MkId (f x)

||| Converts an Identity state context into a Single-Element List.
public export
idToList : Id a -> List a
idToList (MkId x) = [x]

public export
ApplicativeHomomorphism Id List where
  morph = idToList

  purePreserved x = Refl

  appPreserved (MkId f) (MkId x) = Refl

||| Converts an Identity state context into a Constructivist Multiset BoxInt Token.
public export
idToMultiset : Id a -> Multiset BoxInt a
idToMultiset (MkId x) = AddM x (intToBoxInt 1) ZeroM

public export
ApplicativeHomomorphism Id (Multiset BoxInt) where
  morph = idToMultiset

  purePreserved x = Refl

  appPreserved (MkId f) (MkId x) = Refl

||| Composite applicative homomorphism morphing f -> g -> h.
public export
composeHom : {0 f, g, h : Type -> Type} ->
             (morphFG : {0 a : Type} -> f a -> g a) ->
             (morphGH : {0 a : Type} -> g a -> h a) ->
             {0 a : Type} -> f a -> h a
composeHom morphFG morphGH x = morphGH (morphFG x)

-----------------------------------------------------------------------
-- PROPERTY VERIFICATION HELPERS
-----------------------------------------------------------------------

||| Verifies that morph preserves pure at runtime.
public export
prop_purePreservedOnMaybeToList : Integer -> Bool
prop_purePreservedOnMaybeToList x =
  maybeToList (pure {f=Maybe} x) == pure {f=List} x

||| Verifies that morph preserves (<*>) at runtime.
prop_appPreservedOnMaybeToList : Maybe (Integer -> Integer) -> Maybe Integer -> Bool
prop_appPreservedOnMaybeToList h x =
  maybeToList (h <*> x) == (maybeToList h <*> maybeToList x)

||| Verifies that morph preserves pure on Id to List at runtime.
public export
prop_purePreservedOnIdToList : Integer -> Bool
prop_purePreservedOnIdToList x =
  idToList (pure {f=Id} x) == pure {f=List} x

||| Verifies that morph preserves (<*>) on Id to List at runtime.
public export
prop_appPreservedOnIdToList : (Integer -> Integer) -> Integer -> Bool
prop_appPreservedOnIdToList f x =
  idToList (MkId f <*> MkId x) == (idToList (MkId f) <*> idToList (MkId x))

||| Verifies that morph preserves pure on Maybe to Multiset BoxInt at runtime.
public export
prop_purePreservedOnMaybeToMultiset : Integer -> Bool
prop_purePreservedOnMaybeToMultiset x =
  maybeToMultiset (pure {f=Maybe} x) == pure {f=Multiset BoxInt} x

||| Verifies that morph preserves pure on Id to Multiset BoxInt at runtime.
public export
prop_purePreservedOnIdToMultiset : Integer -> Bool
prop_purePreservedOnIdToMultiset x =
  idToMultiset (pure {f=Id} x) == pure {f=Multiset BoxInt} x

||| Converts an Identity context into a Maybe passband.
public export
idToMaybe : Id a -> Maybe a
idToMaybe (MkId y) = Just y

public export
ApplicativeHomomorphism Id Maybe where
  morph = idToMaybe

  purePreserved x = Refl

  appPreserved (MkId f) (MkId x) = Refl

||| Verifies that composed homomorphism morphing Id -> Maybe -> Multiset BoxInt preserves pure.
public export
prop_purePreservedOnComposedIdMaybeMultiset : Integer -> Bool
prop_purePreservedOnComposedIdMaybeMultiset x =
  let compMorph = composeHom {f=Id} {g=Maybe} {h=Multiset BoxInt} idToMaybe maybeToMultiset
  in compMorph (pure {f=Id} x) == pure {f=Multiset BoxInt} x




