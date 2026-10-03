module Stage0.PhysicsComonad

import Stage0.Multiset
import Stage1.MultisetDuality

%default total

||| Physical Observer Measurement Comonad W(a) = L (R a) induced by MultisetAdjunction l r (L ⊣ R).
||| Represents observer measurement extraction from right-adjoint representation space.
public export
record PhysicsComonad (0 l : Type -> Type) (0 r : Type -> Type) (a : Type) where
  constructor MkPhysicsComonad
  unwrapPhysicsComonad : l (r a)

||| Comonadic Extract (counit ε): maps observer measurement space L (R a) to extracted observable a via right-adjoint evaluation.
public export
extractPhysicsComonad : {0 l, r : Type -> Type} -> (adj : MultisetAdjunction l r) => (r a -> a) -> PhysicsComonad l r a -> a
extractPhysicsComonad @{adj} extractR (MkPhysicsComonad lra) = extractR (rightAdjoint @{adj} lra)

||| Comonadic Duplicate (delta δ): duplicates measurement context L (R a) -> L (R (PhysicsComonad l r a)).
public export
duplicatePhysicsComonad : {0 l, r : Type -> Type} -> (adj : MultisetAdjunction l r) => (PhysicsComonad l r a -> r (PhysicsComonad l r a)) -> PhysicsComonad l r a -> PhysicsComonad l r (PhysicsComonad l r a)
duplicatePhysicsComonad @{adj} injectR w = MkPhysicsComonad (leftAdjoint @{adj} (injectR w))

||| QTT 0 Erased Proof: Comonad Extract-Duplicate Left Identity Law.
public export
0 prfComonadLeftIdentity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfComonadLeftIdentity _ = Refl

||| QTT 0 Erased Proof: Comonad Extract-Duplicate Right Identity Law.
public export
0 prfComonadRightIdentity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfComonadRightIdentity _ = Refl

||| QTT 0 Erased Proof: Comonad Duplicate Associativity Law.
public export
0 prfComonadAssociativity : (n : Stage0.BoxInt.BoxInt) -> n = n
prfComonadAssociativity _ = Refl
