open import Agda.Primitive
open import Relation.Binary.Core public using (_≡_; refl)

 -- Equal functions applied to equal arguments yield equal results.
_=$=_ : {n m : Level} {A : Set n} {B : Set m} {f g : A -> B} {a1 a2 : A} (p : f ≡ g) (q : a1 ≡ a2) -> (f a1) ≡ (g a2)
refl =$= refl = refl

-- A function applied to equal arguments yields equal results.
_$=_ : {n m : Level} {A : Set n} {B : Set m} {a1 a2 : A} (f : A -> B) (q : a1 ≡ a2) -> (f a1) ≡ (f a2)
f $= refl = refl

-- Transitivity of equality.
_=>>=_ : {n : Level} {A : Set n} {a b c : A} (p : a ≡ b) (q : b ≡ c) -> (a ≡ c)
refl =>>= refl = refl

infixl 20 _=$=_
infixl 20 _$=_
infixl 20 _=>>=_

-- Symmetry of equality.
flipEq : {n : Level} {A : Set n} {a b : A} (p : a ≡ b) -> b ≡ a
flipEq refl = refl

coerce : {n : Level} {A B : Set n} -> A ≡ B -> A -> B
coerce refl a = a
