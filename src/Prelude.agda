{-# OPTIONS --rewriting #-}

open import Agda.Primitive public
open import Relation.Binary.Core public using (_≡_ ; _≢_ ; refl)
open import Relation.Binary.HeterogeneousEquality public using (_≅_; refl ; ≅-to-≡)
open import Data.Product
open import Function using (_∘_)

 -- Equal functions applied to equal arguments yield equal results.
_=$=_ : {n m : Level} {A : Set n} {B : Set m} {f g : A -> B} {a1 a2 : A} (p : f ≡ g) (q : a1 ≡ a2) -> (f a1) ≡ (g a2)
refl =$= refl = refl

-- A function applied to equal arguments yields equal results.
_$=_ : {n m : Level} {A : Set n} {B : Set m} {a1 a2 : A} (f : A -> B) (q : a1 ≡ a2) -> (f a1) ≡ (f a2)
f $= refl = refl

_=$_ : {n m : Level} {A : Set n} {B : A -> Set m} {f g : (a : A) -> B a} (p : f ≡ g) (a : A) -> (f a) ≡ (g a)
refl =$ a = refl

-- Transitivity of equality.
_=>>=_ : {n : Level} {A : Set n} {a b c : A} (p : a ≡ b) (q : b ≡ c) -> (a ≡ c)
refl =>>= q = q

_~$~_ : {n m : Level} {A : Set n} {B : A -> Set m} {f g : (a : A) -> B a} {a1 a2 : A} (p : f ≅ g) (q : a1 ≅ a2) -> (f a1) ≅ (g a2)
refl ~$~ refl = refl

_$~_ : {n m : Level} {A : Set n} {B : A -> Set m} (f : (a : A) -> B a) {a1 a2 : A} (q : a1 ≅ a2) -> (f a1) ≅ (f a2)
f $~ refl = refl

_~$_ : {n m : Level} {A : Set n} {B : A -> Set m} {f g : (a : A) -> B a} (p : f ≅ g) (a : A) -> (f a) ≅ (g a)
refl ~$ a = refl

_~$'_ : {n m : Level} {A : Set n} {B : A -> Set m} {f g : {a : A} -> B a} (p : (λ {a} -> f {a}) ≅ (λ {a} -> g {a})) (a : A) -> (f {a}) ≅ (g {a})
refl ~$' a = refl

_=,=_ : {n m : Level} {A : Set n} {B : Set m} {a1 a2 : A} {b1 b2 : B} -> a1 ≡ a2 -> b1 ≡ b2 -> (a1 , b1) ≡ (a2 , b2)
refl =,= refl = refl

infixl 20 _=$=_
infixl 20 _$=_
infixl 20 _=$_
infixl 19 _=>>=_
infixl 20 _~$~_
infixl 20 _$~_
infixl 20 _~$_

-- Symmetry of equality.
flipEq : {n : Level} {A : Set n} {a b : A} (p : a ≡ b) -> b ≡ a
flipEq refl = refl

flipEq-involution : {n : Level} {A : Set n} {a b : A} {p : a ≡ b} -> flipEq (flipEq p) ≡ p
flipEq-involution {p = refl} = refl

coerce : {n : Level} {A B : Set n} -> A ≡ B -> A -> B
coerce refl a = a

eqUnicity : {n : Level} {A : Set n} {a b : A} {p q : a ≡ b} -> p ≡ q
eqUnicity {p = refl} {q = refl} = refl

hetero : {l : Level} {A : Set l} {a b : A} -> a ≡ b -> a ≅ b
hetero refl = refl

assoc-=>>= : {a : Level} {A : Set a} {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} ->
             p =>>= (q =>>= r) ≡ (p =>>= q) =>>= r
assoc-=>>= = eqUnicity

-- Note: Don't need the symmetric left identity rewrite rule, since that one is computational.
r-id-=>>= : {a : Level} {A : Set a} {x y : A} {p : x ≡ y} -> p =>>= refl ≡ p
r-id-=>>= = eqUnicity

l-id-$= : {a : Level} {A : Set a} {x y : A} {p : x ≡ y} -> (λ x -> x) $= p ≡ p
l-id-$= = eqUnicity

distr-$=-=>>= : {a b : Level} {A : Set a} {B : Set b} {x y z : A} {f : A -> B} {p : x ≡ y} {q : y ≡ z} ->
                f $= (p =>>= q) ≡ (f $= p) =>>= (f $= q)
distr-$=-=>>= = eqUnicity

join-$= : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} {x y : A} {f : B -> C} {g : A -> B} {p : x ≡ y} ->
          f $= (g $= p) ≡ (f ∘ g) $= p
join-$= = eqUnicity

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE r-id-=>>= #-}
{-# REWRITE assoc-=>>= #-}
{-# REWRITE l-id-$= #-}
{-# REWRITE distr-$=-=>>= #-}
{-# REWRITE join-$= #-}

postulate
  extensionality : {k l : Level} {A : Set k} {B : A -> Set l} {f g : (a : A) -> B a} ->
                   ((a : A) -> (f a) ≡ (g a)) -> f ≡ g

extensionality' : {k l : Level} {A : Set k} {B : A -> Set l} {f g : {a : A} -> B a} ->
                 ({a : A} -> (f {a}) ≡ (g {a})) -> (_≡_ {_} { {a : A} -> B a } f g)
extensionality' {f = f} {g = g} ev = (λ h -> λ {a} -> h a) $= extensionality (λ a -> ev {a})

data Singleton {ℓ : _} {A : Set ℓ} : A -> Set where
  just : (a : A) -> Singleton a

data Doubleton {ℓ : _} {A : Set ℓ} : A -> A -> Set where
  inl : (a : A) {b : A} -> Doubleton a b
  inr : {a : A} (b : A) -> Doubleton a b
