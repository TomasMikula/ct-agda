open import Data.Product
open import Prelude
open import category
open import functor

open Category

record Injective {a b : Level} {A : Set a} {B : Set b} (f : A -> B) : Set (a ⊔ b) where
  constructor isInjective
  field injective : {x y : A} -> f x ≡ f y -> x ≡ y

record Surjective {a b : Level} {A : Set a} {B : Set b} (f : A -> B) : Set (a ⊔ b) where
  constructor isSurjective
  field surjective : {y : B} -> ∃[ x ] (f x ≡ y)

Bijective : {a b : Level} {A : Set a} {B : Set b} (f : A -> B) -> Set (a ⊔ b)
Bijective f = (Injective f) × (Surjective f)

record LeftInvertible {a b : Level} {A : Set a} {B : Set b} (f : A -> B) : Set (a ⊔ b) where
  constructor isLeftInertible
  field
    leftInverse : B -> A
    evidence : (λ a -> leftInverse (f a)) ≡ λ a -> a

record RightInvertible {a b : Level} {A : Set a} {B : Set b} (f : A -> B) : Set (a ⊔ b) where
  constructor isRightInertible
  field
    rightInverse : B -> A
    evidence : (λ b -> f (rightInverse b)) ≡ λ b -> b

record Invertible {a b : Level} {A : Set a} {B : Set b} (f : A -> B) : Set (a ⊔ b) where
  constructor isInvertible
  field
    inverse : B -> A
    leftInverse : (λ a -> inverse (f a)) ≡ λ a -> a
    rightInverse : (λ b -> f (inverse b)) ≡ λ b -> b

invertibleIsBijective : {a b : Level} {A : Set a} {B : Set b} {f : A -> B} -> Invertible f -> Bijective f
invertibleIsBijective (isInvertible g gf=id fg=id) =
  (isInjective λ fx=fy -> flipEq (gf=id =$ _) =>>= g $= fx=fy =>>= gf=id =$ _) ,
  (isSurjective λ {y} -> (g y , fg=id =$ y))

Faithful : ∀ {k l m n} {𝒞 : Category k l} {𝒟 : Category m n} (F : 𝒞 => 𝒟) -> Set (k ⊔ l ⊔ n)
Faithful {𝒞 = 𝒞} (functor _ Fm _ _) = {A B : Obj 𝒞} -> Injective (Fm {A} {B})

Full : ∀ {k l m n} {𝒞 : Category k l} {𝒟 : Category m n} (F : 𝒞 => 𝒟) -> Set (k ⊔ l ⊔ n)
Full {𝒞 = 𝒞} (functor _ Fm _ _) = {A B : Obj 𝒞} -> Surjective (Fm {A} {B})

FullyFaithful : ∀ {k l m n} {𝒞 : Category k l} {𝒟 : Category m n} (F : 𝒞 => 𝒟) -> Set (k ⊔ l ⊔ n)
FullyFaithful {𝒞 = 𝒞} (functor _ Fm _ _) = {A B : Obj 𝒞} -> (Surjective (Fm {A} {B})) × (Injective (Fm {A} {B}))

fullyFaithfulFromBijection : ∀ {k l m n} {𝒞 : Category k l} {𝒟 : Category m n} {F : 𝒞 => 𝒟} ->
                             ({A B : Obj 𝒞} -> Bijective (Functor.mapArr F {A} {B})) -> FullyFaithful F
fullyFaithfulFromBijection ε {A} {B} with ε {A} {B}
... | (inj , sur) = (sur , inj)

fullyFaithfulFromInvertible : ∀ {k l m n} {𝒞 : Category k l} {𝒟 : Category m n} {F : 𝒞 => 𝒟} ->
                              ({A B : Obj 𝒞} -> Invertible (Functor.mapArr F {A} {B})) -> FullyFaithful F
fullyFaithfulFromInvertible {F = F} ε =
  fullyFaithfulFromBijection {F = F} (λ {A B} -> invertibleIsBijective (ε {A} {B}))
