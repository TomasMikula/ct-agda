open import Agda.Primitive
open import Relation.Binary.Core public using (_≡_; refl; _≢_)

_=$=_ : {n m : Level} {A : Set n} {B : Set m} {f g : A -> B} {a1 a2 : A} (p : f ≡ g) (q : a1 ≡ a2) -> (f a1) ≡ (g a2)
refl =$= refl = refl

_$=_ : {n m : Level} {A : Set n} {B : Set m} {a1 a2 : A} (f : A -> B) (q : a1 ≡ a2) -> (f a1) ≡ (f a2)
f $= refl = refl

_=>>=_ : {n : Level} {A : Set n} {a b c : A} (p : a ≡ b) (q : b ≡ c) -> (a ≡ c)
refl =>>= refl = refl

infixl 20 _=$=_
infixl 20 _$=_
infixl 20 _=>>=_

flipEq : {n : Level} {A : Set n} {a b : A} (p : a ≡ b) -> b ≡ a
flipEq refl = refl


record Category {n m : Level} : Set (lsuc (n ⊔ m)) where
  field
    Obj : Set n
    Hom : (A B : Obj) -> Set m
    
    id : { A : Obj } -> Hom A A
    _∘_  : { A B C : Obj } -> (Hom B C) -> (Hom A B) -> (Hom A C)
    
    left_id  : { A B : Obj } -> (f : Hom A B) -> (id ∘ f ≡ f)
    right_id : { A B : Obj } -> (f : Hom A B) -> (f ∘ id ≡ f)
    assoc : { A B C D : Obj } -> (f : Hom C D) -> (g : Hom B C) -> (h : Hom A B) -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

  _>>_ : { A B C : Obj } -> (Hom A B) -> (Hom B C) -> (Hom A C)
  f >> g  = g ∘ f


-- Category of sets and functions
Sets : Category
Sets = record
         { Obj = Set
         ; Hom = λ A B → (A -> B)
         ; id = λ x → x
         ; _∘_ = λ f g x → f (g x)

         ; left_id = λ f → refl
         ; right_id = λ f → refl
         ; assoc = λ f g h → refl
         }


module Morphisms {n m : Level} (𝒞 : Category {n} {m}) where
  open Category 𝒞
  
  record Mono {A B : Obj} (f : Hom A B) : Set (m ⊔ n) where
    constructor mono
    field
      elimL : { X : Obj } {g h : Hom X A} -> ((f ∘ g) ≡ (f ∘ h)) -> (g ≡ h)

  record Epi {A B : Obj} (f : Hom A B) : Set (m ⊔ n) where
    constructor epi
    field
      elimR : { X : Obj } {g h : Hom B X} -> ((g ∘ f) ≡ (h ∘ f)) -> (g ≡ h)
    
  record Section {A B : Obj} (s : Hom A B) : Set m where
    field
      retraction : Hom B A
      evidence : (retraction ∘ s) ≡ id

  record Retraction {A B : Obj} (r : Hom A B) : Set m where
    field
      section : Hom B A
      evidence : (r ∘ section) ≡ id

  record Iso {A B : Obj} (f : Hom A B) : Set m where
    field
      inverse : Hom B A
      leftInverse  : (inverse ∘ f) ≡ id
      rightInverse : (f ∘ inverse) ≡ id

  section_is_mono : {A B : Obj} {f : Hom A B} -> Section f -> Mono f
  section_is_mono {f = f} s = mono λ {x} → λ {g} → λ {h} → λ p → 
    let
      p1 = (λ fg -> retraction ∘ fg) $= p
      p2 = (assoc _ _ _) =>>= p1 =>>= flipEq (assoc _ _ _)
      p3 = flipEq ((λ i -> i ∘ g) $= evidence) =>>= p2 =>>= ((λ i -> i ∘ h) $= evidence)
      p4 = flipEq (left_id _) =>>= p3 =>>= (left_id _)
    in p4 where
      open Section s

  retraction_is_epi : {A B : Obj} {f : Hom A B} -> Retraction f -> Epi f
  retraction_is_epi {f = f} r = epi λ {x} → λ {g} → λ {h} → λ p → 
    let
      p1 = (λ gf -> gf ∘ section) $= p
      p2 = flipEq (assoc _ _ _) =>>= p1 =>>= (assoc _ _ _)
      p3 = flipEq ((λ i -> g ∘ i) $= evidence) =>>= p2 =>>= ((λ i -> h ∘ i) $= evidence)
      p4 = flipEq (right_id _) =>>= p3 =>>= (right_id _)
    in p4 where
      open Retraction r

  iso_is_retraction : {A B : Obj} {f : Hom A B} -> Iso f -> Retraction f
  iso_is_retraction i = record { section = Iso.inverse i ; evidence = Iso.rightInverse i }

  iso_is_section : {A B : Obj} {f : Hom A B} -> Iso f -> Section f
  iso_is_section i = record { retraction = Iso.inverse i ; evidence = Iso.leftInverse i }

  mono_retraction_is_iso : {A B : Obj} {f : Hom A B} -> Mono f -> Retraction f -> Iso f
  mono_retraction_is_iso {f = f} m r =
    record { inverse = section
           ; leftInverse = elimL (flipEq (assoc _ _ _) =>>= ((λ i -> i ∘ f) $= evidence) =>>= left_id f =>>= flipEq (right_id f))
           ; rightInverse = evidence
           }
    where
      open Mono m
      open Retraction r

  epi_section_is_iso : {A B : Obj} {f : Hom A B} -> Epi f -> Section f -> Iso f
  epi_section_is_iso {f = f} e s =
    record { inverse = retraction
           ; leftInverse = evidence
           ; rightInverse = elimR ((assoc _ _ _) =>>= ((λ i -> f ∘ i) $= evidence) =>>= right_id f =>>= flipEq (left_id f))
           }
    where
      open Epi e
      open Section s
