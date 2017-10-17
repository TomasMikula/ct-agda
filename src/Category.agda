open import Agda.Primitive
open import Relation.Binary.Core public using (_≡_; refl; _≢_)

_=$=_ : {n m : Level} { A : Set n } { B : Set m } { f g : A -> B } { a1 a2 : A } (p : f ≡ g) (q : a1 ≡ a2) -> (f a1) ≡ (g a2)
refl =$= refl = refl

_$=_ : {n m : Level} { A : Set n } { B : Set m } { a1 a2 : A } (f : A -> B) (q : a1 ≡ a2) -> (f a1) ≡ (f a2)
f $= refl = refl

_=>>=_ : {n : Level} {A : Set n} {a b c : A} (p : a ≡ b) (q : b ≡ c) -> (a ≡ c)
refl =>>= refl = refl

infixl 20 _=$=_
infixl 20 _$=_
infixl 20 _=>>=_

flipEq : {n : Level} {A : Set n} {a b : A} (p : a ≡ b) -> b ≡ a
flipEq refl = refl

record Category { n m : Level } : Set (lsuc (n ⊔ m)) where
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


record Mono { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } (f : Category.Hom 𝒞 A B) : Set (m ⊔ n) where
  constructor mono
  open Category 𝒞
  field
    elimL : { X : Obj } {g h : Hom X A} -> ((f ∘ g) ≡ (f ∘ h)) -> (g ≡ h)

record Epi { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } (f : Category.Hom 𝒞 A B) : Set (m ⊔ n) where
  constructor epi
  open Category 𝒞
  field
    elimR : { X : Obj } {g h : Hom B X} -> ((g ∘ f) ≡ (h ∘ f)) -> (g ≡ h)
    
record Section { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } (s : Category.Hom 𝒞 A B) : Set m where
  open Category 𝒞
  field
    retraction : Hom B A
    evidence : (retraction ∘ s) ≡ id

record Retraction { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } (r : Category.Hom 𝒞 A B) : Set m where
  open Category 𝒞
  field
    section : Hom B A
    evidence : (r ∘ section) ≡ id

record Iso { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } (f : Category.Hom 𝒞 A B) : Set m where
  open Category 𝒞
  field
    inverse : Hom B A
    leftInverse  : (inverse ∘ f) ≡ id
    rightInverse : (f ∘ inverse) ≡ id

section_is_mono : { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } { f : Category.Hom 𝒞 A B } (s : Section {n} {m} {𝒞} {A} {B} f) -> Mono {n} {m} {𝒞} {A} {B} f
section_is_mono {𝒞 = c} {A} {B} {f} s = mono λ {x} → λ {g} → λ {h} → λ p → 
  let
    p1 = (λ fg -> retraction ∘ fg) $= p
    p2 = (assoc _ _ _) =>>= p1 =>>= flipEq (assoc _ _ _)
    p3 = flipEq ((λ i -> i ∘ g) $= evidence) =>>= p2 =>>= ((λ i -> i ∘ h) $= evidence)
    p4 = flipEq (left_id _) =>>= p3 =>>= (left_id _)
  in p4
  where
  open Category c
  open Section s

retraction_is_epi : { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } { f : Category.Hom 𝒞 A B } -> (Retraction {n} {m} {𝒞} {A} {B} f) -> Epi {n} {m} {𝒞} {A} {B} f
retraction_is_epi {𝒞 = c} {A} {B} {f} r = epi λ {x} → λ {g} → λ {h} → λ p → 
  let
    p1 = (λ gf -> gf ∘ section) $= p
    p2 = flipEq (assoc _ _ _) =>>= p1 =>>= (assoc _ _ _)
    p3 = flipEq ((λ i -> g ∘ i) $= evidence) =>>= p2 =>>= ((λ i -> h ∘ i) $= evidence)
    p4 = flipEq (right_id _) =>>= p3 =>>= (right_id _)
  in p4 where
  open Category c
  open Retraction r

iso_is_retraction : { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } { f : Category.Hom 𝒞 A B } -> (Iso {n} {m} {𝒞} {A} {B} f) -> Retraction {n} {m} {𝒞} {A} {B} f
iso_is_retraction i = record { section = Iso.inverse i ; evidence = Iso.rightInverse i }

iso_is_section : { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } { f : Category.Hom 𝒞 A B } -> (Iso {n} {m} {𝒞} {A} {B} f) -> Section {n} {m} {𝒞} {A} {B} f
iso_is_section i = record { retraction = Iso.inverse i ; evidence = Iso.leftInverse i }

mono_retraction_is_iso : { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } { f : Category.Hom 𝒞 A B } -> (Mono {n} {m} {𝒞} {A} {B} f) -> (Retraction {n} {m} {𝒞} {A} {B} f) -> Iso {n} {m} {𝒞} {A} {B} f
mono_retraction_is_iso {𝒞 = c} {A} {B} {f} m r =
  record { inverse = section
         ; leftInverse = elimL (flipEq (assoc _ _ _) =>>= ((λ i -> i ∘ f) $= evidence) =>>= left_id f =>>= flipEq (right_id f))
         ; rightInverse = evidence
         }
  where
    open Category c
    open Mono m
    open Retraction r

epi_section_is_iso : { n m : Level } { 𝒞 : Category {n} {m} } { A B : Category.Obj 𝒞 } { f : Category.Hom 𝒞 A B } -> (Epi {n} {m} {𝒞} {A} {B} f) -> (Section {n} {m} {𝒞} {A} {B} f) -> Iso {n} {m} {𝒞} {A} {B} f
epi_section_is_iso {𝒞 = c} {A} {B} {f} e s =
  record { inverse = retraction
         ; leftInverse = evidence
         ; rightInverse = elimR ((assoc _ _ _) =>>= ((λ i -> f ∘ i) $= evidence) =>>= right_id f =>>= flipEq (left_id f))
         }
  where
    open Category c
    open Epi e
    open Section s
