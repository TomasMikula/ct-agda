open import Agda.Primitive
open import Prelude
open import category

-- Some special morphisms.
module morphisms {n m : Level} (𝒞 : Category {n} {m}) where
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
      p1 = (retraction ∘_) $= p
      p2 = assoc =>>= p1 =>>= flipEq assoc
      p3 = flipEq ((_∘ g) $= evidence) =>>= p2 =>>= ((_∘ h) $= evidence)
      p4 = flipEq left_id =>>= p3 =>>= left_id
    in p4 where
      open Section s

  retraction_is_epi : {A B : Obj} {f : Hom A B} -> Retraction f -> Epi f
  retraction_is_epi {f = f} r = epi λ {x} → λ {g} → λ {h} → λ p → 
    let
      p1 = (_∘ section) $= p
      p2 = flipEq assoc =>>= p1 =>>= assoc
      p3 = flipEq ((g ∘_) $= evidence) =>>= p2 =>>= ((h ∘_) $= evidence)
      p4 = flipEq right_id =>>= p3 =>>= right_id
    in p4 where
      open Retraction r

  iso_is_retraction : {A B : Obj} {f : Hom A B} -> Iso f -> Retraction f
  iso_is_retraction i = record { section = Iso.inverse i ; evidence = Iso.rightInverse i }

  iso_is_section : {A B : Obj} {f : Hom A B} -> Iso f -> Section f
  iso_is_section i = record { retraction = Iso.inverse i ; evidence = Iso.leftInverse i }

  mono_retraction_is_iso : {A B : Obj} {f : Hom A B} -> Mono f -> Retraction f -> Iso f
  mono_retraction_is_iso {f = f} m r =
    record
      { inverse = section
      ; leftInverse = elimL (flipEq assoc =>>= ((_∘ f) $= evidence) =>>= left_id =>>= flipEq right_id)
      ; rightInverse = evidence
      }
    where
      open Mono m
      open Retraction r

  epi_section_is_iso : {A B : Obj} {f : Hom A B} -> Epi f -> Section f -> Iso f
  epi_section_is_iso {f = f} e s =
    record
      { inverse = retraction
      ; leftInverse = evidence
      ; rightInverse = elimR (assoc =>>= ((f ∘_) $= evidence) =>>= right_id =>>= flipEq left_id)
      }
    where
      open Epi e
      open Section s
