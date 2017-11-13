open import Function hiding (id ; _∘_)
open import Data.Product
open import Prelude
open import category

-- Some special morphisms.
module morphisms {k l : Level} (𝒞 : Category k l) where
  open Category 𝒞
  
  record Mono {A B : Obj} (f : Mph A B) : Set (k ⊔ l) where
    constructor mono
    field
      elimL : { X : Obj } {g h : Mph X A} -> ((f ∘ g) ≡ (f ∘ h)) -> (g ≡ h)

  record Epi {A B : Obj} (f : Mph A B) : Set (l ⊔ k) where
    constructor epi
    field
      elimR : { X : Obj } {g h : Mph B X} -> ((g ∘ f) ≡ (h ∘ f)) -> (g ≡ h)
    
  record Section {A B : Obj} (s : Mph A B) : Set l where
    constructor hasRetraction
    field
      retraction : Mph B A
      evidence : (retraction ∘ s) ≡ id

  record Retraction {A B : Obj} (r : Mph A B) : Set l where
    constructor hasSection
    field
      section : Mph B A
      evidence : (r ∘ section) ≡ id

  record Iso {A B : Obj} (f : Mph A B) : Set l where
    constructor iso
    field
      inverse : Mph B A
      leftInverse  : (inverse ∘ f) ≡ id
      rightInverse : (f ∘ inverse) ≡ id

    reverse : Iso inverse
    reverse = record { inverse = f ; leftInverse = rightInverse ; rightInverse = leftInverse }

  -- reduce f to g, via u
  record MorphismReduction {A B C : Obj} (f : Mph A C) (g : Mph B C) : Set l where
    constructor reduceMorphismBy_witnessedBy_
    field
      u : Mph A B
      ev : g ∘ u ≡ f

  composeMorphismReductions : {A B C D : Obj} {f : Mph A D} {g : Mph B D} {h : Mph C D} ->
                            MorphismReduction g h -> MorphismReduction f g -> MorphismReduction f h
  composeMorphismReductions (reduceMorphismBy u₂ witnessedBy hu₂=g) (reduceMorphismBy u₁ witnessedBy gu₁=f) =
    reduceMorphismBy (u₂ ∘ u₁) witnessedBy (assocRL =>>= ((_∘ u₁) $= hu₂=g) =>>= gu₁=f)

  identityMorphismReduction : {A B : Obj} (f : Mph A B) -> MorphismReduction f f
  identityMorphismReduction f = reduceMorphismBy id witnessedBy right_id

  record UniqueMorphismReduction {A B C : Obj} (f : Mph A C) (g : Mph B C) : Set l where
    constructor _uniquely_
    field
      reduction : MorphismReduction f g
      unique : (red₂ : MorphismReduction f g) -> MorphismReduction.u red₂ ≡ MorphismReduction.u reduction

    open MorphismReduction reduction public

  section_is_mono : {A B : Obj} {f : Mph A B} -> Section f -> Mono f
  section_is_mono {f = f} s = mono λ {x} → λ {g} → λ {h} → λ p → 
    let
      p1 = (retraction ∘_) $= p
      p2 = assoc =>>= p1 =>>= flipEq assoc
      p3 = flipEq ((_∘ g) $= evidence) =>>= p2 =>>= ((_∘ h) $= evidence)
      p4 = flipEq left_id =>>= p3 =>>= left_id
    in p4 where
      open Section s

  retraction_is_epi : {A B : Obj} {f : Mph A B} -> Retraction f -> Epi f
  retraction_is_epi {f = f} r = epi λ {x} → λ {g} → λ {h} → λ p → 
    let
      p1 = (_∘ section) $= p
      p2 = flipEq assoc =>>= p1 =>>= assoc
      p3 = flipEq ((g ∘_) $= evidence) =>>= p2 =>>= ((h ∘_) $= evidence)
      p4 = flipEq right_id =>>= p3 =>>= right_id
    in p4 where
      open Retraction r

  iso_is_retraction : {A B : Obj} {f : Mph A B} -> Iso f -> Retraction f
  iso_is_retraction i = record { section = Iso.inverse i ; evidence = Iso.rightInverse i }

  iso_is_section : {A B : Obj} {f : Mph A B} -> Iso f -> Section f
  iso_is_section i = record { retraction = Iso.inverse i ; evidence = Iso.leftInverse i }

  mono_retraction_is_iso : {A B : Obj} {f : Mph A B} -> Mono f -> Retraction f -> Iso f
  mono_retraction_is_iso {f = f} m r =
    record
      { inverse = section
      ; leftInverse = elimL (flipEq assoc =>>= ((_∘ f) $= evidence) =>>= left_id =>>= flipEq right_id)
      ; rightInverse = evidence
      }
    where
      open Mono m
      open Retraction r

  epi_section_is_iso : {A B : Obj} {f : Mph A B} -> Epi f -> Section f -> Iso f
  epi_section_is_iso {f = f} e s =
    record
      { inverse = retraction
      ; leftInverse = evidence
      ; rightInverse = elimR (assoc =>>= ((f ∘_) $= evidence) =>>= right_id =>>= flipEq left_id)
      }
    where
      open Epi e
      open Section s

  iso_composition : {A B C : Obj} {f : Mph B C} {g : Mph A B} -> Iso f -> Iso g -> Iso (f ∘ g)
  iso_composition {f = f} {g} (iso f⁻¹ f⁻¹f=id ff⁻¹=id) (iso g⁻¹ g⁻¹g=id gg⁻¹=id) =
    iso (g⁻¹ ∘ f⁻¹)
        (assocLR =>>= ((g⁻¹ ∘_) $= (assocRL =>>= ((_∘ g  ) $= f⁻¹f=id) =>>= left_id)) =>>= g⁻¹g=id)
        (assocLR =>>= ((f   ∘_) $= (assocRL =>>= ((_∘ f⁻¹) $= gg⁻¹=id) =>>= left_id)) =>>= ff⁻¹=id)

  mono_composition : {A B C : Obj} {f : Mph B C} {g : Mph A B} -> Mono f -> Mono g -> Mono (f ∘ g)
  mono_composition {f = f} {g = g} mf mg =
    mono λ {_} {α} {β} fgα=fgβ → g-elim (f-elim (assocRL =>>= fgα=fgβ =>>= assocLR))
      where f-elim = Mono.elimL mf ; g-elim = Mono.elimL mg

  mono-decomposition : {A B C : Obj} (f : Mph B C) (g : Mph A B) -> Mono (f ∘ g) -> Mono g
  mono-decomposition f g mono-fg =
    mono (λ gα=gβ -> elimL (assocLR =>>= ((f ∘_) $= gα=gβ) =>>= assocRL))
    where open Mono mono-fg using (elimL)
