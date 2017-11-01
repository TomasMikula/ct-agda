open import Function hiding (id ; _∘_)
open import Data.Product
open import Prelude
open import category

-- Some special morphisms.
module morphisms {k l : Level} (𝒞 : Category k l) where
  open Category 𝒞
  
  record Mono {A B : Obj} (f : Hom A B) : Set (k ⊔ l) where
    constructor mono
    field
      elimL : { X : Obj } {g h : Hom X A} -> ((f ∘ g) ≡ (f ∘ h)) -> (g ≡ h)

  record Epi {A B : Obj} (f : Hom A B) : Set (l ⊔ k) where
    constructor epi
    field
      elimR : { X : Obj } {g h : Hom B X} -> ((g ∘ f) ≡ (h ∘ f)) -> (g ≡ h)
    
  record Section {A B : Obj} (s : Hom A B) : Set l where
    field
      retraction : Hom B A
      evidence : (retraction ∘ s) ≡ id

  record Retraction {A B : Obj} (r : Hom A B) : Set l where
    field
      section : Hom B A
      evidence : (r ∘ section) ≡ id

  record Iso {A B : Obj} (f : Hom A B) : Set l where
    field
      inverse : Hom B A
      leftInverse  : (inverse ∘ f) ≡ id
      rightInverse : (f ∘ inverse) ≡ id

  record ExtremalMono {A B : Obj} (m : Hom A B) : Set (k ⊔ l) where
    field
      monic : Mono m
      extremal : {X : Obj} (f : Hom X B) (e : Hom A X) -> m ≡ f ∘ e -> Epi e -> Iso e

  orthogonal : {A B C D : Obj} (f : Hom A B) (g : Hom C D) -> Set l
  orthogonal {A} {B} {C} {D} f g =
    (u : Hom A C) (v : Hom B D) -> (v ∘ f) ≡ (g ∘ u) -> ∃[ w ] ((v ≡ g ∘ w) × (u ≡ w ∘ f))

  record StrongMono {A B : Obj} (m : Hom A B) : Set (k ⊔ l) where
    field
      monic : Mono m
      strong : {C D : Obj} (e : Hom C D) -> Epi e -> orthogonal e m

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

  mono_composition :  {A B C : Obj} {f : Hom B C} {g : Hom A B} -> Mono f -> Mono g -> Mono (f ∘ g)
  mono_composition {f = f} {g = g} mf mg =
    mono λ {_} {α} {β} fgα=fgβ → g-elim (f-elim (assocRL =>>= fgα=fgβ =>>= assocLR))
      where f-elim = Mono.elimL mf ; g-elim = Mono.elimL mg

  epi_extrermal_mono_is_iso : {A B : Obj} {f : Hom A B} -> Epi f -> ExtremalMono f -> Iso f
  epi_extrermal_mono_is_iso {f = f} epi-f ext-f = extremal id f (flipEq left_id) epi-f
    where open ExtremalMono ext-f

  strong_mono_composition : {A B C : Obj} {f : Hom B C} {g : Hom A B} -> StrongMono f -> StrongMono g -> StrongMono (f ∘ g)
  strong_mono_composition {f = f} {g = g} sf sg =
    record { monic = mono_composition mono-f mono-g
           ; strong = strong }
    where
      open StrongMono sf renaming (monic to mono-f ; strong to strong-f)
      open StrongMono sg renaming (monic to mono-g ; strong to strong-g)

      strong : {C D : Obj} (e : Hom C D) → Epi e → orthogonal e (f ∘ g)
      strong e epi-e u v ve=fgu =
        case (strong-f e epi-e (g ∘ u) v (ve=fgu =>>= assocLR)) of
        λ { (w' , v=fw' , gu=w'e) →
            case (strong-g e epi-e u w' (flipEq gu=w'e)) of
            λ { (w , w'=gw , u=we) → (w , v=fw' =>>= ((f ∘_) $= w'=gw) =>>= assocRL , u=we) }
          }

  strong_mono_is_extremal : {A B : Obj} {m : Hom A B} -> StrongMono m -> ExtremalMono m
  strong_mono_is_extremal sm = record
    { monic = StrongMono.monic sm
    ; extremal = λ f e m=fe epi-e →
        case (StrongMono.strong sm e epi-e id f (flipEq (right_id =>>= m=fe))) of
        λ { (e⁻¹ , f=me⁻¹ , id=e⁻¹e) →
          epi_section_is_iso epi-e (record { retraction = e⁻¹ ; evidence = flipEq id=e⁻¹e })
        }
    }

  mono-decomposition : {A B C : Obj} (f : Hom B C) (g : Hom A B) -> Mono (f ∘ g) -> Mono g
  mono-decomposition f g mono-fg =
    mono (λ gα=gβ -> elimL (assocLR =>>= ((f ∘_) $= gα=gβ) =>>= assocRL))
    where open Mono mono-fg using (elimL)

  extremal-mono-decomposition : {A B C : Obj} (f : Hom B C) (g : Hom A B) -> ExtremalMono (f ∘ g) -> ExtremalMono g
  extremal-mono-decomposition f g ext-fg = record
    { monic = mono-decomposition f g mono-fg
    ; extremal = λ h e g=he epi-e → extremal-fg (f ∘ h) e ((f ∘_) $= g=he =>>= assocRL) epi-e
    } where
        open ExtremalMono ext-fg renaming (monic to mono-fg ; extremal to extremal-fg)

  strong-mono-decomposition : {A B C : Obj} (f : Hom B C) (g : Hom A B) -> StrongMono (f ∘ g) -> StrongMono g
  strong-mono-decomposition f g str-fg = record
    { monic = mono-decomposition f g mono-fg
    ; strong = λ e epi-e u v ve=gu →
        case (strong-fg e epi-e u (f ∘ v) (assocLR =>>= ((f ∘_) $= ve=gu) =>>= assocRL)) of
        λ { (w , fv=fgw , u=we) → (w , Epi.elimR epi-e (ve=gu =>>= ((g ∘_) $= u=we) =>>= assocRL) , u=we) }
    } where
        open StrongMono str-fg renaming (monic to mono-fg ; strong to strong-fg)
