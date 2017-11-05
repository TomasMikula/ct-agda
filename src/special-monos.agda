open import Data.Product
open import Function using (case_of_)
open import Prelude
open import category

-- Some special monomorphisms
module special-monos {k l : Level} (𝒞 : Category k l) where
  open Category 𝒞
  open import morphisms 𝒞
  open import equalizers 𝒞

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

  record RegularMono {A B : Obj} (m : Hom A B) : Set (k ⊔ l) where
    constructor regularMono
    field
      C : Obj
      f : Hom B C
      g : Hom B C
      equ : Equalizer f g m

    monic : Mono m
    monic = equalizer_is_mono' equ

  pattern equalizerOf_and_provedBy_ {C} f g equ = regularMono C f g equ


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

  regular-mono-is-strong : {A B : Obj} {m : Hom A B} -> RegularMono m -> StrongMono m
  regular-mono-is-strong {m = m} rm@(equalizerOf α and β provedBy ((isEqualizing αm=βm) universally universality)) =
    record { monic = mono-m ; strong = strong-m } where
      mono-m = RegularMono.monic rm
      elim-m = Mono.elimL mono-m
      strong-m : {C D : Obj} (e : Hom C D) -> (Epi e) -> orthogonal e m
      strong-m e (epi elim-e) u v ve=mu = w-ev where
        αmu=βmu = assocRL =>>= ((_∘ u) $= αm=βm) =>>= assocLR
        αve=βve = assocLR =>>= ((α ∘_) $= ve=mu) =>>= αmu=βmu =>>= ((β ∘_) $= (flipEq ve=mu)) =>>= assocRL
        αv=βv = elim-e αve=βve
        w-ev = case (universality (isEqualizing αv=βv)) of 
          λ { ((reduceMorphismBy w witnessedBy mw=v) uniquely _) →
              w , flipEq mw=v , elim-m (flipEq ((_∘ e) $= mw=v =>>= ve=mu) =>>= assocLR)
            }
