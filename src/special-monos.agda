open import Data.Product
open import Function using (case_of_)
open import Prelude
open import category
open import patterns

-- Some special monomorphisms
module special-monos {k l : Level} (𝒞 : Category k l) where
  open Category 𝒞
  open import morphisms 𝒞
  open import equalizers 𝒞

  record ExtremalMono {A B : Obj} (m : Mph A B) : Set (k ⊔ l) where
    constructor isMonic_andExtremal_
    field
      monic : Mono m
      extremal : {X : Obj} (f : Mph X B) (e : Mph A X) -> m ≡ f ∘ e -> Epi e -> Iso e

  orthogonal : {A B C D : Obj} (f : Mph A B) (g : Mph C D) -> Set l
  orthogonal {A} {B} {C} {D} f g =
    (u : Mph A C) (v : Mph B D) -> (v ∘ f) ≡ (g ∘ u) -> ∃[ w ] ((v ≡ g ∘ w) × (u ≡ w ∘ f))

  record StrongMono {A B : Obj} (m : Mph A B) : Set (k ⊔ l) where
    constructor isMonic_andStrong_
    field
      monic : Mono m
      strong : {C D : Obj} (e : Mph C D) -> Epi e -> orthogonal e m

  record RegularMono {A B : Obj} (m : Mph A B) : Set (k ⊔ l) where
    constructor regularMono
    field
      C : Obj
      f : Mph B C
      g : Mph B C
      equ : Equalizer f g m

    monic : Mono m
    monic = equalizer_is_mono' equ

  pattern equalizerOf_and_provedBy_ {C} f g equ = regularMono C f g equ


  epi_extrermal_mono_is_iso : {A B : Obj} {f : Mph A B} -> Epi f -> ExtremalMono f -> Iso f
  epi_extrermal_mono_is_iso {f = f} epi-f ext-f = extremal id f (flipEq left-id) epi-f
    where open ExtremalMono ext-f

  strong-mono-composition : {A B C : Obj} {f : Mph B C} {g : Mph A B} -> StrongMono f -> StrongMono g -> StrongMono (f ∘ g)
  strong-mono-composition {f = f} {g = g} sf sg =
    record { monic = mono-composition mono-f mono-g
           ; strong = strong }
    where
      open StrongMono sf renaming (monic to mono-f ; strong to strong-f)
      open StrongMono sg renaming (monic to mono-g ; strong to strong-g)

      strong : {C D : Obj} (e : Mph C D) → Epi e → orthogonal e (f ∘ g)
      strong e epi-e u v ve=fgu =
        case (strong-f e epi-e (g ∘ u) v (ve=fgu =>>= assocLR)) of
        λ { (w' , v=fw' , gu=w'e) →
            case (strong-g e epi-e u w' (flipEq gu=w'e)) of
            λ { (w , w'=gw , u=we) → (w , v=fw' =>>= ((f ∘_) $= w'=gw) =>>= assocRL , u=we) }
          }

  strong-mono-is-extremal : {A B : Obj} {m : Mph A B} -> StrongMono m -> ExtremalMono m
  strong-mono-is-extremal (isMonic mono-m andStrong strong-m) =
    isMonic mono-m
    andExtremal λ f e m=fe epi-e →
      case (strong-m e epi-e id f (flipEq (right-id =>>= m=fe))) of
      λ { (e⁻¹ , f=me⁻¹ , id=e⁻¹e) →
        epi-section-is-iso epi-e (record { retraction = e⁻¹ ; evidence = flipEq id=e⁻¹e })
      }

  extremal-mono-decomposition : {A B C : Obj} (f : Mph B C) (g : Mph A B) -> ExtremalMono (f ∘ g) -> ExtremalMono g
  extremal-mono-decomposition f g (isMonic mono-fg andExtremal extremal-fg) =
    isMonic (mono-decomposition f g mono-fg)
    andExtremal λ h e g=he epi-e → extremal-fg (f ∘ h) e ((f ∘_) $= g=he =>>= assocRL) epi-e

  strong-mono-decomposition : {A B C : Obj} (f : Mph B C) (g : Mph A B) -> StrongMono (f ∘ g) -> StrongMono g
  strong-mono-decomposition f g (isMonic mono-fg andStrong strong-fg) =
    isMonic mono-decomposition f g mono-fg
    andStrong λ e epi-e u v ve=gu →
      case (strong-fg e epi-e u (f ∘ v) (assocLR =>>= ((f ∘_) $= ve=gu) =>>= assocRL)) of
      λ { (w , fv=fgw , u=we) → (w , Epi.elimR epi-e (ve=gu =>>= ((g ∘_) $= u=we) =>>= assocRL) , u=we) }

  regular-mono-is-strong : {A B : Obj} {m : Mph A B} -> RegularMono m -> StrongMono m
  regular-mono-is-strong {m = m} rm@(equalizerOf α and β provedBy ((isEqualizing αm=βm) universally universality)) =
    isMonic mono-m andStrong strong-m where
      mono-m = RegularMono.monic rm
      elim-m = Mono.elimL mono-m
      strong-m : {C D : Obj} (e : Mph C D) -> (Epi e) -> orthogonal e m
      strong-m e (epi elim-e) u v ve=mu = w-ev where
        αmu=βmu = assocRL =>>= ((_∘ u) $= αm=βm) =>>= assocLR
        αve=βve = assocLR =>>= ((α ∘_) $= ve=mu) =>>= αmu=βmu =>>= ((β ∘_) $= (flipEq ve=mu)) =>>= assocRL
        αv=βv = elim-e αve=βve
        w-ev = case (universality (isEqualizing αv=βv)) of 
          λ { ((reduceMorphismBy w witnessedBy mw=v) uniquely _) →
              w , flipEq mw=v , elim-m (flipEq ((_∘ e) $= mw=v =>>= ve=mu) =>>= assocLR)
            }

  open import pushouts 𝒞
  module WithPushouts (pushout : {A A₁ A₂ : Obj} (a₁ : Mph A A₁) (a₂ : Mph A A₂) -> PushoutOf a₁ a₂) where
    extremal-mono-is-strong : {A B : Obj} {m : Mph A B} -> ExtremalMono m -> StrongMono m
    extremal-mono-is-strong {m = m} (isMonic mono-m @ (mono elim-m) andExtremal extremal-m) =
      isMonic mono-m
      andStrong λ e epi-e u v ve=mu → case pushout e u of λ { (pushoutData _ e' u' po@(isPushout e'u=u'e univ)) →
        case univ (commutingSquare (flipEq ve=mu)) of λ { ((reduceCospanBy h witnessedBy v=hu' and m=he') uniquely uniq) →
          case extremal-m h e' m=he' (pushout_of_epi_is_epi po epi-e) of λ { (iso e'⁻¹ (e'⁻¹e'=id , e'e'⁻¹=id)) →
            let
              w = e'⁻¹ ∘ u'
              h=me'⁻¹ = flipEq (((_∘ e'⁻¹) $= m=he') =>>= assocLR =>>= ((h ∘_) $= e'e'⁻¹=id) =>>= right-id)
              v=me'⁻¹u' = v=hu' =>>= ((_∘ u') $= h=me'⁻¹) =>>= assocLR
              u=e'⁻¹u'e = flipEq left-id =>>=((_∘ u) $= (flipEq e'⁻¹e'=id)) =>>= assocLR =>>= ((e'⁻¹ ∘_) $= e'u=u'e)
              u=e'⁻¹u'e = elim-m ((m ∘_) $= (u=e'⁻¹u'e =>>= assocRL))
            in w , v=me'⁻¹u' , u=e'⁻¹u'e
          }
        }
      }

    extremal-mono-composition : {A B C : Obj} {f : Mph B C} {g : Mph A B} -> ExtremalMono f -> ExtremalMono g -> ExtremalMono (f ∘ g)
    extremal-mono-composition ext-f ext-g =
      strong-mono-is-extremal (strong-mono-composition (extremal-mono-is-strong ext-f) (extremal-mono-is-strong ext-g))

    open import pullbacks 𝒞
    pulled-extremal-mono-is-extremal : {A B C : Obj} {m : Mph A C} {f : Mph B C}
                                       {P : Obj} {m' : Mph P B} {f' : Mph P A} ->
                                       Pullback m f m' f' -> ExtremalMono m -> ExtremalMono m'
    pulled-extremal-mono-is-extremal {A} {B} {C} {m} {f} {P} {m'} {f'} (pb @ (isPullback mf'=fm' univ-pb)) (isMonic mono-m andExtremal ext-m) =
      isMonic mono-m'
      andExtremal extremal-m'
        where
          rm-id : {D E F X : Obj} {r : Mph X E} {s : Mph E X} -> r ∘ s ≡ id -> (p : Mph E F) (q : Mph D E) -> (p ∘ r) ∘ (s ∘ q) ≡ p ∘ q
          rm-id rs=id p q = assocRL =>>= ((_∘ q) $= (assocLR =>>= ((p ∘_) $= rs=id) =>>= right-id))
          mono-m' = pullback_of_mono_is_mono pb mono-m
          extremal-m' : {X : Obj} (h' : Mph X B) (e' : Mph P X) -> m' ≡ h' ∘ e' -> Epi e' -> Iso e'
          extremal-m' h' e' m'=h'e' epi-e' with pushout e' f'
          ... | pushoutData _ e f'' po@(isPushout ef'=f''e' univ-po) with pushout_of_epi_is_epi po epi-e'
          ... | epi-e with mf'=fm' =>>= ((f ∘_) $= m'=h'e') =>>= assocRL
          ... | mf'=fh'e' with univ-po (commutingSquare mf'=fh'e')
          ... | (reduceCospanBy h witnessedBy fh'=hf'' and m=he) uniquely _ with ext-m h e m=he epi-e
          ... | iso e⁻¹ (e⁻¹e=id , ee⁻¹=id) with ((_∘ (e⁻¹ ∘ f'')) $= m=he) =>>= (rm-id ee⁻¹=id h f'') =>>= (flipEq fh'=hf'')
          ... | me⁻¹f''=fh' with univ-pb {f'' = h'} {g'' = e⁻¹ ∘ f''} (commutingSquare me⁻¹f''=fh')
          ... | (reduceSpanBy β witnessedBy f'β=e⁻¹f'' and m'β=h') uniquely _ with mono-m' | epi-e'
          ... | mono elim-m' | epi elim-e' = iso β (βe'=id , e'β=id) where
            βe'=id = elim-m' (assocRL =>>= ((_∘ e') $= m'β=h') =>>= (flipEq m'=h'e') =>>= (flipEq right-id))
            e'β=id = elim-e' (assocLR =>>= ((e' ∘_) $= βe'=id) =>>= right-id =>>= flipEq left-id)

    pulled-strong-mono-is-strong : {A B C : Obj} {m : Mph A C} {f : Mph B C}
                                   {P : Obj} {m' : Mph P B} {f' : Mph P A} ->
                                   Pullback m f m' f' -> StrongMono m -> StrongMono m'
    pulled-strong-mono-is-strong pb strong-m =
      extremal-mono-is-strong (pulled-extremal-mono-is-extremal pb (strong-mono-is-extremal strong-m))

    pulled-regular-mono-is-regular : {A B C : Obj} {m : Mph A C} {f : Mph B C}
                                     {P : Obj} {m' : Mph P B} {f' : Mph P A} ->
                                     Pullback m f m' f' -> RegularMono m -> RegularMono m'
    pulled-regular-mono-is-regular {A} {B} {C} {m} {f} {P} {m'} {f'}
                                   pb@(isPullback mf'=fm' univ-pb)
                                   reg-m@(regularMono D α β (isEqualizing αm=βm universally univ-m)) =
      regularMono D (α ∘ f) (β ∘ f) (isEqualizing αfm'=βfm' universally univ-m') where
        elim-m' = Mono.elimL (pullback_of_mono_is_mono pb (RegularMono.monic reg-m))

        αfm'=βfm' = assocLR =>>= ((α ∘_) $= flipEq mf'=fm') =>>= assocRL =>>= ((_∘ f') $= αm=βm) =>>= assocLR =>>= ((β ∘_) $= mf'=fm') =>>= assocRL

        univ-m' : {F : Obj} {φ : Mph F B} → Equalizing (α ∘ f) (β ∘ f) φ → UniqueMorphismReduction φ m'
        univ-m' {F} {φ} (isEqualizing αfφ=βfφ) with univ-m (isEqualizing (assocRL =>>= αfφ=βfφ =>>= assocLR))
        ... | (reduceMorphismBy ψ witnessedBy mψ=fφ) uniquely uniq-ψ with univ-pb (commutingSquare mψ=fφ)
        ... | (reduceSpanBy χ witnessedBy f'χ=ψ and m'χ=φ) uniquely uniq-χ =
          (reduceMorphismBy χ witnessedBy m'χ=φ) uniquely
            λ { (reduceMorphismBy χ' witnessedBy m'χ'=φ) → elim-m' (m'χ'=φ =>>= flipEq m'χ=φ) }
