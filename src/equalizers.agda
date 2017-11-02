open import Agda.Primitive
open import Data.Product
open import Prelude
open import category
import morphisms

module equalizers {n m : Level} (𝒞 : Category n m) where
  open Category 𝒞
  open morphisms 𝒞

  record Equalizing {A B : Obj} (f g : Hom A B) {E : Obj} (e : Hom E A) : Set (n ⊔ m) where
    constructor equalizing
    field
      evidence : f ∘ e ≡ g ∘ e

  record EqualizingReduction {A B : Obj} {f g : Hom A B} {E₂ E : Obj} {e₂ : Hom E₂ A} {e : Hom E A}
                             (eq₂ : Equalizing f g e₂) (eq : Equalizing f g e) : Set (n ⊔ m) where
    field
      u : Hom E₂ E
      ev : e ∘ u ≡ e₂

  composeEqualizingReductions : {A B : Obj} {f g : Hom A B}
                                {C : Obj} {ec : Hom C A} {eqc : Equalizing f g ec} ->
                                {D : Obj} {ed : Hom D A} {eqd : Equalizing f g ed} ->
                                {E : Obj} {ee : Hom E A} {eqe : Equalizing f g ee} ->
                                EqualizingReduction eqd eqe -> EqualizingReduction eqc eqd ->
                                EqualizingReduction eqc eqe
  composeEqualizingReductions de cd =
    record
      { u = u_de ∘ u_cd
      ; ev = flipEq assoc =>>= ((_∘ u_cd) $= ev_de) =>>= ev_cd
      }
    where
      open EqualizingReduction de renaming (u to u_de ; ev to ev_de)
      open EqualizingReduction cd renaming (u to u_cd ; ev to ev_cd)

  identityEqualizingReduction : {A B E : Obj} {f g : Hom A B} {e : Hom E A} (eq : Equalizing f g e) -> EqualizingReduction eq eq
  identityEqualizingReduction eq = record { u = id ; ev = right_id }

  record UniqueEqualizingReduction {A B : Obj} {f g : Hom A B}
                                   {E₂ : Obj} {e₂ : Hom E₂ A} (eq₂ : Equalizing f g e₂)
                                   {E₁ : Obj} {e₁ : Hom E₁ A} (eq₁ : Equalizing f g e₁) : Set (n ⊔ m) where
    field
      reduction : EqualizingReduction eq₂ eq₁
      unique : (red₂ : EqualizingReduction eq₂ eq₁) -> EqualizingReduction.u red₂ ≡ EqualizingReduction.u reduction

    u = EqualizingReduction.u reduction
    ev = EqualizingReduction.ev reduction

  record Equalizer {A B E : Obj} (f g : Hom A B) (e : Hom E A) : Set (n ⊔ m) where
    field
      cone : Equalizing f g e
      universal : {E₂ : Obj} {e₂ : Hom E₂ A} (eq₂ : Equalizing f g e₂) -> UniqueEqualizingReduction eq₂ cone

    open Equalizing cone public

    reduceCone : {E₂ : Obj} {e₂ : Hom E₂ A} (eq2 : Equalizing f g e₂) -> EqualizingReduction eq2 cone
    reduceCone eq2 = reduction where open UniqueEqualizingReduction (universal eq2)

    proveId : (red : EqualizingReduction cone cone) -> EqualizingReduction.u red ≡ id
    proveId red =
      let
        open UniqueEqualizingReduction (universal cone)
        u_id = unique (identityEqualizingReduction cone)
        u_red = unique red
      in u_red =>>= flipEq u_id

  record EqualizerOf {A B : Obj} (f g : Hom A B) : Set (n ⊔ m) where
    field
      E : Obj
      e : Hom E A
      equalizer : Equalizer f g e

    open Equalizer equalizer public

  idEqualizer : {A B : Obj} {f g : Hom A B} -> f ≡ g -> Equalizer f g id
  idEqualizer {A} f=g =
    record
      { cone = equalizing ((_∘ id) $= f=g)
      ; universal =
        λ { {_} {e₂} _ → record
            { reduction = record { u = e₂ ; ev = left_id }
            ; unique = λ { record { u = u ; ev = id∘u=e₂ } → flipEq left_id =>>= id∘u=e₂ }
            }
          }
      }

  idEqualizerOf : {A B : Obj} {f g : Hom A B} -> f ≡ g -> EqualizerOf f g
  idEqualizerOf f=g = record { E = _ ; e = id ; equalizer = idEqualizer f=g }

  equalizer_uniqueness : {A B : Obj} {f g : Hom A B} (e1 e2 : EqualizerOf f g) -> Σ (EqualizingReduction (EqualizerOf.cone e1) (EqualizerOf.cone e2)) (λ red -> Iso (EqualizingReduction.u red))
  equalizer_uniqueness e1 e2 =
    let
      open EqualizerOf e1 renaming (cone to cone1 ; reduceCone to redEq1 ; proveId to proveId1)
      open EqualizerOf e2 renaming (cone to cone2 ; reduceCone to redEq2 ; proveId to proveId2)

      r12 : EqualizingReduction cone1 cone2
      r12 = redEq2 cone1

      r21 : EqualizingReduction cone2 cone1
      r21 = redEq1 cone2

      u21 = EqualizingReduction.u r21
    in r12 , record
               { inverse = u21
               ; leftInverse  = proveId1 (composeEqualizingReductions r21 r12)
               ; rightInverse = proveId2 (composeEqualizingReductions r12 r21)
               }


  equalizer_is_mono : {A B : Obj} {f g : Hom A B} (eq : EqualizerOf f g) -> Mono (EqualizerOf.e eq)
  equalizer_is_mono {f = f} {g = g} eq = mono λ {X α β} eα=eβ →
    let
      open EqualizerOf eq renaming (evidence to fe=ge)

      feβ=geβ : f ∘ (e ∘ β) ≡ g ∘ (e ∘ β)
      feβ=geβ = flipEq assoc =>>= ((_∘ β) $= fe=ge) =>>= assoc

      eqβ : Equalizing f g (e ∘ β)
      eqβ = equalizing feβ=geβ

      redα : EqualizingReduction eqβ cone
      redα = record { u = α ; ev = eα=eβ }

      redβ : EqualizingReduction eqβ cone
      redβ = record { u = β ; ev = refl }

      open UniqueEqualizingReduction (universal eqβ)
      α=u = unique redα
      β=u = unique redβ
    in α=u =>>= flipEq β=u

  epi_equalizer_is_iso : {A B : Obj} {f g : Hom A B} (eq : EqualizerOf f g) -> Epi (EqualizerOf.e eq) -> Iso (EqualizerOf.e eq)
  epi_equalizer_is_iso {f = f} {g = g} eq isEpi =
    let
      open EqualizerOf eq renaming (evidence to fe=ge)

      f=g = Epi.elimR isEpi fe=ge

      idEq : Equalizing f g id
      idEq = equalizing ((_∘ id) $= f=g)

      id_to_eq : EqualizingReduction idEq cone
      id_to_eq = UniqueEqualizingReduction.reduction (universal idEq)

      r : Retraction e
      r = record
            { section = EqualizingReduction.u id_to_eq
            ; evidence = EqualizingReduction.ev id_to_eq
            }
    in mono_retraction_is_iso (equalizer_is_mono eq) r

  -- A different proof of the same fact.
  epi_equalizer_is_iso' : {A B : Obj} {f g : Hom A B} (eq : EqualizerOf f g) -> Epi (EqualizerOf.e eq) -> Iso (EqualizerOf.e eq)
  epi_equalizer_is_iso' {f = f} {g = g} eq isEpi =
    let
      open EqualizerOf eq using (e) renaming (cone to eCone ; evidence to fe=ge)

      f=g = Epi.elimR isEpi fe=ge

      idEq : EqualizerOf f g
      idEq = idEqualizerOf f=g

      open EqualizerOf idEq hiding (e) renaming (universal to idUniversal)
      open UniqueEqualizingReduction (idUniversal eCone) renaming (reduction to red ; unique to redUnique)

      open Σ (equalizer_uniqueness eq idEq) renaming (proj₁ to red' ; proj₂ to iso_red')
      u_red'=u_red = redUnique red'
      u_red=e = flipEq (redUnique (record { u = e ; ev = left_id }))
      u_red'=e = u_red'=u_red =>>= u_red=e
    in coerce (Iso $= u_red'=e) iso_red'

  section_is_equalizer : {A B : Obj} {s : Hom A B} (sec : Section s) -> Equalizer (s ∘ Section.retraction sec) id s
  section_is_equalizer {A} {B} {s} record { retraction = r ; evidence = rs=id } =
    record
      { cone = equalizing (assoc =>>= ((s ∘_) $= rs=id) =>>= right_id =>>= flipEq left_id)
      ; universal = λ { {E₂} {e₂} (equalizing sre=e) → record
                        { reduction = record
                          { u = r ∘ e₂
                          ; ev = flipEq assoc =>>= sre=e =>>= left_id
                          }
                        ; unique = λ { record { u = u ; ev = su=e₂ } → 
                            flipEq left_id =>>= ((_∘ u) $= (flipEq rs=id)) =>>= assoc =>>= ((r ∘_) $= su=e₂) }
                        }
                      }
      }
