open import Data.Product
open import Function using (case_of_)
open import Prelude
open import category
import morphisms

module equalizers {n m : Level} (𝒞 : Category n m) where
  open Category 𝒞
  open morphisms 𝒞

  record Equalizing {A B : Obj} (f g : Mph A B) {E : Obj} (e : Mph E A) : Set (n ⊔ m) where
    constructor isEqualizing
    field
      evidence : f ∘ e ≡ g ∘ e

  record Equalizer {A B E : Obj} (f g : Mph A B) (e : Mph E A) : Set (n ⊔ m) where
    constructor _universally_
    field
      cone : Equalizing f g e
      universal : {E₂ : Obj} {e₂ : Mph E₂ A} (eq₂ : Equalizing f g e₂) -> UniqueMorphismReduction e₂ e

    open Equalizing cone public

    reduceCone : {E₂ : Obj} {e₂ : Mph E₂ A} (eq2 : Equalizing f g e₂) -> MorphismReduction e₂ e
    reduceCone eq2 = UniqueMorphismReduction.reduction (universal eq2)

    proveId : (red : MorphismReduction e e) -> MorphismReduction.u red ≡ id
    proveId red = u=red =>>= flipEq u=id
      where
        open UniqueMorphismReduction (universal cone) using (unique)
        u=id = unique (identityMorphismReduction e)
        u=red = unique red

  record EqualizerOf {A B : Obj} (f g : Mph A B) : Set (n ⊔ m) where
    constructor equalizerData
    field
      E : Obj
      e : Mph E A
      equalizer : Equalizer f g e

    open Equalizer equalizer public

  idEqualizer : {A B : Obj} {f g : Mph A B} -> f ≡ g -> Equalizer f g id
  idEqualizer {A} f=g =
    record
      { cone = isEqualizing ((_∘ id) $= f=g)
      ; universal =
        λ { {_} {e₂} _ → record
            { reduction = reduceMorphismBy e₂ witnessedBy left_id
            ; unique = λ { (reduceMorphismBy u witnessedBy id∘u=e₂) → flipEq left_id =>>= id∘u=e₂ }
            }
          }
      }

  idEqualizerOf : {A B : Obj} {f g : Mph A B} -> f ≡ g -> EqualizerOf f g
  idEqualizerOf f=g = record { E = _ ; e = id ; equalizer = idEqualizer f=g }

  equalizer_uniqueness : {A B : Obj} {f g : Mph A B} (eq1 eq2 : EqualizerOf f g) -> Σ (MorphismReduction (EqualizerOf.e eq1) (EqualizerOf.e eq2)) (λ red -> Iso (MorphismReduction.u red))
  equalizer_uniqueness eq1 eq2 =
    let
      open EqualizerOf eq1 renaming (e to e1 ; cone to cone1 ; reduceCone to redEq1 ; proveId to proveId1)
      open EqualizerOf eq2 renaming (e to e2 ; cone to cone2 ; reduceCone to redEq2 ; proveId to proveId2)

      r12 : MorphismReduction e1 e2
      r12 = redEq2 cone1

      r21 : MorphismReduction e2 e1
      r21 = redEq1 cone2

      u21 = MorphismReduction.u r21
    in r12 , record
               { inverse = u21
               ; leftInverse  = proveId1 (composeMorphismReductions r21 r12)
               ; rightInverse = proveId2 (composeMorphismReductions r12 r21)
               }


  equalizer_is_mono : {A B : Obj} {f g : Mph A B} (eq : EqualizerOf f g) -> Mono (EqualizerOf.e eq)
  equalizer_is_mono {f = f} {g = g} eq = mono λ {X α β} eα=eβ →
    let
      open EqualizerOf eq renaming (evidence to fe=ge)

      feβ=geβ : f ∘ (e ∘ β) ≡ g ∘ (e ∘ β)
      feβ=geβ = flipEq assoc =>>= ((_∘ β) $= fe=ge) =>>= assoc

      eqβ : Equalizing f g (e ∘ β)
      eqβ = isEqualizing feβ=geβ

      redα : MorphismReduction (e ∘ β) e
      redα = record { u = α ; ev = eα=eβ }

      redβ : MorphismReduction (e ∘ β) e
      redβ = record { u = β ; ev = refl }

      open UniqueMorphismReduction (universal eqβ)
      α=u = unique redα
      β=u = unique redβ
    in α=u =>>= flipEq β=u

  equalizer_is_mono' : {A B E : Obj} {f g : Mph A B} {e : Mph E A} (eq : Equalizer f g e) -> Mono e
  equalizer_is_mono' {E = E} {e = e} eq = equalizer_is_mono (equalizerData E e eq)

  epi_equalizer_is_iso : {A B : Obj} {f g : Mph A B} (eq : EqualizerOf f g) -> Epi (EqualizerOf.e eq) -> Iso (EqualizerOf.e eq)
  epi_equalizer_is_iso {f = f} {g} eq isEpi with equalizer_is_mono eq
  epi_equalizer_is_iso {f = f} {g} (equalizerData E e ((isEqualizing fe=ge) universally universal)) (epi elim-e) | mono-e = mono_retraction_is_iso mono-e retr-e
    where
      f=g = elim-e fe=ge

      idEq : Equalizing f g id
      idEq = isEqualizing ((_∘ id) $= f=g)

      retr-e : Retraction e
      retr-e = case (universal idEq) of
        λ { ((reduceMorphismBy e⁻¹ witnessedBy ee⁻¹=id) uniquely _) → hasSection e⁻¹ ee⁻¹=id }

  -- A different proof of the same fact.
  epi_equalizer_is_iso' : {A B : Obj} {f g : Mph A B} (eq : EqualizerOf f g) -> Epi (EqualizerOf.e eq) -> Iso (EqualizerOf.e eq)
  epi_equalizer_is_iso' {f = f} {g} eq (epi elim-e) = iso-e
    where
      open EqualizerOf eq using (e) renaming (evidence to fe=ge)

      f=g = elim-e fe=ge

      idEq : EqualizerOf f g
      idEq = idEqualizerOf f=g

      iso-e : Iso e
      iso-e with equalizer_uniqueness idEq eq
      ... | (reduceMorphismBy d witnessedBy ed=id , iso d⁻¹ d⁻¹d=id dd⁻¹=id) =
        case d⁻¹=e of λ { refl -> iso d dd⁻¹=id d⁻¹d=id } where
          d⁻¹=e = flipEq left_id =>>= ((_∘ d⁻¹) $= flipEq ed=id) =>>= assocLR =>>= ((e ∘_) $= dd⁻¹=id) =>>= right_id

  section_is_equalizer : {A B : Obj} {s : Mph A B} (sec : Section s) -> Equalizer (s ∘ Section.retraction sec) id s
  section_is_equalizer {A} {B} {s} record { retraction = r ; evidence = rs=id } =
    record
      { cone = isEqualizing (assoc =>>= ((s ∘_) $= rs=id) =>>= right_id =>>= flipEq left_id)
      ; universal = λ { {E₂} {e₂} (isEqualizing sre=e) → record
                        { reduction = record
                          { u = r ∘ e₂
                          ; ev = flipEq assoc =>>= sre=e =>>= left_id
                          }
                        ; unique = λ { record { u = u ; ev = su=e₂ } → 
                            flipEq left_id =>>= ((_∘ u) $= (flipEq rs=id)) =>>= assoc =>>= ((r ∘_) $= su=e₂) }
                        }
                      }
      }
