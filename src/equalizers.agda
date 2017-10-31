open import Agda.Primitive
open import Data.Product
open import Prelude
open import category
import morphisms

module equalizers {n m : Level} (𝒞 : Category n m) where
  open Category 𝒞
  open morphisms 𝒞

  record Equalizing {A B : Obj} (f g : Hom A B) : Set (n ⊔ m) where
    constructor equalizing
    field
      E : Obj
      e : Hom E A
      comm : f ∘ e ≡ g ∘ e

  record EqualizingReduction {A B : Obj} {f g : Hom A B} (eq₂ : Equalizing f g) (eq : Equalizing f g) : Set (n ⊔ m) where
    open Equalizing(eq)
    open Equalizing(eq₂) renaming (E to E₂ ; e to e₂)
    field
      u : Hom E₂ E
      ev : e ∘ u ≡ e₂

  composeEqualizingReductions : {A B : Obj} {f g : Hom A B} {c d e : Equalizing f g} -> EqualizingReduction d e -> EqualizingReduction c d -> EqualizingReduction c e
  composeEqualizingReductions de cd =
    record
      { u = u_de ∘ u_cd
      ; ev = flipEq assoc =>>= ((_∘ u_cd) $= ev_de) =>>= ev_cd
      }
    where
      open EqualizingReduction de renaming (u to u_de ; ev to ev_de)
      open EqualizingReduction cd renaming (u to u_cd ; ev to ev_cd)

  identityEqualizingReduction : {A B : Obj} {f g : Hom A B} (e : Equalizing f g) -> EqualizingReduction e e
  identityEqualizingReduction e = record { u = id ; ev = right_id }

  record UniqueEqualizingReduction {A B : Obj} {f g : Hom A B} (eq₂ : Equalizing f g) (eq : Equalizing f g) : Set (n ⊔ m) where
    field
      reduction : EqualizingReduction eq₂ eq
      unique : (red₂ : EqualizingReduction eq₂ eq) -> EqualizingReduction.u red₂ ≡ EqualizingReduction.u reduction

    u = EqualizingReduction.u reduction
    ev = EqualizingReduction.ev reduction

  record Equalizer {A B : Obj} (f g : Hom A B) : Set (n ⊔ m) where
    field
      cone : Equalizing f g
      universal : (eq₂ : Equalizing f g) -> UniqueEqualizingReduction eq₂ cone

    E    = Equalizing.E    cone
    e    = Equalizing.e    cone
    comm = Equalizing.comm cone

    reduceCone : (e2 : Equalizing f g) -> EqualizingReduction e2 cone
    reduceCone e2 = reduction where open UniqueEqualizingReduction (universal e2)

    proveId : (red : EqualizingReduction cone cone) -> EqualizingReduction.u red ≡ id
    proveId red =
      let
        open UniqueEqualizingReduction (universal cone)
        u_id = unique (identityEqualizingReduction cone)
        u_red = unique red
      in u_red =>>= flipEq u_id

  idEqualizer : {A B : Obj} {f g : Hom A B} -> f ≡ g -> Equalizer f g
  idEqualizer {A} f=g =
    record
      { cone = equalizing A id ((_∘ id) $= f=g)
      ; universal = λ eq →
          let
            open Equalizing eq using (e)
          in record
            { reduction = record { u = e ; ev = left_id }
            ; unique = λ red₂ → flipEq left_id =>>= EqualizingReduction.ev red₂
            }
      }

  equalizer_uniqueness : {A B : Obj} {f g : Hom A B} (e1 e2 : Equalizer f g) -> Σ (EqualizingReduction (Equalizer.cone e1) (Equalizer.cone e2)) (λ red -> Iso (EqualizingReduction.u red))
  equalizer_uniqueness e1 e2 =
    let
      open Equalizer e1 renaming (cone to cone1 ; reduceCone to redEq1 ; proveId to proveId1)
      open Equalizer e2 renaming (cone to cone2 ; reduceCone to redEq2 ; proveId to proveId2)

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


  equalizer_is_mono : {A B : Obj} {f g : Hom A B} (eq : Equalizer f g) -> Mono (Equalizer.e eq)
  equalizer_is_mono {f = f} {g = g} eq = mono λ {X α β} eα=eβ →
    let
      open Equalizer eq

      fe=ge : f ∘ e ≡ g ∘ e
      fe=ge = Equalizer.comm eq

      feβ=geβ : f ∘ (e ∘ β) ≡ g ∘ (e ∘ β)
      feβ=geβ = flipEq assoc =>>= ((_∘ β) $= fe=ge) =>>= assoc

      eqβ = equalizing X (e ∘ β) feβ=geβ

      redα : EqualizingReduction eqβ cone
      redα = record { u = α ; ev = eα=eβ }

      redβ : EqualizingReduction eqβ cone
      redβ = record { u = β ; ev = refl }

      open UniqueEqualizingReduction (universal eqβ)
      α=u = unique redα
      β=u = unique redβ
    in α=u =>>= flipEq β=u

  epi_equalizer_is_iso : {A B : Obj} {f g : Hom A B} (eq : Equalizer f g) -> Epi (Equalizer.e eq) -> Iso (Equalizer.e eq)
  epi_equalizer_is_iso {f = f} {g = g} eq isEpi =
    let
      open Equalizer eq renaming (comm to fe=ge)

      f=g = Epi.elimR isEpi fe=ge

      idEq : Equalizing f g
      idEq = equalizing _ id ((_∘ id) $= f=g)

      id_to_eq : EqualizingReduction idEq cone
      id_to_eq = UniqueEqualizingReduction.reduction (universal idEq)

      r : Retraction e
      r = record
            { section = EqualizingReduction.u id_to_eq
            ; evidence = EqualizingReduction.ev id_to_eq
            }
    in mono_retraction_is_iso (equalizer_is_mono eq) r

  -- A different proof of the same fact.
  epi_equalizer_is_iso' : {A B : Obj} {f g : Hom A B} (eq : Equalizer f g) -> Epi (Equalizer.e eq) -> Iso (Equalizer.e eq)
  epi_equalizer_is_iso' {f = f} {g = g} eq isEpi =
    let
      open Equalizer eq using (e) renaming (cone to eCone ; comm to fe=ge)

      f=g = Epi.elimR isEpi fe=ge

      idEq : Equalizer f g
      idEq = idEqualizer f=g

      open Equalizer idEq hiding (e) renaming (universal to idUniversal)
      open UniqueEqualizingReduction (idUniversal eCone) renaming (reduction to red ; unique to redUnique)

      open Σ (equalizer_uniqueness eq idEq) renaming (proj₁ to red' ; proj₂ to iso_red')
      u_red'=u_red = redUnique red'
      u_red=e = flipEq (redUnique (record { u = e ; ev = left_id }))
      u_red'=e = u_red'=u_red =>>= u_red=e
    in coerce (Iso $= u_red'=e) iso_red'

  section_is_equalizer : {A B : Obj} {s : Hom A B} (sec : Section s) -> Equalizer (s ∘ Section.retraction sec) id
  section_is_equalizer {A} {B} {s} sec =
    let
      open Section sec renaming (retraction to r ; evidence to rs=id)
    in record
         { cone = equalizing A s (assoc =>>= ((s ∘_) $= rs=id) =>>= right_id =>>= flipEq left_id)
         ; universal = λ eq₂ →
           let
             open Equalizing eq₂ renaming (e to e ; comm to sre=e)
           in record
                { reduction = record
                    { u = r ∘ e
                    ; ev = flipEq assoc =>>= sre=e =>>= left_id
                    }
                ; unique = λ red₂ →
                  let
                    open EqualizingReduction red₂
                  in flipEq left_id =>>= ((_∘ u) $= (flipEq rs=id)) =>>= assoc =>>= ((r ∘_) $= ev)
                }
         }
