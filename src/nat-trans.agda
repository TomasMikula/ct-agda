open import Data.Product
open import Prelude
open import category
open import functor
import morphisms

-- Natural transformation.
record NatTrans {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} (F G : Functor 𝒞 𝒟) : Set (nc ⊔ mc ⊔ nd ⊔ md) where
  constructor natTrans_witnessedBy_
  open Category hiding (_∘_)
  open Category 𝒟 using (_∘_)
  open Functor F renaming (mapObj to Fobj ; mapArr to Farr)
  open Functor G renaming (mapObj to Gobj ; mapArr to Garr)
  field
    τ : {A : Obj 𝒞} -> Mph 𝒟 (Fobj A) (Gobj A)
    naturality : {A B : Obj 𝒞} (f : Mph 𝒞 A B) -> τ ∘ (Farr f) ≡ (Garr f) ∘ τ

-- Composition of natural transformations.
_⊙_ : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F G H : Functor 𝒞 𝒟} ->
      NatTrans G H -> NatTrans F G -> NatTrans F H
_⊙_ {𝒞 = 𝒞} {𝒟 = 𝒟} {F} {G} {H} (natTrans τ witnessedBy τ-naturality) (natTrans σ witnessedBy σ-naturality) =
  natTrans (τ ∘ σ) witnessedBy naturality where
    open Category using (Obj ; Mph)
    open Category 𝒟 using (_∘_ ; assocLR ; assocRL)
    open Functor F renaming (mapArr to Farr)
    open Functor H renaming (mapArr to Harr)
    
    naturality : {A B : Obj 𝒞} (f : Mph 𝒞 A B) → ((τ ∘ σ) ∘ Farr f) ≡ (Harr f ∘ (τ ∘ σ))
    naturality f = assocLR =>>= ((τ ∘_) $= σ-naturality f) =>>= assocRL =>>= ((_∘ σ) $= τ-naturality f) =>>= assocLR

-- Natural equivalence.
record NatEquiv {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} (F G : Functor 𝒞 𝒟) : Set (nc ⊔ mc ⊔ nd ⊔ md) where
  constructor natEquiv_witnessedBy_and_
  open Category using (Obj ; Mph)
  open Category 𝒟 using (_∘_ ; assocLR ; assocRL ; left_id ; right_id)
  open Functor F renaming (mapObj to Fobj ; mapArr to Farr)
  open Functor G renaming (mapObj to Gobj ; mapArr to Garr)
  open morphisms 𝒟

  field
    τ : {A : Obj 𝒞} -> Mph 𝒟 (Fobj A) (Gobj A)
    naturality : {A B : Obj 𝒞} (f : Mph 𝒞 A B) -> τ ∘ (Farr f) ≡ (Garr f) ∘ τ
    isomorphic : {A : Obj 𝒞} -> Iso (τ {A})

  reverse : NatEquiv G F
  reverse = record
    { τ = rev-τ
    ; naturality = rev-nat
    ; isomorphic = Iso.reverse isomorphic
    }
   where
    rev-τ : {A : Obj 𝒞} → Mph 𝒟 (Gobj A) (Fobj A)
    rev-τ = Iso.inverse isomorphic

    rev-nat : {A B : Obj 𝒞} (f : Mph 𝒞 A B) → (rev-τ ∘ Garr f) ≡ (Farr f ∘ rev-τ)
    rev-nat {A} {B} f = flipEq right_id =>>= (((rev-τ ∘ Garr f) ∘_) $= flipEq (Iso.rightInverse isomorphic)) =>>= assocRL =>>= ((_∘ rev-τ) $= (assocLR =>>= ((rev-τ ∘_) $= flipEq (naturality f)) =>>= assocRL =>>= ((_∘ Farr f) $= (Iso.leftInverse isomorphic)) =>>= left_id))

  trans : NatTrans F G
  trans = natTrans τ witnessedBy naturality

  rev-trans : NatTrans G F
  rev-trans with reverse
  ... | record { τ = ρ ; naturality = ρ-nat ; isomorphic = ρ-iso } = natTrans ρ witnessedBy ρ-nat
