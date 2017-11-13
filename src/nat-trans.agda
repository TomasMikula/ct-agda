open import Prelude
open import category
open import functor

record NatTrans {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} (F G : Functor 𝒞 𝒟) : Set (nc ⊔ mc ⊔ nd ⊔ md) where
  constructor natTrans_witnessedBy_
  open Category hiding (_∘_)
  open Category 𝒟 using (_∘_)
  open Functor F renaming (mapObj to Fobj ; mapArr to Farr)
  open Functor G renaming (mapObj to Gobj ; mapArr to Garr)
  field
    τ : {A : Obj 𝒞} -> Hom 𝒟 (Fobj A) (Gobj A)
    naturality : {A B : Obj 𝒞} (f : Hom 𝒞 A B) -> τ ∘ (Farr f) ≡ (Garr f) ∘ τ

-- Composition of natural transformations.
_⊙_ : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F G H : Functor 𝒞 𝒟} ->
      NatTrans G H -> NatTrans F G -> NatTrans F H
_⊙_ {𝒞 = 𝒞} {𝒟 = 𝒟} {F} {G} {H} (natTrans τ witnessedBy τ-naturality) (natTrans σ witnessedBy σ-naturality) =
  natTrans (τ ∘ σ) witnessedBy naturality where
    open Category using (Obj ; Hom)
    open Category 𝒟 using (_∘_ ; assocLR ; assocRL)
    open Functor F renaming (mapArr to Farr)
    open Functor H renaming (mapArr to Harr)
    
    naturality : {A B : Obj 𝒞} (f : Hom 𝒞 A B) → ((τ ∘ σ) ∘ Farr f) ≡ (Harr f ∘ (τ ∘ σ))
    naturality f = assocLR =>>= ((τ ∘_) $= σ-naturality f) =>>= assocRL =>>= ((_∘ σ) $= τ-naturality f) =>>= assocLR
