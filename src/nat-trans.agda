open import Data.Product
open import Function using (case_of_)
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

-- ∸ is Unicode symbol U+2238
syntax NatTrans F G = F ∸> G

-- Composition of natural transformations.
-- Unicode symbol U+2299.
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

-- Identity natural transformation.
-- Unicode symbol U+1D7D9
𝟙 : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F : 𝒞 => 𝒟} -> (F ∸> F)
𝟙 {𝒟 = 𝒟} {F} = natTrans id witnessedBy λ f -> left_id =>>= (flipEq right_id) where
  open Category 𝒟

-- Data witnessing equality of natural transformations.
NatTransEqWitness : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F G : Functor 𝒞 𝒟}
                    (α β : F ∸> G) -> Set (nc ⊔ md)
NatTransEqWitness {𝒞 = 𝒞} {𝒟} {functor F _ _ _} {functor G _ _ _}
                  (natTrans α witnessedBy _) (natTrans β witnessedBy _) =
  _≡_ {_} { {A : Obj 𝒞} -> Mph 𝒟 (F A) (G A) } α β where open Category

-- Helper for proving equality of natural transformations.
equalNatTrans : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F G : Functor 𝒞 𝒟}
                {α β : F ∸> G} -> NatTransEqWitness α β -> α ≡ β
equalNatTrans {𝒞 = 𝒞} {𝒟 = 𝒟} {functor _ F _ _} {functor _ G _ _}
              {natTrans α witnessedBy α-nat} {natTrans .α witnessedBy β-nat} refl = res where
  open Category hiding (_∘_)
  open Category 𝒟 using (_∘_)

  naturality-eq : _≡_ {_} { {A B : Obj 𝒞} (f : Mph 𝒞 A B) -> α ∘ (F f) ≡ (G f) ∘ α } α-nat β-nat
  naturality-eq = extensionality' (extensionality' (extensionality λ f -> eqUnicity))
  res = case naturality-eq of λ { refl -> refl }

-- Associativity of composition of natural transformations.
assoc-⊙ : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F G H I : Functor 𝒞 𝒟}
          {α : H ∸> I} {β : G ∸> H} {γ : F ∸> G} -> (α ⊙ β) ⊙ γ ≡ α ⊙ (β ⊙ γ)
assoc-⊙ {𝒟 = 𝒟} = equalNatTrans (extensionality' assoc) where open Category 𝒟 using (assoc)

-- Left identity for composition of natural transformations.
left-id-⊙ : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F G : Functor 𝒞 𝒟}
            {α : F ∸> G} -> 𝟙 ⊙ α ≡ α
left-id-⊙ {𝒟 = 𝒟} = equalNatTrans (extensionality' left_id) where open Category 𝒟 using (left_id)

-- Right identity for composition of natural transformations.
right-id-⊙ : {nc mc nd md : Level} {𝒞 : Category nc mc} {𝒟 : Category nd md} {F G : Functor 𝒞 𝒟}
             {α : F ∸> G} -> α ⊙ 𝟙 ≡ α
right-id-⊙ {𝒟 = 𝒟} = equalNatTrans (extensionality' right_id) where open Category 𝒟 using (right_id)


-- Composition of natural transformation and functor.
_⊙>_ : {nb mb nc mc nd md : Level} {𝓑 : Category nb mb} {𝓒 : Category nc mc} {𝓓 : Category nd md} ->
       {F G : 𝓒 => 𝓓} -> (F ∸> G) -> (K : 𝓑 => 𝓒) -> ((F ⊚ K) ∸> (G ⊚ K))
(natTrans τ witnessedBy τ-nat) ⊙> K = natTrans (λ {A} -> τ {KObj A}) witnessedBy λ f -> τ-nat (KArr f) where
  open Functor K renaming (mapObj to KObj ; mapArr to KArr)

-- Composition of functor and natural transformation.
_<⊙_ : {nc mc nd md ne me : Level} {𝓒 : Category nc mc} {𝓓 : Category nd md} {𝓔 : Category ne me} ->
       {F G : 𝓒 => 𝓓} -> (H : 𝓓 => 𝓔) -> (F ∸> G) -> ((H ⊚ F) ∸> (H ⊚ G))
functor H HArr H-id H-cmp <⊙ (natTrans τ witnessedBy τ-nat) =
  natTrans HArr τ witnessedBy λ f -> flipEq H-cmp =>>= (HArr $= τ-nat _) =>>= H-cmp

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

syntax NatEquiv F G = F <∸> G
