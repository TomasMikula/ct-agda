open import Data.Product
open import Prelude
open import category
open import functor
open import SET

Hom : {k l : Level} (𝒞 : Category k l) -> (op 𝒞 ⨉ 𝒞) => SET l
Hom 𝒞 = record
  { mapObj = λ { (A , B) → Mph A B }
  ; mapArr = λ { (f , h) g → h ∘ (g ∘ f) }
  ; identity = extensionality (λ f → id ∘= right-id =>>= left-id)
  ; composition = extensionality (λ f → assocLR =>>= (_ ∘= (_ ∘= assocRL =>>= assocRL)))
  }
 where
  open Category 𝒞

_-Hom-_ : {kc lc kd ld ka la : Level} {𝒞 : Category kc lc} {𝒟 : Category kd ld} {𝒜 : Category ka la} ->
          (𝒞 => 𝒜) -> (𝒟 => 𝒜) -> (op 𝒞 ⨉ 𝒟) => SET la
_-Hom-_ {𝒞 = 𝒞} {𝒟 = 𝒟} {𝒜 = 𝒜} F G = record
  { mapObj = λ { (C , D) -> Mph (FObj C) (GObj D) }
  ; mapArr = λ { (f , h) g → GArr h ∘ (g ∘ FArr f) }
  ; identity = extensionality λ f -> G-id =∘= ((f ∘= F-id) =>>= right-id) =>>= left-id
  ; composition = extensionality λ f -> G-cmp =∘= (f ∘= F-cmp) =>>= assocLR =>>= (_ ∘= (_ ∘= assocRL =>>= assocRL))
  }
 where
  open Category 𝒜
  open Category 𝒞 using () renaming (id to idC)
  open Category 𝒟 using () renaming (id to idD)
  open Functor F renaming (mapObj to FObj ; mapArr to FArr ; identity to F-id ; composition to F-cmp)
  open Functor G renaming (mapObj to GObj ; mapArr to GArr ; identity to G-id ; composition to G-cmp)
