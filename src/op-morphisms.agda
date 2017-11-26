open import Data.Product
open import Prelude
open import category

module op-morphisms where
  open Category
  open import morphisms
  
  op-iso : {k l : Level} {𝒞 : Category k l} {A B : Obj 𝒞} {f : Mph 𝒞 A B} -> Iso 𝒞 f -> Iso (op 𝒞) f
  op-iso (iso f⁻¹ (f⁻¹f=id , ff⁻¹=id)) = iso f⁻¹ (ff⁻¹=id , f⁻¹f=id)

  unop-iso : {k l : Level} {𝒞 : Category k l} {A B : Obj 𝒞} {f : Mph (op 𝒞) B A} -> Iso (op 𝒞) f -> Iso 𝒞 f
  unop-iso (iso f⁻¹ (f⁻¹f=id , ff⁻¹=id)) = iso f⁻¹ (ff⁻¹=id , f⁻¹f=id)

  op-mono : {k l : Level} {𝒞 : Category k l} {A B : Obj 𝒞} {f : Mph 𝒞 A B} -> Mono 𝒞 f -> Epi (op 𝒞) f
  op-mono (mono elim-f) = epi elim-f

  unop-epi : {k l : Level} {𝒞 : Category k l} {A B : Obj 𝒞} {f : Mph (op 𝒞) B A} -> Epi (op 𝒞) f -> Mono 𝒞 f
  unop-epi (epi elim-f) = mono elim-f

  op-epi : {k l : Level} {𝒞 : Category k l} {A B : Obj 𝒞} {f : Mph 𝒞 A B} -> Epi 𝒞 f -> Mono (op 𝒞) f
  op-epi (epi elim-f) = mono elim-f

  unop-mono : {k l : Level} {𝒞 : Category k l} {A B : Obj 𝒞} {f : Mph (op 𝒞) B A} -> Mono (op 𝒞) f -> Epi 𝒞 f
  unop-mono (mono elim-f) = epi elim-f
