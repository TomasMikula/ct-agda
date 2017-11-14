open import Prelude
open import category

record Functor {n₁ m₁ n₂ m₂ : Level} (𝒞₁ : Category n₁ m₁) (𝒞₂ : Category n₂ m₂) : Set (n₁ ⊔ m₁ ⊔ n₂ ⊔ m₂) where
  open Category 𝒞₁ using () renaming (Obj to Obj₁ ; Mph to Mph₁ ; id to id₁ ; _∘_ to _∘₁_)
  open Category 𝒞₂ using () renaming (Obj to Obj₂ ; Mph to Mph₂ ; id to id₂ ; _∘_ to _∘₂_)
  field
    mapObj : Obj₁ -> Obj₂
    mapArr : {A B : Obj₁} -> Mph₁ A B -> Mph₂ (mapObj A) (mapObj B)

    -- laws
    identity : {A : Obj₁} -> mapArr (id₁ {A}) ≡ id₂ {mapObj A}
    composition : {A B C : Obj₁} {g : Mph₁ B C} {f : Mph₁ A B} -> mapArr (g ∘₁ f) ≡ (mapArr g) ∘₂ (mapArr f)

syntax Functor 𝒞 𝒟 = 𝒞 => 𝒟

ConstFunctor : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} -> Category.Obj 𝒞₂ -> 𝒞₁ => 𝒞₂
ConstFunctor {𝒞₂ = 𝒞₂} C = record
  { mapObj = λ x → C
  ; mapArr = λ f → id₂
  
  ; identity = refl
  ; composition = flipEq left_id₂
  }
  where
    open Category 𝒞₂ renaming (id to id₂ ; left_id to left_id₂)

Id : {n m : Level} (𝒞 : Category n m) -> 𝒞 => 𝒞
Id 𝒞 = record
  { mapObj = λ A → A
  ; mapArr = λ f → f
  ; identity = refl
  ; composition = refl
  }

-- Functor composition.
-- Unicode symbol U+229A.
_⊚_ : {n₁ m₁ n₂ m₂ n₃ m₃ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {𝒞₃ : Category n₃ m₃} ->
      (𝒞₂ => 𝒞₃) -> (𝒞₁ => 𝒞₂) -> (𝒞₁ => 𝒞₃)
_⊚_ F G = record
  { mapObj = λ A -> FObj (GObj A)
  ; mapArr = λ f -> FArr (GArr f)
  ; identity = (FArr $= G-id) =>>= F-id
  ; composition = (FArr $= G-cmp) =>>= F-cmp
  }
 where
  open Functor F renaming (mapObj to FObj ; mapArr to FArr ; identity to F-id ; composition to F-cmp)
  open Functor G renaming (mapObj to GObj ; mapArr to GArr ; identity to G-id ; composition to G-cmp)
