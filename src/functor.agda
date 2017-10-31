open import Prelude
open import category

record Functor {n₁ m₁ n₂ m₂ : Level} (𝒞₁ : Category n₁ m₁) (𝒞₂ : Category n₂ m₂) : Set (n₁ ⊔ m₁ ⊔ n₂ ⊔ m₂) where
  open Category 𝒞₁ using () renaming (Obj to Obj₁ ; Hom to Hom₁ ; id to id₁ ; _∘_ to _∘₁_)
  open Category 𝒞₂ using () renaming (Obj to Obj₂ ; Hom to Hom₂ ; id to id₂ ; _∘_ to _∘₂_)
  field
    mapObj : Obj₁ -> Obj₂
    mapArr : {A B : Obj₁} -> Hom₁ A B -> Hom₂ (mapObj A) (mapObj B)

    -- laws
    identity : {A : Obj₁} -> mapArr (id₁ {A}) ≡ id₂ {mapObj A}
    composition : {A B C : Obj₁} {g : Hom₁ B C} {f : Hom₁ A B} -> mapArr (g ∘₁ f) ≡ (mapArr g) ∘₂ (mapArr f)

ConstFunctor : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} -> Category.Obj 𝒞₂ -> Functor 𝒞₁ 𝒞₂
ConstFunctor {𝒞₂ = 𝒞₂} C = record
  { mapObj = λ x → C
  ; mapArr = λ f → id₂
  
  ; identity = refl
  ; composition = flipEq left_id₂
  }
  where
    open Category 𝒞₂ renaming (id to id₂ ; left_id to left_id₂)
