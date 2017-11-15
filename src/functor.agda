open import Data.Product
open import Prelude
open import category

open Category

record Functor {n₁ m₁ n₂ m₂ : Level} (𝒞₁ : Category n₁ m₁) (𝒞₂ : Category n₂ m₂) : Set (n₁ ⊔ m₁ ⊔ n₂ ⊔ m₂) where
  constructor functor
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

Id : {n m : Level} {𝒞 : Category n m} -> 𝒞 => 𝒞
Id = record
  { mapObj = λ A → A
  ; mapArr = λ f → f
  ; identity = refl
  ; composition = refl
  }

-- Functor composition.
-- Unicode symbol U+229A.
_⊚_ : {n₁ m₁ n₂ m₂ n₃ m₃ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {𝒞₃ : Category n₃ m₃} ->
      (𝒞₂ => 𝒞₃) -> (𝒞₁ => 𝒞₂) -> (𝒞₁ => 𝒞₃)
(functor Fo Fm F-id F-cmp) ⊚ (functor Go Gm G-id G-cmp) = record
  { mapObj = λ A -> Fo (Go A)
  ; mapArr = λ f -> Fm (Gm f)
  ; identity = (Fm $= G-id) =>>= F-id
  ; composition = (Fm $= G-cmp) =>>= F-cmp
  }

-- Data needed to prove equality of functors.
FunctorEqWitness : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂}
                   (F G : 𝒞₁ => 𝒞₂) -> Set (n₁ ⊔ n₂ ⊔ m₁ ⊔ m₂)
FunctorEqWitness {𝒞₁ = 𝒞₁} {𝒞₂} (functor Fobj Fmph F-id F-cmp) (functor Gobj Gmph G-id G-cmp) =
  Σ (Fobj ≡ Gobj) λ { refl →
    (_≡_ {_} { {A B : Obj 𝒞₁} → Mph 𝒞₁ A B → Mph 𝒞₂ (Fobj A) (Fobj B) } Fmph Gmph)
  }

FunctorEqWitness' : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂}
                    (F G : 𝒞₁ => 𝒞₂) -> Set (n₁ ⊔ n₂ ⊔ m₁ ⊔ m₂)
FunctorEqWitness' {𝒞₁ = 𝒞₁} {𝒞₂} F@(functor Fo Fm F-id F-cmp) G@(functor Go Gm G-id G-cmp) =
  Σ (FunctorEqWitness F G) λ { (refl , refl) ->
    (_≡_ {_} { {A : Obj 𝒞₁} -> Fm (id 𝒞₁ {A}) ≡ id 𝒞₂ {Fo A} } F-id G-id) ×
    (_≡_ {_} { {A B C : Obj 𝒞₁} {g : Mph 𝒞₁ B C} {f : Mph 𝒞₁ A B} -> Fm (_∘_ 𝒞₁ g f) ≡ _∘_ 𝒞₂ (Fm g) (Fm f) } F-cmp G-cmp)
  }

equalFunctors' : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂}
                 {F G : 𝒞₁ => 𝒞₂} -> FunctorEqWitness' F G -> F ≡ G
equalFunctors' ((refl , refl) , refl , refl) = refl

equalFunctors : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂}
                {F G : 𝒞₁ => 𝒞₂} -> FunctorEqWitness F G -> F ≡ G
equalFunctors (refl , refl) =
  equalFunctors' ((refl , refl) , (extensionality' eqUnicity , extensionality' (extensionality' (extensionality' (extensionality' (extensionality' eqUnicity))))))

-- Associativity of functor composition.
assoc-⊚ : {n₁ m₁ n₂ m₂ n₃ m₃ n₄ m₄ : Level}
          {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {𝒞₃ : Category n₃ m₃} {𝒞₄ : Category n₄ m₄}
          {F : 𝒞₃ => 𝒞₄} {G : 𝒞₂ => 𝒞₃} {H : 𝒞₁ => 𝒞₂} -> (F ⊚ G) ⊚ H ≡ F ⊚ (G ⊚ H)
assoc-⊚ = equalFunctors (refl , refl)

left-id-⊚ : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {F : 𝒞₁ => 𝒞₂} -> Id ⊚ F ≡ F
left-id-⊚ = equalFunctors (refl , refl)

right-id-⊚ : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {F : 𝒞₁ => 𝒞₂} -> F ⊚ Id ≡ F
right-id-⊚ = equalFunctors (refl , refl)
