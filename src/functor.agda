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
  ; composition = flipEq left-id₂
  }
  where
    open Category 𝒞₂ renaming (id to id₂ ; left-id to left-id₂)

Id : {n m : Level} {𝒞 : Category n m} -> 𝒞 => 𝒞
Id = record
  { mapObj = λ A → A
  ; mapArr = λ f → f
  ; identity = refl
  ; composition = refl
  }

-- Functor composition.
-- Unicode symbol U+29BE.
_⦾_ : {n₁ m₁ n₂ m₂ n₃ m₃ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {𝒞₃ : Category n₃ m₃} ->
      (𝒞₂ => 𝒞₃) -> (𝒞₁ => 𝒞₂) -> (𝒞₁ => 𝒞₃)
(functor Fo Fm F-id F-cmp) ⦾ (functor Go Gm G-id G-cmp) = record
  { mapObj = λ A -> Fo (Go A)
  ; mapArr = λ f -> Fm (Gm f)
  ; identity = (Fm $= G-id) =>>= F-id
  ; composition = (Fm $= G-cmp) =>>= F-cmp
  }

-- Data witnessing equality of functors.
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
assoc-⦾ : {n₁ m₁ n₂ m₂ n₃ m₃ n₄ m₄ : Level}
          {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {𝒞₃ : Category n₃ m₃} {𝒞₄ : Category n₄ m₄}
          {F : 𝒞₃ => 𝒞₄} {G : 𝒞₂ => 𝒞₃} {H : 𝒞₁ => 𝒞₂} -> (F ⦾ G) ⦾ H ≡ F ⦾ (G ⦾ H)
assoc-⦾ = equalFunctors (refl , refl)

left-id-⦾ : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {F : 𝒞₁ => 𝒞₂} -> Id ⦾ F ≡ F
left-id-⦾ = equalFunctors (refl , refl)

right-id-⦾ : {n₁ m₁ n₂ m₂ : Level} {𝒞₁ : Category n₁ m₁} {𝒞₂ : Category n₂ m₂} {F : 𝒞₁ => 𝒞₂} -> F ⦾ Id ≡ F
right-id-⦾ = equalFunctors (refl , refl)

-- `F [ A ,-]` is functor `F : 𝓐⨉𝓑 => 𝓒` (partially) applied to object A of 𝓐, resulting in a functor `𝓑 => 𝓒`.
_[_,-] : ∀ {ka la kb lb kc lc} {𝓐 : Category ka la} {𝓑 : Category kb lb} {𝓒 : Category kc lc}
         (F : (𝓐 ⨉ 𝓑) => 𝓒) (A : Obj 𝓐) -> (𝓑 => 𝓒)
_[_,-] {𝓐 = 𝓐} {𝓑} {𝓒} (functor Fo Fm F-id F-cmp) A =
  functor
    (λ B → Fo (A , B))
    (λ g → Fm (id 𝓐 {A} , g))
    F-id
    λ {B C D g h} ->
      Fm (id 𝓐 {A} , g ∘𝓑 h)
        <[ (λ >O< -> Fm (>O< , g ∘𝓑 h)) $= right-id 𝓐 ]=
      Fm ((id 𝓐 {A}) ∘𝓐 (id 𝓐 {A}) , g ∘𝓑 h)
        =[ F-cmp ]>
      Fm (id 𝓐 {A}, g) ∘𝓒 (Fm (id 𝓐 {A}, h))
    ∎
  where
    open Category 𝓐 using () renaming (_∘_ to _∘𝓐_)
    open Category 𝓑 using () renaming (_∘_ to _∘𝓑_)
    open Category 𝓒 using () renaming (_∘_ to _∘𝓒_)

-- `F [-, B ]` is functor `F : 𝓐⨉𝓑 => 𝓒` (partially) applied to object B of 𝓑, resulting in a functor `𝓐 => 𝓒`.
_[-,_] : ∀ {ka la kb lb kc lc} {𝓐 : Category ka la} {𝓑 : Category kb lb} {𝓒 : Category kc lc}
         (F : (𝓐 ⨉ 𝓑) => 𝓒) (B : Obj 𝓑) -> (𝓐 => 𝓒)
_[-,_] {𝓐 = 𝓐} {𝓑} {𝓒} (functor Fo Fm F-id F-cmp) B =
  functor
    (λ A → Fo (A , B))
    (λ f → Fm (f , id 𝓑 {B}))
    F-id
    λ {A C D g h} ->
      Fm (g ∘𝓐 h , id 𝓑 {B})
        <[ (λ >O< -> Fm (g ∘𝓐 h , >O<)) $= left-id 𝓑 ]=
      Fm (g ∘𝓐 h , (id 𝓑 {B}) ∘𝓑 (id 𝓑 {B}))
        =[ F-cmp ]>
      Fm (g , id 𝓑 {B}) ∘𝓒 Fm (h , id 𝓑 {B})
    ∎
  where
    open Category 𝓐 using () renaming (_∘_ to _∘𝓐_)
    open Category 𝓑 using () renaming (_∘_ to _∘𝓑_)
    open Category 𝓒 using () renaming (_∘_ to _∘𝓒_)
