open import Data.Product
open import Prelude
open import category
open import functor
open import morphisms
open import nat-trans

open Category using (Obj ; Mph)

record Monoidal {k l : Level} (𝒞 : Category k l) : Set (k ⊔ l) where
  open Category 𝒞 using (_∘_ ; id)
  
  field
    -- tensor product (U+2A02)
    ⨂ : (𝒞 ⨉ 𝒞) => 𝒞

    -- unit object
    I : Obj 𝒞

  -- functor ⨂ acting on objects
  _⨂ᵒ_ : Obj 𝒞 -> Obj 𝒞 -> Obj 𝒞
  _⨂ᵒ_ A B = Functor.mapObj ⨂ (A , B)

  -- functor ⨂ acting on morphisms
  _⨂ᵐ_ : {A B C D : Obj 𝒞} -> Mph 𝒞 A B -> Mph 𝒞 C D -> Mph 𝒞 (A ⨂ᵒ C) (B ⨂ᵒ D)
  _⨂ᵐ_ f g = Functor.mapArr ⨂ (f , g)

  [-⨂-]⨂- : ((𝒞 ⨉ 𝒞) ⨉ 𝒞) => 𝒞
  [-⨂-]⨂- = ⨂ ⦾ (⨂ || Id)

  -⨂[-⨂-] : (𝒞 ⨉ (𝒞 ⨉ 𝒞)) => 𝒞
  -⨂[-⨂-] = ⨂ ⦾ (Id || ⨂)

  field
    -- associator
    α  : {A B C : Obj 𝒞} -> Mph 𝒞 ((A ⨂ᵒ B) ⨂ᵒ C) (A ⨂ᵒ (B ⨂ᵒ C))
    α' : {A B C : Obj 𝒞} -> Mph 𝒞 (A ⨂ᵒ (B ⨂ᵒ C)) ((A ⨂ᵒ B) ⨂ᵒ C)
    α-iso : {A B C : Obj 𝒞} -> MutuallyInverse 𝒞 (α {A} {B} {C}) (α' {A} {B} {C})

    -- α is natural in each variable
    α-nat₁ : {B C : Obj 𝒞} -> Natural ([-⨂-]⨂- [-, C ] [-, B ]) (-⨂[-⨂-] [-, (B , C)])    (λ {A} -> α {A} {B} {C})
    α-nat₂ : {A C : Obj 𝒞} -> Natural ([-⨂-]⨂- [-, C ] [ A ,-]) (-⨂[-⨂-] [ A ,-] [-, C ]) (λ {B} -> α {A} {B} {C})
    α-nat₃ : {A B : Obj 𝒞} -> Natural ([-⨂-]⨂- [(A , B) ,-])    (-⨂[-⨂-] [ A ,-] [ B ,-]) (λ {C} -> α {A} {B} {C})

    -- left unitor
    -- (𝜆 is Unicode U+1D706)
    𝜆  : {A : Obj 𝒞} -> Mph 𝒞 (I ⨂ᵒ A) A
    𝜆' : {A : Obj 𝒞} -> Mph 𝒞 A (I ⨂ᵒ A)
    𝜆-iso : {A : Obj 𝒞} -> MutuallyInverse 𝒞 (𝜆 {A}) (𝜆' {A})
    𝜆-nat : Natural (⨂ [ I ,-]) Id 𝜆

    -- right unitor
    ρ  : {A : Obj 𝒞} -> Mph 𝒞 (A ⨂ᵒ I) A
    ρ' : {A : Obj 𝒞} -> Mph 𝒞 A (A ⨂ᵒ I)
    ρ-iso : {A : Obj 𝒞} -> MutuallyInverse 𝒞 (ρ {A}) (ρ' {A})
    ρ-nat : Natural (⨂ [-, I ]) Id ρ

    -- Pentagon diagram commutes.
    --
    --                     α{A}{B}{C} ⨂ id{D}                      α{A}{B⨂C}{D}
    -- ((A ⨂ B) ⨂ C) ⨂ D -------------------> (A ⨂ (B ⨂ C)) ⨂ D -------------> A ⨂ ((B ⨂ C) ⨂ D)
    --        |                                                                     |
    --        | α{A⨂B}{C}{D}                                                        | id{A} ⨂ α{B}{C}{D}
    --        v                                                                     v
    -- (A ⨂ B) ⨂ (C ⨂ D) -----------------------------------------------------> A ⨂ (B ⨂ (C ⨂ D))
    --                                      α{A}{B}{C⨂D}
    --
    coherence-pentagon : {A B C D : Obj 𝒞} ->
      (id {A} ⨂ᵐ α{B}{C}{D}) ∘ (α{A}{B ⨂ᵒ C}{D} ∘ (α{A}{B}{C} ⨂ᵐ id {D}))
      ≡
      α{A}{B}{C ⨂ᵒ D} ∘ α{A ⨂ᵒ B}{C}{D}

    -- Triangle diagram commutes
    --
    --                α{A}{I}{B}
    --  (A ⨂ I) ⨂ B -----------> A ⨂ (I ⨂ B)
    --            \_              _/
    --              \_          _/
    --  ρ{A} ⨂ id{B}  \_      _/  id{A} ⨂ 𝜆{B}
    --                  \    /
    --                   V  V
    --                  A ⨂ Β
    --
    coherence-triangle : {A B : Obj 𝒞} -> (id{A} ⨂ᵐ 𝜆{B}) ∘ α{A}{I}{B} ≡ ρ{A} ⨂ᵐ id{B}
