{-# OPTIONS --rewriting #-}

open import Prelude
open import category
open import functor
open import nat-trans
open import monoidal
open import functor-category

open Monoidal

record Monad {k l : Level} {𝒞 : Category k l} (F : 𝒞 => 𝒞) : Set (k ⊔ l) where
  constructor monad
  field
    μ : (F ⦾ F) ∸> F
    η : Id ∸> F

    associativity  : μ ⦿ (μ ⧁ F) ≡ μ ⦿ (F ⧀ μ)
    left-identity  : μ ⦿ (η ⧁ F) ≡ 𝟙
    right-identity : μ ⦿ (F ⧀ η) ≡ 𝟙

-- Monad is a monoid in the category of endofunctors.
monad-monoid : {k l : Level} {𝒞 : Category k l} {F : 𝒞 => 𝒞} -> Monad F -> Monoid (Endo-⦾-Id 𝒞) F
monad-monoid {𝒞 = 𝒞} {functor Fₒ F F-id _}
             (monad μμ@(natTrans μ witnessedBy μ-nat) ηη@(natTrans η witnessedBy η-nat) μμF=μFμ μηF=1 μFη=1) =
 record
  { μ = μμ
  ; η = ηη
  ; associativity = equalNatTrans (extensionality' (λ {A} ->
      μ {A} ∘ ((id ∘ F (μ {A})) ∘ id)        =[ μ {A} ∘= (right-id =>>= left-id) ]>
      μ {A} ∘        F (μ {A})               <[ NatTrans.τ $= μμF=μFμ =$' A ]=
      μ {A} ∘        μ {Fₒ A}                <[ μ {A} ∘= (μ {Fₒ A} ∘= (F $= F-id =>>= F-id) =>>= right-id) ]=
      μ {A} ∘       (μ {Fₒ A} ∘ F (F id))    ∎
    ))
  ; left-identity = equalNatTrans (extensionality' (λ {A} ->
      μ ∘ (η ∘ id {Fₒ A})    =[ μ ∘= right-id ]>
      μ ∘  η                 =[ NatTrans.τ $= μηF=1 =$' A ]>
      id {Fₒ A}              ∎
    ))
  ; right-identity = equalNatTrans (extensionality' (λ {A} ->
      μ ∘ (id {Fₒ (Fₒ A)} ∘ F η)    =[ μ ∘= left-id ]>
      μ ∘                   F η     =[ NatTrans.τ $= μFη=1 =$' A ]>
      id {Fₒ A}                     ∎
    ))
  }
 where
  open Category 𝒞
