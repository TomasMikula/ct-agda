open import Data.Product
open import Prelude
open import category
open import functor
open import nat-trans
open import monad
open import f-algebra

-- Algebra for the monad T.
record T-algebra {k l : Level} {𝒞 : Category k l} {T : 𝒞 => 𝒞} (M : Monad T) : Set (l ⊔ k) where
  constructor _respecting_
  open Category 𝒞
  open Functor T using () renaming (mapArr to Tm)
  open Monad M using (μ ; η)
  open NatTrans μ using () renaming (τ to μ₀)
  open NatTrans η using () renaming (τ to η₀)
  
  field
    base : F-algebra T

  open F-algebra base public using (A ; α)

  field
    laws : (α ∘ Tm α ≡ α ∘ μ₀) × (α ∘ η₀ ≡ id)

-- Category of algebras for the monad T. Also called the Eilenberg-Moore category.
T-Alg : {k l : Level} {𝒞 : Category k l} {T : 𝒞 => 𝒞} (M : Monad T) -> Category (l ⊔ k) l
T-Alg {𝒞 = 𝒞} {T} M = record
  { Obj = T-algebra M
  ; Mph = AlgMph
  ; id = λ { {algebra A α respecting _} -> (id {A} , left-id =>>= flipEq right-id =>>= flipEq (α ∘= T-id)) }
  ; _∘_ = λ { {algebra A α respecting _}
              {algebra B β respecting _}
              {algebra C γ respecting _}
              (f , f∘β=γ∘Tf) (g , g∘α=β∘Tg) →
            ( f ∘ g
            , ( (f ∘ g) ∘ α          =[ assoc ]>
                f ∘ (g ∘ α)          =[ f ∘= g∘α=β∘Tg ]>
                f ∘ (β ∘ Tm g)       <[ assoc ]=
                (f ∘ β) ∘ Tm g       =[ f∘β=γ∘Tf =∘ Tm g ]>
                (γ ∘ Tm f) ∘ Tm g    =[ assoc ]>
                γ ∘ (Tm f ∘ Tm g)    <[ γ ∘= T-cmp ]=
                γ ∘ Tm (f ∘ g)       ∎)
            )}

  ; left-id  = λ {A B}     {f}     -> equalAlgMphs {A} {B} {_} {f} left-id
  ; right-id = λ {A B}     {f}     -> equalAlgMphs {A} {B} {_} {f} right-id
  ; assoc    = λ {A B C D} {f g h} -> equalAlgMphs {A} {D} {_} {_} assoc
  }
 where
  open Category 𝒞
  open Functor T using () renaming (mapArr to Tm ; identity to T-id ; composition to T-cmp)
  
  AlgMph : (A B : T-algebra M) -> Set _
  AlgMph (algebra A α respecting (α∘Tα=α∘μ , α∘η=id)) (algebra B β respecting _) =
    Σ[ f ∈ Mph A B ] f ∘ α ≡ β ∘ Tm f

  equalAlgMphs : {A B : T-algebra M} {f g : AlgMph A B} -> Σ.proj₁ f ≡ Σ.proj₁ g -> f ≡ g
  equalAlgMphs refl = Σ= (refl , eqUnicity)
