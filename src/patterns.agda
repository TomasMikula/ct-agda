open import Prelude
open import category

module patterns {k l : Level} (𝒞 : Category k l) where
  open Category 𝒞

  record SpanReduction {X Y A₁ A₂ : Obj} (x₁ : Mph X A₁) (x₂ : Mph X A₂) (y₁ : Mph Y A₁) (y₂ : Mph Y A₂) : Set l where
    constructor reduceSpanBy_witnessedBy_and_
    field
      u : Mph X Y
      ev₁ : (y₁ ∘ u) ≡ x₁
      ev₂ : (y₂ ∘ u) ≡ x₂

  composeSpanReductions : {X Y Z A₁ A₂ : Obj} {x₁ : Mph X A₁} {x₂ : Mph X A₂}
                          {y₁ : Mph Y A₁} {y₂ : Mph Y A₂} {z₁ : Mph Z A₁} {z₂ : Mph Z A₂} ->
                          SpanReduction y₁ y₂ z₁ z₂ -> SpanReduction x₁ x₂ y₁ y₂ -> SpanReduction x₁ x₂ z₁ z₂
  composeSpanReductions (reduceSpanBy yz witnessedBy z₁∘yz=y₁ and z₂∘yz=y₂)
                        (reduceSpanBy xy witnessedBy y₁∘xy=x₁ and y₂∘xy=x₂) =
    reduceSpanBy (yz ∘ xy) witnessedBy
          (assocRL =>>= ((_∘ xy) $= z₁∘yz=y₁) =>>= y₁∘xy=x₁)
      and (assocRL =>>= ((_∘ xy) $= z₂∘yz=y₂) =>>= y₂∘xy=x₂)

  identitySpanReduction : {A A₁ A₂ : Obj} (a₁ : Mph A A₁) (a₂ : Mph A A₂) -> SpanReduction a₁ a₂ a₁ a₂
  identitySpanReduction _ _ = record { u = id ; ev₁ = right-id ; ev₂ = right-id }

  record UniqueSpanReduction {X A A₁ A₂ : Obj} (x₁ : Mph X A₁) (x₂ : Mph X A₂) (a₁ : Mph A A₁) (a₂ : Mph A A₂) : Set l where
    constructor _uniquely_
    field
      reduction : SpanReduction x₁ x₂ a₁ a₂
      unique : (red₂ : SpanReduction x₁ x₂ a₁ a₂) -> SpanReduction.u red₂ ≡ SpanReduction.u reduction

    open SpanReduction reduction public


  record CospanReduction {C D A₁ A₂ : Obj} (c₁ : Mph A₁ C) (c₂ : Mph A₂ C) (d₁ : Mph A₁ D) (d₂ : Mph A₂ D) : Set l where
    constructor reduceCospanBy_witnessedBy_and_
    field
      u : Mph D C
      ev₁ : c₁ ≡ u ∘ d₁
      ev₂ : c₂ ≡ u ∘ d₂

  record UniqueCospanReduction {C D A₁ A₂ : Obj} (c₁ : Mph A₁ C) (c₂ : Mph A₂ C) (d₁ : Mph A₁ D) (d₂ : Mph A₂ D) : Set l where
    constructor _uniquely_
    field
      reduction : CospanReduction c₁ c₂ d₁ d₂
      unique : (red₂ : CospanReduction c₁ c₂ d₁ d₂) -> CospanReduction.u red₂ ≡ CospanReduction.u reduction

    open CospanReduction reduction public

  --
  --      f₁
  --    A -> B
  --  f₂|    |g₁
  --    v    v
  --    C -> D
  --      g₂
  --
  record CommutingSquare {A B C D : Obj} (f₁ : Mph A B) (g₁ : Mph B D) (f₂ : Mph A C) (g₂ : Mph C D) : Set l where
    constructor commutingSquare
    field
      evidence : g₁ ∘ f₁ ≡ g₂ ∘ f₂
