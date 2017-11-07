open import Prelude
open import category

module patterns {k l : Level} (𝒞 : Category k l) where
  open Category 𝒞

  record SpanReduction {X Y A₁ A₂ : Obj} (x₁ : Hom X A₁) (x₂ : Hom X A₂) (y₁ : Hom Y A₁) (y₂ : Hom Y A₂) : Set l where
    constructor reduceSpanBy_witnessedBy_and_
    field
      u : Hom X Y
      ev₁ : (y₁ ∘ u) ≡ x₁
      ev₂ : (y₂ ∘ u) ≡ x₂

  composeSpanReductions : {X Y Z A₁ A₂ : Obj} {x₁ : Hom X A₁} {x₂ : Hom X A₂}
                          {y₁ : Hom Y A₁} {y₂ : Hom Y A₂} {z₁ : Hom Z A₁} {z₂ : Hom Z A₂} ->
                          SpanReduction y₁ y₂ z₁ z₂ -> SpanReduction x₁ x₂ y₁ y₂ -> SpanReduction x₁ x₂ z₁ z₂
  composeSpanReductions (reduceSpanBy yz witnessedBy z₁∘yz=y₁ and z₂∘yz=y₂)
                        (reduceSpanBy xy witnessedBy y₁∘xy=x₁ and y₂∘xy=x₂) =
    reduceSpanBy (yz ∘ xy) witnessedBy
          (assocRL =>>= ((_∘ xy) $= z₁∘yz=y₁) =>>= y₁∘xy=x₁)
      and (assocRL =>>= ((_∘ xy) $= z₂∘yz=y₂) =>>= y₂∘xy=x₂)

  identitySpanReduction : {A A₁ A₂ : Obj} (a₁ : Hom A A₁) (a₂ : Hom A A₂) -> SpanReduction a₁ a₂ a₁ a₂
  identitySpanReduction _ _ = record { u = id ; ev₁ = right_id ; ev₂ = right_id }

  record UniqueSpanReduction {X A A₁ A₂ : Obj} (x₁ : Hom X A₁) (x₂ : Hom X A₂) (a₁ : Hom A A₁) (a₂ : Hom A A₂) : Set l where
    field
      reduction : SpanReduction x₁ x₂ a₁ a₂
      unique : (red₂ : SpanReduction x₁ x₂ a₁ a₂) -> SpanReduction.u red₂ ≡ SpanReduction.u reduction

    open SpanReduction reduction public


  record CospanReduction {C D A₁ A₂ : Obj} (c₁ : Hom A₁ C) (c₂ : Hom A₂ C) (d₁ : Hom A₁ D) (d₂ : Hom A₂ D) : Set l where
    constructor reduceCospanBy_witnessedBy_and_
    field
      u : Hom D C
      ev₁ : c₁ ≡ u ∘ d₁
      ev₂ : c₂ ≡ u ∘ d₂

  record UniqueCospanReduction {C D A₁ A₂ : Obj} (c₁ : Hom A₁ C) (c₂ : Hom A₂ C) (d₁ : Hom A₁ D) (d₂ : Hom A₂ D) : Set l where
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
  record CommutingSquare {A B C D : Obj} (f₁ : Hom A B) (g₁ : Hom B D) (f₂ : Hom A C) (g₂ : Hom C D) : Set l where
    constructor commutingSquare
    field
      evidence : g₁ ∘ f₁ ≡ g₂ ∘ f₂
