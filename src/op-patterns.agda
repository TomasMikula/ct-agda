open import Prelude
open import category
open import patterns

module op-patterns where
  open Category

  op-square : {k l : Level} {𝒞 : Category k l} {A B C D : Obj 𝒞}
              {f₁ : Hom 𝒞 A B} {f₂ : Hom 𝒞 B D} {g₁ : Hom 𝒞 A C} {g₂ : Hom 𝒞 C D} ->
              CommutingSquare 𝒞 f₁ f₂ g₁ g₂ -> CommutingSquare (op 𝒞) g₂ g₁ f₂ f₁
  op-square (commutingSquare f₂f₁=g₂g₁) = commutingSquare (flipEq f₂f₁=g₂g₁)

  unop-square : {k l : Level} {𝒞 : Category k l} {A B C D : Obj 𝒞}
                {f₁ : Hom 𝒞 A B} {f₂ : Hom 𝒞 B D} {g₁ : Hom 𝒞 A C} {g₂ : Hom 𝒞 C D} ->
                CommutingSquare (op 𝒞) g₂ g₁ f₂ f₁ -> CommutingSquare 𝒞 f₁ f₂ g₁ g₂
  unop-square (commutingSquare g₂g₁=f₂f₁) = commutingSquare (flipEq g₂g₁=f₂f₁)

  op-spanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                     {x₁ : Hom 𝒞 X A₁} {x₂ : Hom 𝒞 X A₂} {y₁ : Hom 𝒞 Y A₁} {y₂ : Hom 𝒞 Y A₂} ->
                     SpanReduction 𝒞 x₁ x₂ y₁ y₂ -> CospanReduction (op 𝒞) x₁ x₂ y₁ y₂
  op-spanReduction (reduceSpanBy xy witnessedBy y₁xy=x₁ and y₂xy=x₂) =
    record { u = xy ; ev₁ = flipEq y₁xy=x₁ ; ev₂ = flipEq y₂xy=x₂ }

  unop-cospanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                       {x₁ : Hom 𝒞 X A₁} {x₂ : Hom 𝒞 X A₂} {y₁ : Hom 𝒞 Y A₁} {y₂ : Hom 𝒞 Y A₂} ->
                       CospanReduction (op 𝒞) x₁ x₂ y₁ y₂ -> SpanReduction 𝒞 x₁ x₂ y₁ y₂
  unop-cospanReduction (reduceCospanBy xy witnessedBy x₁=y₁xy and x₂=y₂xy) =
    reduceSpanBy xy witnessedBy (flipEq x₁=y₁xy) and (flipEq x₂=y₂xy)

  op-cospanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                       {x₁ : Hom 𝒞 A₁ X} {x₂ : Hom 𝒞 A₂ X} {y₁ : Hom 𝒞 A₁ Y} {y₂ : Hom 𝒞 A₂ Y} ->
                       CospanReduction 𝒞 x₁ x₂ y₁ y₂ -> SpanReduction (op 𝒞) x₁ x₂ y₁ y₂
  op-cospanReduction (reduceCospanBy yx witnessedBy x₁=yx∘y₁ and x₂=yx∘y₂) =
    reduceSpanBy yx witnessedBy (flipEq x₁=yx∘y₁) and (flipEq x₂=yx∘y₂)

  unop-spanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                       {x₁ : Hom 𝒞 A₁ X} {x₂ : Hom 𝒞 A₂ X} {y₁ : Hom 𝒞 A₁ Y} {y₂ : Hom 𝒞 A₂ Y} ->
                       SpanReduction (op 𝒞) x₁ x₂ y₁ y₂ -> CospanReduction 𝒞 x₁ x₂ y₁ y₂
  unop-spanReduction (reduceSpanBy yx witnessedBy yx∘y₁=x₁ and yx∘y₂=x₂) =
    reduceCospanBy yx witnessedBy (flipEq yx∘y₁=x₁) and (flipEq yx∘y₂=x₂)

  op-uniqueSpanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                           {x₁ : Hom 𝒞 X A₁} {x₂ : Hom 𝒞 X A₂} {y₁ : Hom 𝒞 Y A₁} {y₂ : Hom 𝒞 Y A₂} ->
                           UniqueSpanReduction 𝒞 x₁ x₂ y₁ y₂ -> UniqueCospanReduction (op 𝒞) x₁ x₂ y₁ y₂
  op-uniqueSpanReduction record { reduction = reduction; unique = unique } =
    record
      { reduction = op-spanReduction reduction
      ; unique = λ rd → unique (unop-cospanReduction rd)
      }

  unop-uniqueCospanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                               {x₁ : Hom 𝒞 X A₁} {x₂ : Hom 𝒞 X A₂} {y₁ : Hom 𝒞 Y A₁} {y₂ : Hom 𝒞 Y A₂} ->
                               UniqueCospanReduction (op 𝒞) x₁ x₂ y₁ y₂ -> UniqueSpanReduction 𝒞 x₁ x₂ y₁ y₂
  unop-uniqueCospanReduction record { reduction = reduction ; unique = unique } =
    record
      { reduction = unop-cospanReduction reduction
      ; unique = λ rd -> unique (op-spanReduction rd)
      }

  op-uniqueCospanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                             {x₁ : Hom 𝒞 A₁ X} {x₂ : Hom 𝒞 A₂ X} {y₁ : Hom 𝒞 A₁ Y} {y₂ : Hom 𝒞 A₂ Y} ->
                             UniqueCospanReduction 𝒞 x₁ x₂ y₁ y₂ -> UniqueSpanReduction (op 𝒞) x₁ x₂ y₁ y₂
  op-uniqueCospanReduction record { reduction = reduction ; unique = unique } =
    record
      { reduction = op-cospanReduction reduction
      ; unique = λ rd → unique (unop-spanReduction rd)
      }

  unop-uniqueSpanReduction : {k l : Level} {𝒞 : Category k l} {X Y A₁ A₂ : Obj 𝒞}
                             {x₁ : Hom 𝒞 A₁ X} {x₂ : Hom 𝒞 A₂ X} {y₁ : Hom 𝒞 A₁ Y} {y₂ : Hom 𝒞 A₂ Y} ->
                             UniqueSpanReduction (op 𝒞) x₁ x₂ y₁ y₂ -> UniqueCospanReduction 𝒞 x₁ x₂ y₁ y₂
  unop-uniqueSpanReduction record { reduction = reduction ; unique = unique } =
    record
      { reduction = unop-spanReduction reduction
      ; unique = λ rd → unique (op-cospanReduction rd)
      }
