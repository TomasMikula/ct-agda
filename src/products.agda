open import Agda.Primitive
open import Data.Product
open import Prelude
open import category
import morphisms

module products {n m : Level} (𝒞 : Category {n} {m}) where
  open Category 𝒞
  open morphisms 𝒞

  record Span (A A₁ A₂ : Obj) : Set m where
    constructor span
    field
      f₁ : Hom A A₁
      f₂ : Hom A A₂

  record SpanReduction {X A A₁ A₂ : Obj} (s : Span X A₁ A₂) (r : Span A A₁ A₂) : Set m where
    open Span s renaming (f₁ to s₁ ; f₂ to s₂)
    open Span r renaming (f₁ to r₁ ; f₂ to r₂)
    field
      u : Hom X A
      ev₁ : (r₁ ∘ u) ≡ s₁
      ev₂ : (r₂ ∘ u) ≡ s₂

  composeSpanReductions : {X Y Z A₁ A₂ : Obj} {x : Span X A₁ A₂} {y : Span Y A₁ A₂} {z : Span Z A₁ A₂} -> SpanReduction y z -> SpanReduction x y -> SpanReduction x z
  composeSpanReductions = λ yz xy →
    let
      open SpanReduction yz renaming (u to u_yz ; ev₁ to ev_yz₁ ; ev₂ to ev_yz₂)
      open SpanReduction xy renaming (u to u_xy ; ev₁ to ev_xy₁ ; ev₂ to ev_xy₂)
    in record
      { u = u_yz ∘ u_xy
      ; ev₁ = flipEq assoc =>>= ((_∘ u_xy) $= ev_yz₁) =>>= ev_xy₁
      ; ev₂ = flipEq assoc =>>= ((_∘ u_xy) $= ev_yz₂) =>>= ev_xy₂
      }

  identitySpanReduction : {A A₁ A₂ : Obj} (s : Span A A₁ A₂) -> SpanReduction s s
  identitySpanReduction s = record { u = id ; ev₁ = right_id ; ev₂ = right_id }

  record UniqueSpanReduction {X A A₁ A₂ : Obj} (s : Span X A₁ A₂) (r : Span A A₁ A₂) : Set m where
    field
      reduction : SpanReduction s r
      unique : (red₂ : SpanReduction s r) -> SpanReduction.u red₂ ≡ SpanReduction.u reduction

    u   = SpanReduction.u   reduction
    ev₁ = SpanReduction.ev₁ reduction
    ev₂ = SpanReduction.ev₂ reduction

  record Product (A B : Obj) : Set (n ⊔ m) where
    field
      P : Obj
      cone : Span P A B
      universal : {X : Obj} (s : Span X A B) -> UniqueSpanReduction s cone

    π₁ = Span.f₁ cone
    π₂ = Span.f₂ cone

    reduceCone : {X : Obj} (s : Span X A B) -> SpanReduction s cone
    reduceCone = λ s → UniqueSpanReduction.reduction (universal s)

    proveId : (red : SpanReduction cone cone) -> SpanReduction.u red ≡ id
    proveId red =
      let
        open UniqueSpanReduction (universal cone)
        u_id  = unique (identitySpanReduction cone)
        u_red = unique red
      in u_red =>>= flipEq u_id

  product_uniqueness : {A B : Obj} (p1 p2 : Product A B) -> Σ (Hom (Product.P p1) (Product.P p2)) Iso
  product_uniqueness p1 p2 =
    let
      open Product p1 renaming (cone to cone1 ; reduceCone to reduceCone1 ; proveId to proveId1)
      open Product p2 renaming (cone to cone2 ; reduceCone to reduceCone2 ; proveId to proveId2)

      r12 : SpanReduction cone1 cone2
      r12 = reduceCone2 cone1

      r21 : SpanReduction cone2 cone1
      r21 = reduceCone1 cone2

      u12 = SpanReduction.u r12
      u21 = SpanReduction.u r21

    in u12 , record
               { inverse = u21
               ; leftInverse  = proveId1 (composeSpanReductions r21 r12)
               ; rightInverse = proveId2 (composeSpanReductions r12 r21)
               }
