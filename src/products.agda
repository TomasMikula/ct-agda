open import Agda.Primitive
open import Data.Product
open import Prelude
open import category

module products {n m : Level} (𝒞 : Category n m) where
  open Category 𝒞
  open import morphisms 𝒞
  open import patterns 𝒞

  record Product (A B : Obj) : Set (n ⊔ m) where
    field
      P : Obj
      π₁ : Hom P A
      π₂ : Hom P B
      universal : {Q : Obj} (q₁ : Hom Q A) (q₂ : Hom Q B) -> UniqueSpanReduction q₁ q₂ π₁ π₂

    reduceCone : {Q : Obj} (q₁ : Hom Q A) (q₂ : Hom Q B) -> SpanReduction q₁ q₂ π₁ π₂
    reduceCone q₁ q₂ = UniqueSpanReduction.reduction (universal q₁ q₂)

    proveId : (red : SpanReduction π₁ π₂ π₁ π₂) -> SpanReduction.u red ≡ id
    proveId red =
      let
        open UniqueSpanReduction (universal π₁ π₂)
        u_id  = unique (identitySpanReduction π₁ π₂)
        u_red = unique red
      in u_red =>>= flipEq u_id

  product_uniqueness : {A B : Obj} (p q : Product A B) -> Σ (Hom (Product.P p) (Product.P q)) Iso
  product_uniqueness p q =
    let
      open Product p renaming (π₁ to p₁ ; π₂ to p₂ ; reduceCone to reduceCone-p ; proveId to proveId-p)
      open Product q renaming (π₁ to q₁ ; π₂ to q₂ ; reduceCone to reduceCone-q ; proveId to proveId-q)

      p-q : SpanReduction p₁ p₂ q₁ q₂
      p-q = reduceCone-q p₁ p₂

      q-p : SpanReduction q₁ q₂ p₁ p₂
      q-p = reduceCone-p q₁ q₂

      pq = SpanReduction.u p-q
      qp = SpanReduction.u q-p

    in pq , iso qp (proveId-p (composeSpanReductions q-p p-q)) (proveId-q (composeSpanReductions p-q q-p))
