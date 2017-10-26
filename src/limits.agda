open import Prelude
open import category
open import functor
open import nat-trans

module limits {n m : Level} (𝒞 : Category {n} {m}) where
  open Category hiding (_∘_)

  record Diagram {nj mj : Level} (J : Category {nj} {mj}) : Set (n ⊔ m ⊔ nj ⊔ mj) where
    field
      functor : Functor J 𝒞
      
  record Cone {nj mj : Level} {J : Category {nj} {mj}} (D : Diagram J) : Set (n ⊔ m ⊔ nj ⊔ mj) where
    open Diagram D renaming (functor to F)
    field
      C : Obj 𝒞
      trans : NatTrans (ConstFunctor C) F
    τ = NatTrans.τ trans

  record ConeReduction {nj mj : Level} {J : Category {nj} {mj}} {D : Diagram J} (c₁ : Cone D) (c₂ : Cone D) : Set (m ⊔ nj) where
    open Cone c₁ renaming (C to C₁ ; τ to τ₁)
    open Cone c₂ renaming (C to C₂ ; τ to τ₂)
    open Category 𝒞 using (_∘_)
    field
      u : Hom 𝒞 C₁ C₂
      ev : {A : Obj J} -> τ₁ {A} ≡ τ₂ ∘ u
      
  record UniqueConeReduction {nj mj : Level} {J : Category {nj} {mj}} {D : Diagram J} (C₁ : Cone D) (C₂ : Cone D) : Set (m ⊔ nj) where
    field
      reduction : ConeReduction C₁ C₂
      unique : (r : ConeReduction C₁ C₂) -> ConeReduction.u r ≡ ConeReduction.u reduction
      
  record Limit {nj mj : Level} {J : Category {nj} {mj}} {D : Diagram J} (C : Cone D) : Set (m ⊔ n ⊔ mj ⊔ nj) where
    field
      universal : (C₂ : Cone D) -> UniqueConeReduction C₂ C
