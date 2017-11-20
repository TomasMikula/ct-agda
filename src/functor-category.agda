open import Prelude
open import category
open import functor
open import nat-trans

Funct : ∀ {kc lc kd ld} (𝒞 : Category kc lc) (𝒟 : Category kd ld) -> Category (kc ⊔ lc ⊔ kd ⊔ ld) (kc ⊔ lc ⊔ kd ⊔ ld)
Funct 𝒞 𝒟 =
  category
    (𝒞 => 𝒟)
    NatTrans
    𝟙
    _⊙_
    left-id-⊙
    right-id-⊙
    λ {F G H I α β γ} -> assoc-⊙ {𝒞 = 𝒞} {𝒟 = 𝒟} {F} {G} {H} {I} {α} {β} {γ}
