{-# OPTIONS --rewriting #-}

open import Data.Product
open import Prelude
open import category
open import functor
open import nat-trans
open import monoidal

-- Category of functors from 𝒞 to 𝒟.
Funct : ∀ {kc lc kd ld} (𝒞 : Category kc lc) (𝒟 : Category kd ld) -> Category (kc ⊔ lc ⊔ kd ⊔ ld) (kc ⊔ lc ⊔ kd ⊔ ld)
Funct 𝒞 𝒟 =
  category
    (𝒞 => 𝒟)
    NatTrans
    𝟙
    _⦿_
    left-id-⦿
    right-id-⦿
    λ {F G H I α β γ} -> assoc-⦿ {𝒞 = 𝒞} {𝒟 = 𝒟} {F} {G} {H} {I} {α} {β} {γ}

-- Category of endofunctors.
Endo : ∀ {k l} (𝒞 : Category k l) -> Category (k ⊔ l) (k ⊔ l)
Endo 𝒞 = Funct 𝒞 𝒞

-- Monoidal structure on the category of endofunctors.
Endo-⦾-Id : ∀ {k l} (𝒞 : Category k l) -> Monoidal (Endo 𝒞)
Endo-⦾-Id 𝒞 = record
  { ⨂ = functor
      (λ { (F , G) -> F  ⦾  G })
      (λ { (α , β) -> α <⦿> β })
      (λ { {functor _ Fm F-id _ , G} -> equalNatTrans (extensionality' λ {a} ->
        (id ∘ Fm id)  =[ left-id ]>  Fm id  =[ F-id ]>  id ∎
      )})
      (λ { {functor _ F₁ _ F₁-cmp , F₂} {functor _ G₁ _ _ , G₂} {H₁ , H₂}
            {natTrans α₁ witnessedBy α₁-nat , natTrans α₂ witnessedBy α₂-nat}
            {natTrans β₁ witnessedBy β₁-nat , natTrans β₂ witnessedBy β₂-nat} ->
         equalNatTrans (extensionality' λ {a} ->
           (α₁ ∘ β₁) ∘ F₁ (α₂ ∘ β₂)         =[ _ ∘= F₁-cmp ]>
           (α₁ ∘ β₁) ∘ (F₁ α₂ ∘ F₁ β₂)      =[ assocLR =>>= α₁ ∘= assocRL ]>
            α₁ ∘ ((β₁ ∘ F₁ α₂) ∘ F₁ β₂)     =[ _ ∘= (β₁-nat α₂ =∘ _) ]>
            α₁ ∘ ((G₁ α₂ ∘ β₁) ∘ F₁ β₂)     =[ α₁ ∘= assocLR =>>= assocRL ]>
           (α₁ ∘ G₁ α₂) ∘ (β₁ ∘ F₁ β₂)
           ∎)
      })
  ; I = Id
  ; α = 𝟙
  ; α' = 𝟙
  ; α-iso = (equalNatTrans (extensionality' left-id) , equalNatTrans (extensionality' left-id))
  ; α-nat₁ = λ { {functor _ G _ _} {H}
                 {functor _ J _ J-cmp} {K} (natTrans τ witnessedBy _) ->
               equalNatTrans (extensionality' (
                 id ∘ ((τ ∘ J id) ∘ J (G id))         =[ left-id ]>
                       (τ ∘ J id) ∘ J (G id)          =[ assocLR ]>
                        τ ∘ (J id ∘ J (G id))         <[ τ ∘= J-cmp ]=
                        τ ∘ J (id ∘    G id)          <[ right-id ]=
                       (τ ∘ J (id ∘    G id)) ∘ id    ∎
               ))}
  ; α-nat₂ = λ { {functor _ F _ F-cmp} {H}
                 {functor _ J _ _} {K} (natTrans τ witnessedBy _) ->
               equalNatTrans (extensionality' (
                 id ∘ ((id ∘ F τ) ∘ F (J id))         =[ left-id ]>
                       (id ∘ F τ) ∘ F (J id)          =[ assocLR ]>
                        id ∘ (F τ ∘ F (J id))         <[ id ∘= F-cmp ]=
                        id ∘ F (τ ∘    J id)          <[ right-id ]=
                       (id ∘ F (τ ∘    J id)) ∘ id    ∎
               ))}
  ; α-nat₃ = λ { {functor _ F _ F-cmp} {functor _ G _ _} {J} {K} (natTrans τ witnessedBy _) ->
               equalNatTrans (extensionality' (
                 id ∘ ((id ∘ F id) ∘ F (G τ))         =[ left-id ]>
                       (id ∘ F id) ∘ F (G τ)          =[ assocLR ]>
                        id ∘ (F id ∘ F (G τ))         <[ id ∘= F-cmp ]=
                        id ∘ F (id ∘    G τ)          <[ right-id ]=
                       (id ∘ F (id ∘    G τ)) ∘ id    ∎
               ))}
  ; 𝜆 = 𝟙
  ; 𝜆' = 𝟙
  ; 𝜆-iso = (equalNatTrans (extensionality' left-id) , equalNatTrans (extensionality' left-id))
  ; 𝜆-nat = λ {F} {G} τ -> equalNatTrans (extensionality' (left-id =>>= left-id =>>= flipEq right-id))
  ; ρ = 𝟙
  ; ρ' = 𝟙
  ; ρ-iso = (equalNatTrans (extensionality' left-id) , equalNatTrans (extensionality' left-id))
  ; ρ-nat = λ { {functor _ F F-id _} {G} (natTrans τ witnessedBy _) ->
              equalNatTrans (extensionality' (
                id ∘ (τ ∘ F id)    =[ left-id ]>
                      τ ∘ F id     =[ τ ∘= F-id ]>
                      τ ∘   id     ∎
              ))}
  ; coherence-pentagon = λ { {functor _ F F-id _} {functor _ G G-id _} {functor _ H H-id _} {J} ->
                           equalNatTrans (extensionality' (
                             (id ∘ F id) ∘ (id ∘ (id ∘ F (G (H id))))    =[ left-id =∘= left-id ]>
                                   F id  ∘       (id ∘ F (G (H id)))     =[ F-id =∘= left-id ]>
                                     id  ∘             F (G (H id))      =[ id ∘= (F $= (G $= H-id)) ]>
                                     id  ∘             F (G    id )      =[ id ∘= (F $= G-id) ]>
                                     id  ∘             F (     id )      =[ id ∘= F-id ]>
                                     id  ∘                     id        ∎
                           ))}
  ; coherence-triangle = λ {F} {G} -> equalNatTrans (extensionality' right-id)
  }
 where
  open Category 𝒞
