open import Data.Product
open import Prelude
open import category
open import functor

record F-algebra {k l : Level} {𝒞 : Category k l} (F : 𝒞 => 𝒞) : Set (k ⊔ l) where
  constructor algebra
  open Category
  open Functor F renaming (mapObj to Fₒ)
  field
    A : Obj 𝒞
    α : Mph 𝒞 (Fₒ A) A

-- Category of F-algebras for functor F.
F-Alg : {k l : Level} {𝒞 : Category k l} (F : 𝒞 => 𝒞) -> Category (l ⊔ k) l
F-Alg {𝒞 = 𝒞} F@(functor _ Fm F-id F-cmp) = record
  { Obj = F-algebra F
  ; Mph = AlgMph
  ; id = λ { {algebra A α} -> ( id {A}
                              , ( id ∘ α          =[ left-id ]>
                                       α          <[ right-id ]=
                                       α ∘ id     <[ α ∘= F-id ]=
                                       α ∘ Fm id  ∎ ))}
  ; _∘_ = λ { {algebra A α} {algebra B β} {algebra C γ} (f , f∘β=γ∘Ff) (g , g∘α=β∘Fg) →
    ( f ∘ g
    , ( (f ∘ g) ∘ α        =[ assocLR ]>
         f ∘ (g ∘ α)       =[ f ∘= g∘α=β∘Fg ]>
         f ∘ (β    ∘ Fm g) =[ assocRL ]>
        (f ∘  β)   ∘ Fm g  =[ f∘β=γ∘Ff =∘ Fm g ]>
        (γ ∘ Fm f) ∘ Fm g  =[ assocLR ]>
        γ ∘ (Fm f  ∘ Fm g) <[ γ ∘= F-cmp ]=
        γ ∘ Fm (f ∘     g) ∎ ))}

  ; left-id = equalAlgMphs left-id
  ; right-id = equalAlgMphs right-id
  ; assoc = equalAlgMphs assoc
  }
 where
  open Category 𝒞

  AlgMph : (A B : F-algebra F) -> Set _
  AlgMph (algebra A α) (algebra B β) = Σ[ f ∈ Mph A B ] (f ∘ α ≡ β ∘ (Fm f))
  
  equalAlgMphs : {A B : F-algebra F} {f g : AlgMph A B} -> Σ.proj₁ f ≡ Σ.proj₁ g -> f ≡ g
  equalAlgMphs refl = Σ= (refl , eqUnicity)
