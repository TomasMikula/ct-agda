open import Agda.Primitive
open import Data.Product
open import Prelude
open import category
open import op-morphisms

module pushouts {n m : Level} (𝒞 : Category n m) where
  open Category 𝒞
  open import morphisms 𝒞
  open import patterns 𝒞
  open import op-patterns

  record Pushout {C A B P : Obj} (f : Mph C A) (g : Mph C B) (f' : Mph B P) (g' : Mph A P) : Set (m ⊔ n) where
    constructor isPushout
    field
      commuting : f' ∘ g ≡ g' ∘ f
      universal : {Q : Obj} {f'' : Mph B Q} {g'' : Mph A Q} (sq : CommutingSquare g f'' f g'') -> UniqueCospanReduction g'' f'' g' f'

    square : CommutingSquare g f' f g'
    square = commutingSquare commuting

    reduceCocone : {Q : Obj} {f'' : Mph B Q} {g'' : Mph A Q} (sq : CommutingSquare g f'' f g'') -> CospanReduction g'' f'' g' f'
    reduceCocone sq = UniqueCospanReduction.reduction (universal sq)
{-
    proveId : (red : CospanReduction (cospan g' f') (cospan g' f')) -> CospanReduction.u red ≡ id
    proveId red = red=u =>>= flipEq id=u
      where
        open UniqueCospanReduction (universal square)
        id=u = unique (identityCospanReduction (cospan g' f'))
        red=u = unique red
-}
  record PushoutOf {C A B : Obj} (f : Mph C A) (g : Mph C B) : Set (n ⊔ m) where
    constructor pushoutData
    field
      P : Obj
      f' : Mph B P
      g' : Mph A P
      pushout : Pushout f g f' g'

    open Pushout pushout public

  open import pullbacks

  co-pushout : {C A B P : Obj} {f : Mph C A} {g : Mph C B} {f' : Mph B P} {g' : Mph A P} ->
               Pushout f g f' g' -> Pullback (op 𝒞) f g f' g'
  co-pushout record { commuting = f'g=g'f ; universal = universal } =
    record
      { commuting = flipEq f'g=g'f
      ; universal = λ sq -> op-uniqueCospanReduction (universal (unop-square sq))
      }

  unco-pullback : {C A B P : Obj} {f : Mph C A} {g : Mph C B} {f' : Mph B P} {g' : Mph A P} ->
                  Pullback (op 𝒞) f g f' g' -> Pushout f g f' g'
  unco-pullback record { commuting = commuting ; universal = universal } =
    record
      { commuting = flipEq commuting
      ; universal = λ sq → unop-uniqueSpanReduction (universal (op-square sq))
      }

  pushout_uniqueness : {C A B : Obj} {f : Mph C A} {g : Mph C B}
                       {P₁ : Obj} {f₁ : Mph B P₁} {g₁ : Mph A P₁} (p₁ : Pushout f g f₁ g₁)
                       {P₂ : Obj} {f₂ : Mph B P₂} {g₂ : Mph A P₂} (p₂ : Pushout f g f₂ g₂) ->
                       Σ[ u ∈ (Mph P₂ P₁) ] Iso u
  pushout_uniqueness p1 p2 with pullback_uniqueness (op 𝒞) (co-pushout p1) (co-pushout p2)
  ... | (u , op-iso-u) = u , unop-iso op-iso-u

  pushout_of_epi_is_epi : {A B C : Obj} {f : Mph C A} {g : Mph C B}
                          {P : Obj} {f' : Mph B P} {g' : Mph A P} -> Pushout f g f' g' -> Epi f -> Epi f'
  pushout_of_epi_is_epi {f = f} {g = g} po e =
    unop-mono (pullback_of_mono_is_mono (op 𝒞) (co-pushout po) (op-epi e))

  --
  --   A → B → C
  --   ↓   ↓   ↓
  --   D → E → F
  --
  pushout_pasting : {A B C D E F : Obj} {ab : Mph A B} {bc : Mph B C} {ad : Mph A D} {be : Mph B E} {cf : Mph C F} {de : Mph D E} {ef : Mph E F} ->
                     Pushout ad ab be de -> Pushout be bc cf ef -> Pushout ad (bc ∘ ab) cf (ef ∘ de)
  pushout_pasting p1 p2 = unco-pullback (pullback_pasting (op 𝒞) (co-pushout p1) (co-pushout p2))
