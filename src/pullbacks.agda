open import Agda.Primitive
open import Data.Product
open import Prelude
open import category

module pullbacks {n m : Level} (𝒞 : Category n m) where
  open Category 𝒞
  open import morphisms 𝒞
  open import patterns 𝒞
  open import products 𝒞

  record Pullback {P A B C : Obj} (f : Hom A C) (g : Hom B C) (f' : Hom P B) (g' : Hom P A) : Set (m ⊔ n) where
    field
      commuting : f ∘ g' ≡ g ∘ f'
      universal : {Q : Obj} {f'' : Hom Q B} {g'' : Hom Q A} (sq : CommutingSquare g'' f f'' g) -> UniqueSpanReduction g'' f'' g' f'

    square : CommutingSquare g' f f' g
    square = commutingSquare commuting

    reduceCone : {Q : Obj} {f'' : Hom Q B} {g'' : Hom Q A} (sq : CommutingSquare g'' f f'' g) -> SpanReduction g'' f'' g' f'
    reduceCone sq = UniqueSpanReduction.reduction (universal sq)

    proveId : (red : SpanReduction g' f' g' f') -> SpanReduction.u red ≡ id
    proveId red = red=u =>>= flipEq id=u
      where
        open UniqueSpanReduction (universal square)
        id=u = unique (identitySpanReduction g' f')
        red=u = unique red

  record PullbackOf {C A B : Obj} (f : Hom A C) (g : Hom B C) : Set (n ⊔ m) where
    constructor pullbackData
    field
      P : Obj
      f' : Hom P B
      g' : Hom P A
      pullback : Pullback f g f' g'

    open Pullback pullback public


  pullback_uniqueness : {C A B : Obj} {f : Hom A C} {g : Hom B C}
                        {P₁ : Obj} {f₁ : Hom P₁ B} {g₁ : Hom P₁ A} (p₁ : Pullback f g f₁ g₁)
                        {P₂ : Obj} {f₂ : Hom P₂ B} {g₂ : Hom P₂ A} (p₂ : Pullback f g f₂ g₂) ->
                        Σ[ u ∈ (Hom P₁ P₂) ] Iso u
  pullback_uniqueness {f₁ = f₁} {g₁} p1 {f₂ = f₂} {g₂} p2 =
    let
      open Pullback p1 renaming (square to sq1 ; reduceCone to reduce1 ; proveId to proveId1)
      open Pullback p2 renaming (square to sq2 ; reduceCone to reduce2 ; proveId to proveId2)

      r12 : SpanReduction g₁ f₁ g₂ f₂
      r12 = reduce2 sq1

      r21 : SpanReduction g₂ f₂ g₁ f₁
      r21 = reduce1 sq2

      u12 = SpanReduction.u r12
      u21 = SpanReduction.u r21
    in u12 , record
               { inverse = u21
               ; leftInverse  = proveId1 (composeSpanReductions r21 r12)
               ; rightInverse = proveId2 (composeSpanReductions r12 r21)
               }

  pullback_uniqueness' : {C A B : Obj} {f : Hom A C} {g : Hom B C}
                         (p₁ : PullbackOf f g) (p₂ : PullbackOf f g) ->
                         Σ[ u ∈ (Hom (PullbackOf.P p₁) (PullbackOf.P p₂)) ] Iso u
  pullback_uniqueness' (pullbackData _ _ _ p₁) (pullbackData _ _ _ p₂) = pullback_uniqueness p₁ p₂
               
  pullback_of_mono_is_mono : {A B C : Obj} {f : Hom A C} {g : Hom B C}
                             {P : Obj} {f' : Hom P B} {g' : Hom P A} ->
                             Pullback f g f' g' -> Mono f -> Mono f'
  pullback_of_mono_is_mono {f = f} {g = g} {f' = f'} {g' = g'} p m =
    let
      open Pullback p renaming (commuting to fg'=gf')
    in mono λ {X} {α} {β} f'α=f'β ->
      let
        gf'α=gf'β = (g ∘_) $= f'α=f'β
        fg'α=gf'β = flipEq assoc =>>= ((_∘ α) $= fg'=gf') =>>=  assoc =>>= gf'α=gf'β
        fg'α=fg'β = fg'α=gf'β =>>= flipEq assoc =>>= flipEq ((_∘ β) $= fg'=gf') =>>= assoc

        sq2 : CommutingSquare (g' ∘ α) f (f' ∘ β)  g
        sq2 = commutingSquare fg'α=gf'β

        αr : SpanReduction (g' ∘ α) (f' ∘ β) g' f'
        αr = record { u = α ; ev₁ = refl ; ev₂ = f'α=f'β }

        βr : SpanReduction (g' ∘ α) (f' ∘ β) g' f'
        βr = record { u = β ; ev₁ = flipEq (Mono.elimL m fg'α=fg'β) ; ev₂ = refl }

        open UniqueSpanReduction (universal sq2)
        αu = unique αr
        βu = unique βr
      in αu =>>= flipEq βu

  pullback_of_mono_is_mono' : {A B C : Obj} {f : Hom A C} {g : Hom B C} -> (p : PullbackOf f g) -> Mono f -> Mono (PullbackOf.f' p)
  pullback_of_mono_is_mono' (pullbackData _ _ _ p) = pullback_of_mono_is_mono p

  --
  --   Q ---------╮
  --   | ↘        v
  --   |  A → B → C
  --   |  ↓   ↓   ↓
  --   ╰> D → E → F
  --
  pullback_pasting : {A B C D E F : Obj} {ab : Hom A B} {bc : Hom B C} {ad : Hom A D} {be : Hom B E} {cf : Hom C F} {de : Hom D E} {ef : Hom E F} ->
                     Pullback cf ef be bc -> Pullback be de ad ab -> Pullback cf (ef ∘ de) ad (bc ∘ ab)
  pullback_pasting {A} {B} {C} {D} {E} {F} {ab} {bc} {ad} {be} {cf} {de} {ef} p1 p2 =
    let
      open Pullback p1 renaming (commuting to cf∘bc=ef∘be ; universal to universal1 ; square to square1)
      open Pullback p2 renaming (commuting to be∘ab=de∘ad ; universal to universal2 ; square to square2)
    in record
         { commuting = flipEq assoc =>>= ((_∘ ab) $= cf∘bc=ef∘be) =>>= assoc =>>= ((ef ∘_) $= be∘ab=de∘ad) =>>= flipEq assoc
         ; universal = λ {Q} {qd} {qc} sq →
             let
               open CommutingSquare sq renaming (evidence to cf∘qc=ef∘de∘qd)

               sq₁ : CommutingSquare qc cf (de ∘ qd) ef
               sq₁ = commutingSquare (cf∘qc=ef∘de∘qd =>>= assoc)

               sq1_b : UniqueSpanReduction qc (de ∘ qd) bc be
               sq1_b = universal1 sq₁

               open UniqueSpanReduction sq1_b renaming (u to qb ; ev₁ to bc∘qb=qc ; ev₂ to de∘qd=be∘qb ; unique to unique1)

               sq₂ : CommutingSquare qb be qd de
               sq₂ = commutingSquare de∘qd=be∘qb

               sq2_a : UniqueSpanReduction qb qd ab ad
               sq2_a = universal2 sq₂

               open UniqueSpanReduction sq2_a renaming (u to qa ; ev₁ to ab∘qa=qb ; ev₂ to qd=ad∘qa ; unique to unique2)
             in record
                  { reduction = record
                      { u = qa
                      ; ev₁ = assoc =>>= ((bc ∘_) $= ab∘qa=qb =>>= bc∘qb=qc)
                      ; ev₂ = qd=ad∘qa
                      }
                  ; unique = λ red →
                    let
                      open SpanReduction red renaming (u to qa' ; ev₁ to bc∘ab∘qa'=qc ; ev₂ to ad∘qa'=qd)
                      red₁ : SpanReduction qc (de ∘ qd) bc be
                      red₁ = record
                        { u = ab ∘ qa'
                        ; ev₁ = assocRL =>>= bc∘ab∘qa'=qc
                        ; ev₂ = assocRL =>>= ((_∘ qa') $= be∘ab=de∘ad) =>>= assoc =>>= ((de ∘_) $= ad∘qa'=qd)
                        }
                      ab∘qa'=qb = unique1 red₁

                      red₂ : SpanReduction qb qd ab ad
                      red₂ = record
                        { u = qa'
                        ; ev₁ = ab∘qa'=qb
                        ; ev₂ = ad∘qa'=qd
                        }
                      qa'=qa = unique2 red₂
                    in qa'=qa
                  }
         }

  open import equalizers 𝒞

  -- Construction of pullbacks from products and equalizers
  pullbacks_from_products_and_equalizers :
    ((A B : Obj) -> Product A B) ->
    ({A B : Obj} -> (f g : Hom A B) -> EqualizerOf f g) ->
    {A₁ A₂ C : Obj} -> (f : Hom A₁ C) -> (g : Hom A₂ C) -> PullbackOf f g
  pullbacks_from_products_and_equalizers prod equ {A₁} {A₂} {C} f g =
    let
      open Product (prod A₁ A₂) renaming (P to A₁xA₂ ; universal to prodUniversal)
      open EqualizerOf (equ (f ∘ π₁) (g ∘ π₂)) renaming (E to P ; evidence to f∘π₁∘e=g∘π₂∘e ; universal to equUniversal)
    in record
       { P = P
       ; f' = π₂ ∘ e
       ; g' = π₁ ∘ e
       ; pullback = record
         { commuting = assocRL =>>= f∘π₁∘e=g∘π₂∘e =>>= assocLR
         ; universal = λ { {P₂} {f'} {g'} (commutingSquare fg'=gf') →
             let
               open UniqueSpanReduction (prodUniversal g' f') renaming (u to u₀ ; ev₁ to π₁u₀=g' ; ev₂ to π₂u₀=f' ; unique to prodUnique)

               fπ₁u₀=gπ₂u₀ : ((f ∘ π₁) ∘ u₀) ≡ ((g ∘ π₂) ∘ u₀)
               fπ₁u₀=gπ₂u₀ = assocLR =>>= ((f ∘_) $= π₁u₀=g') =>>= fg'=gf' =>>= ((g ∘_) $= (flipEq π₂u₀=f')) =>>= assocRL
               open UniqueMorphismReduction (equUniversal (isEqualizing fπ₁u₀=gπ₂u₀)) renaming (u to u ; ev to eu=u₀ ; unique to equUnique)
             in record
               { reduction = record
                 { u = u
                 ; ev₁ = assoc =>>= ((π₁ ∘_) $= eu=u₀) =>>= π₁u₀=g'
                 ; ev₂ = assoc =>>= ((π₂ ∘_) $= eu=u₀) =>>= π₂u₀=f'
                 }
               ; unique = λ { record { u = u₂ ; ev₁ = π₁eu₂=g' ; ev₂ = π₂eu₂=f' } →
                   let
                     eu₂=u₀ = prodUnique (record { u = e ∘ u₂ ; ev₁ = assocRL =>>= π₁eu₂=g' ; ev₂ = assocRL =>>= π₂eu₂=f' })
                     u₂=u = equUnique (record { u = u₂ ; ev =  eu₂=u₀ })
                   in u₂=u
                 }
               }
           }
         }
       }
