open import Agda.Primitive
open import Data.Product
open import Prelude
open import category
import morphisms

module pullbacks {n m : Level} (𝒞 : Category n m) where
  open Category 𝒞
  open morphisms 𝒞

  --
  --      f₁
  --    A -> B
  --  f₂|    |g₁
  --    v    v
  --    C -> D
  --      g₂
  --
  record CommutingSquare {A B C D : Obj} (f₁ : Hom A B) (g₁ : Hom B D) (f₂ : Hom A C) (g₂ : Hom C D) : Set m where
    constructor commutingSquare
    field
      evidence : g₁ ∘ f₁ ≡ g₂ ∘ f₂

  --        g₂
  --   P₂ ------╮
  --   | ↘u  g₁ v
  --   |  P₁ -> A
  -- f₂| f₁|    |f
  --   |   v    v
  --   ╰-> B -> C
  --         g
  record PullbackSquareReduction {P₁ P₂ A B C : Obj}{f : Hom A C}{g : Hom B C}
                                 {f₂ : Hom P₂ B} {g₂ : Hom P₂ A}   {f₁ : Hom P₁ B} {g₁ : Hom P₁ A}
                                 (sq₂ : CommutingSquare g₂ f f₂ g) (sq₁ : CommutingSquare g₁ f f₁ g) : Set m where
    field
      u : Hom P₂ P₁
      ev₁ : g₂ ≡ g₁ ∘ u
      ev₂ : f₂ ≡ f₁ ∘ u

  composePullbackSquareReductions : {P₁ P₂ P₃ A B C : Obj} {f : Hom A C} {g : Hom B C}
                                    {f₁ : Hom P₁ B} {g₁ : Hom P₁ A} {sq₁ : CommutingSquare g₁ f f₁ g}
                                    {f₂ : Hom P₂ B} {g₂ : Hom P₂ A} {sq₂ : CommutingSquare g₂ f f₂ g}
                                    {f₃ : Hom P₃ B} {g₃ : Hom P₃ A} {sq₃ : CommutingSquare g₃ f f₃ g} ->
                                    PullbackSquareReduction sq₂ sq₃ -> PullbackSquareReduction sq₁ sq₂ ->
                                    PullbackSquareReduction sq₁ sq₃
  composePullbackSquareReductions r23 r12 =
    record
      { u = u₂₃ ∘ u₁₂
      ; ev₁ = g₁=g₂u₁₂ =>>= ((_∘ u₁₂) $= g₂=g₃u₂₃) =>>= assoc
      ; ev₂ = f₁=f₂u₁₂ =>>= ((_∘ u₁₂) $= f₂=f₃u₂₃) =>>= assoc
      }
    where
      open PullbackSquareReduction r23 renaming (u to u₂₃ ; ev₁ to g₂=g₃u₂₃ ; ev₂ to f₂=f₃u₂₃)
      open PullbackSquareReduction r12 renaming (u to u₁₂ ; ev₁ to g₁=g₂u₁₂ ; ev₂ to f₁=f₂u₁₂)

  identityPullbackSquareReduction : {P A B C : Obj} {f : Hom A C} {g : Hom B C} {f' : Hom P B} {g' : Hom P A}
                              (sq : CommutingSquare g' f f' g) -> PullbackSquareReduction sq sq
  identityPullbackSquareReduction sq = record { u = id ; ev₁ = flipEq right_id ; ev₂ = flipEq right_id }

  record UniquePullbackSquareReduction
    {A B C : Obj}{f : Hom A C}{g : Hom B C}
    {P₂ : Obj }{f₂ : Hom P₂ B}{g₂ : Hom P₂ A}{P₁ : Obj}{f₁ : Hom P₁ B}{g₁ : Hom P₁ A}
    (sq₂ : CommutingSquare g₂ f f₂ g) (sq₁ : CommutingSquare g₁ f f₁ g) : Set m
   where
    field
      reduction : PullbackSquareReduction sq₂ sq₁
      unique : (red : PullbackSquareReduction sq₂ sq₁) -> PullbackSquareReduction.u red ≡ PullbackSquareReduction.u reduction

    u   = PullbackSquareReduction.u   reduction
    ev₁ = PullbackSquareReduction.ev₁ reduction
    ev₂ = PullbackSquareReduction.ev₂ reduction

  record Pullback {P A B C : Obj} (f : Hom A C) (g : Hom B C) (f' : Hom P B) (g' : Hom P A) : Set (m ⊔ n) where
    field
      commuting : f ∘ g' ≡ g ∘ f'
      universal : {Q : Obj} {f'' : Hom Q B} {g'' : Hom Q A} (sq : CommutingSquare g'' f f'' g) -> UniquePullbackSquareReduction sq (commutingSquare commuting)

    square : CommutingSquare g' f f' g
    square = commutingSquare commuting

    reduceCone : {Q : Obj} {f'' : Hom Q B} {g'' : Hom Q A} (sq : CommutingSquare g'' f f'' g) -> PullbackSquareReduction sq square
    reduceCone sq = reduction where open UniquePullbackSquareReduction (universal sq)

    proveId : (red : PullbackSquareReduction square square) -> PullbackSquareReduction.u red ≡ id
    proveId red = red=u =>>= flipEq id=u
      where
        open UniquePullbackSquareReduction (universal square)
        id=u = unique (identityPullbackSquareReduction square)
        red=u = unique red

  record PullbackOf {C A B : Obj} (f : Hom A C) (g : Hom B C) : Set (n ⊔ m) where
    field
      P : Obj
      f' : Hom P B
      g' : Hom P A
      pullback : Pullback f g f' g'

    open Pullback pullback public


  pullback_uniqueness : {C A B : Obj} {f : Hom A C} {g : Hom B C} (p1 p2 : PullbackOf f g) -> Σ (Hom (PullbackOf.P p1) (PullbackOf.P p2)) Iso
  pullback_uniqueness p1 p2 =
    let
      open PullbackOf p1 renaming (square to pb1 ; reduceCone to reduce1 ; proveId to proveId1)
      open PullbackOf p2 renaming (square to pb2 ; reduceCone to reduce2 ; proveId to proveId2)

      r12 : PullbackSquareReduction pb1 pb2
      r12 = reduce2 pb1

      r21 : PullbackSquareReduction pb2 pb1
      r21 = reduce1 pb2

      u12 = PullbackSquareReduction.u r12
      u21 = PullbackSquareReduction.u r21
    in u12 , record
               { inverse = u21
               ; leftInverse  = proveId1 (composePullbackSquareReductions r21 r12)
               ; rightInverse = proveId2 (composePullbackSquareReductions r12 r21)
               }
               
  pullback_of_mono_is_mono : {A B C : Obj} {f : Hom A C} {g : Hom B C} -> (p : PullbackOf f g) -> Mono f -> Mono (PullbackOf.f' p)
  pullback_of_mono_is_mono {f = f} {g = g} p m =
    let
      open PullbackOf p
      fg'=gf' = commuting
    in mono λ {X} {α} {β} f'α=f'β ->
      let
        gf'α=gf'β = (g ∘_) $= f'α=f'β
        fg'α=gf'β = flipEq assoc =>>= ((_∘ α) $= fg'=gf') =>>=  assoc =>>= gf'α=gf'β
        fg'α=fg'β = fg'α=gf'β =>>= flipEq assoc =>>= flipEq ((_∘ β) $= fg'=gf') =>>= assoc

        p2 : CommutingSquare (g' ∘ α) f (f' ∘ β)  g
        p2 = commutingSquare fg'α=gf'β

        αr : PullbackSquareReduction p2 square
        αr = record { u = α ; ev₁ = refl ; ev₂ = flipEq f'α=f'β }

        βr : PullbackSquareReduction p2 square
        βr = record { u = β ; ev₁ = Mono.elimL m fg'α=fg'β ; ev₂ = refl }

        open UniquePullbackSquareReduction (universal p2)
        αu = unique αr
        βu = unique βr
      in αu =>>= flipEq βu

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

               sq1_b : UniquePullbackSquareReduction sq₁ square1
               sq1_b = universal1 sq₁

               open UniquePullbackSquareReduction sq1_b renaming (u to qb ; ev₁ to qc=bc∘qb ; ev₂ to de∘qd=be∘qb ; unique to unique1)

               sq₂ : CommutingSquare qb be qd de
               sq₂ = commutingSquare (flipEq de∘qd=be∘qb)

               sq2_a : UniquePullbackSquareReduction sq₂ square2
               sq2_a = universal2 sq₂

               open UniquePullbackSquareReduction sq2_a renaming (u to qa ; ev₁ to qb=ab∘qa ; ev₂ to qd=ad∘qa ; unique to unique2)
             in record
                  { reduction = record
                      { u = qa
                      ; ev₁ = qc=bc∘qb =>>= ((bc ∘_) $= qb=ab∘qa) =>>= flipEq assoc
                      ; ev₂ = qd=ad∘qa
                      }
                  ; unique = λ red →
                    let
                      open PullbackSquareReduction red renaming (u to qa' ; ev₁ to qc=bc∘ab∘qa' ; ev₂ to qd=ad∘qa')
                      red₁ : PullbackSquareReduction sq₁ square1
                      red₁ = record
                        { u = ab ∘ qa'
                        ; ev₁ =  qc=bc∘ab∘qa' =>>= assoc
                        ; ev₂ = ((de ∘_) $= qd=ad∘qa') =>>= flipEq assoc =>>= ((_∘ qa') $= (flipEq be∘ab=de∘ad)) =>>= assoc
                        }
                      ab∘qa'=qb = unique1 red₁

                      red₂ : PullbackSquareReduction sq₂ square2
                      red₂ = record
                        { u = qa'
                        ; ev₁ = flipEq ab∘qa'=qb
                        ; ev₂ = qd=ad∘qa'
                        }
                      qa'=qa = unique2 red₂
                    in qa'=qa
                  }
         }

  open import products 𝒞
  open import equalizers 𝒞

  -- Construction of pullbacks from products and equalizers
  pullback_construction : ((A B : Obj) -> Product A B) ->
                          ({A B : Obj} -> (f g : Hom A B) -> EqualizerOf f g) ->
                          {A₁ A₂ C : Obj} -> (f : Hom A₁ C) -> (g : Hom A₂ C) -> PullbackOf f g
  pullback_construction prod equ {A₁} {A₂} {C} f g =
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
               open UniqueSpanReduction (prodUniversal (span g' f')) renaming (u to u₀ ; ev₁ to π₁u₀=g' ; ev₂ to π₂u₀=f' ; unique to prodUnique)

               fπ₁u₀=gπ₂u₀ : ((f ∘ π₁) ∘ u₀) ≡ ((g ∘ π₂) ∘ u₀)
               fπ₁u₀=gπ₂u₀ = assocLR =>>= ((f ∘_) $= π₁u₀=g') =>>= fg'=gf' =>>= ((g ∘_) $= (flipEq π₂u₀=f')) =>>= assocRL
               open UniqueEqualizingReduction (equUniversal (equalizing fπ₁u₀=gπ₂u₀)) renaming (u to u ; ev to eu=u₀ ; unique to equUnique)
             in record
               { reduction = record
                 { u = u
                 ; ev₁ = flipEq (assoc =>>= ((π₁ ∘_) $= eu=u₀) =>>= π₁u₀=g')
                 ; ev₂ = flipEq (assoc =>>= ((π₂ ∘_) $= eu=u₀) =>>= π₂u₀=f')
                 }
               ; unique = λ { record { u = u₂ ; ev₁ = g'=π₁eu₂ ; ev₂ = f'=π₂eu₂ } →
                   let
                     eu₂=u₀ = prodUnique (record { u = e ∘ u₂ ; ev₁ = assocRL =>>= flipEq g'=π₁eu₂ ; ev₂ = assocRL =>>= flipEq f'=π₂eu₂ })
                     u₂=u = equUnique (record { u = u₂ ; ev =  eu₂=u₀ })
                   in u₂=u
                 }
               }
           }
         }
       }
