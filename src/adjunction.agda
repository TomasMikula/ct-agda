{-# OPTIONS --rewriting #-}

open import Data.Product
open import Prelude
open import category
open import functor
open import hom-functors
open import nat-trans
open import morphisms using (Iso ; iso)

record Adjoint {k l m : Level} {𝒞 : Category k m} {𝒟 : Category l m} (L : 𝒞 => 𝒟) (R : 𝒟 => 𝒞) : Set (lsuc m ⊔ l ⊔ k) where
  field
    ε : (L -Hom- Id) <∸> (Id -Hom- R)

  ε⁻¹ = NatEquiv.reverse ε

  field
    𝜆 : (L ⦾ R) ∸> Id -- 𝜆 here is mathematical italic small lambda, Unicode U+1D706 (to avoid conflict with λ)
    ρ : Id ∸> (R ⦾ L)

  Lρ = L ⧀ ρ
  𝜆L = 𝜆 ⧁ L
  ρR = ρ ⧁ R
  R𝜆 = R ⧀ 𝜆

  field
    𝜆L⦿Lρ=1 : 𝜆L ⦿ Lρ ≡ 𝟙
    R𝜆⦿ρR=1 : R𝜆 ⦿ ρR ≡ 𝟙

homset-adjunction : {k l m : Level} {𝒞 : Category k m} {𝒟 : Category l m} {L : 𝒞 => 𝒟} {R : 𝒟 => 𝒞}
                    (ε : (L -Hom- Id) <∸> (Id -Hom- R)) -> Adjoint L R
homset-adjunction {𝒞 = 𝒞} {𝒟 = 𝒟} {L = L} {R = R} ε' @ (natEquiv ε witnessedBy ε-nat and ε-iso) = record
  { ε = ε'
  ; 𝜆 = natTrans ε⁻¹ (id 𝒞) witnessedBy 𝜆-nat
  ; ρ = natTrans ε   (id 𝒟) witnessedBy ρ-nat
  ; 𝜆L⦿Lρ=1 = equalNatTrans (extensionality' ε⁻¹[1]∘L[ε[1]]≡1)
  ; R𝜆⦿ρR=1 = equalNatTrans (extensionality' R[ε⁻¹[1]]∘ε[1]≡1)
  }
 where
   open NatEquiv (NatEquiv.reverse ε') renaming (τ to ε⁻¹ ; naturality to ε⁻¹-nat)
   open Functor L renaming (mapObj to Lo ; mapArr to Lm ; identity to L-id)
   open Functor R renaming (mapObj to Ro ; mapArr to Rm ; identity to R-id)
   open Category using (Obj ; Mph ; id ; left-id ; right-id ; assoc)
   open Category 𝒞 using () renaming (_∘_ to _∘𝒞_ ; _=∘_ to _=∘𝒞_ ; _∘=_ to _∘𝒞=_ ; _=∘=_ to _=∘𝒞=_)
   open Category 𝒟 using () renaming (_∘_ to _∘𝒟_ ; _∘=_ to  _∘𝒟=_)
   
   𝜆-nat : {Y Y' : Obj 𝒟} (g : Mph 𝒟 Y Y') → (ε⁻¹ (id 𝒞 {Ro Y'}) ∘𝒟 Lm (Rm g)) ≡ (g ∘𝒟 ε⁻¹ (id 𝒞 {Ro Y}))
   𝜆-nat {Y} {Y'} g =
                         ε⁻¹ (id 𝒞 {Ro Y'})  ∘𝒟  Lm (Rm g)      <[ left-id 𝒟 ]=
         id 𝒟 {Y'}  ∘𝒟  (ε⁻¹ (id 𝒞 {Ro Y'})  ∘𝒟  Lm (Rm g))     <[ ε⁻¹-nat (Rm g , id 𝒟 {Y'}) =$ id 𝒞 {Ro Y'} ]=
     ε⁻¹ (Rm (id 𝒟 {Y'}) ∘𝒞  (id 𝒞 {Ro Y'}   ∘𝒞      Rm g)   )  =[ ε⁻¹ $= (R-id =∘𝒞 _) ]>
     ε⁻¹ ( id 𝒞 {Ro Y'}  ∘𝒞  (id 𝒞 {Ro Y'}   ∘𝒞      Rm g)   )  =[ ε⁻¹ $= left-id 𝒞 ]>
     ε⁻¹ (                    id 𝒞 {Ro Y'}   ∘𝒞      Rm g    )  =[ ε⁻¹ $= left-id 𝒞 ]>
     ε⁻¹ (Rm g                                               )  <[ ε⁻¹ $= right-id 𝒞 ]=
     ε⁻¹ (Rm g  ∘𝒞        id 𝒞 {Ro Y}                        )  <[ ε⁻¹ $= (Rm g ∘𝒞= right-id 𝒞) ]=
     ε⁻¹ (Rm g  ∘𝒞  (     id 𝒞 {Ro Y}   ∘𝒞      id 𝒞 {Ro Y}) )  =[ ε⁻¹-nat (id 𝒞 {Ro Y} , g) =$ (id 𝒞 {Ro Y}) ]>
             g  ∘𝒟  (ε⁻¹ (id 𝒞 {Ro Y})  ∘𝒟  Lm (id 𝒞 {Ro Y}))   <[ assoc 𝒟 ]=
            (g  ∘𝒟   ε⁻¹ (id 𝒞 {Ro Y})) ∘𝒟  Lm (id 𝒞 {Ro Y})    =[ _ ∘𝒟= L-id ]>
            (g  ∘𝒟   ε⁻¹ (id 𝒞 {Ro Y})) ∘𝒟  id 𝒟 {Lo (Ro Y)}    =[ right-id 𝒟 ]>
             g  ∘𝒟   ε⁻¹ (id 𝒞 {Ro Y})                          ∎

   ρ-nat : {X X' : Obj 𝒞} (f : Mph 𝒞 X' X) → (ε (id 𝒟 {Lo X}) ∘𝒞 f) ≡ (Rm (Lm f) ∘𝒞 ε (id 𝒟 {Lo X'}))
   ρ-nat {X} {X'} f =
                            ε (id 𝒟 {Lo X})  ∘𝒞     f           <[ left-id 𝒞 ]=
     id 𝒞 {Ro (Lo X)}  ∘𝒞  (ε (id 𝒟 {Lo X})  ∘𝒞     f)          <[ R-id =∘𝒞 _ ]=
     Rm (id 𝒟 {Lo X})  ∘𝒞  (ε (id 𝒟 {Lo X})  ∘𝒞     f)          <[ ε-nat (f , id 𝒟 {Lo X}) =$ id 𝒟 {Lo X} ]=
     ε ( id 𝒟 {Lo X}   ∘𝒟  (   id 𝒟 {Lo X}   ∘𝒟  Lm f) )        =[ ε $= left-id 𝒟 ]>
     ε (                       id 𝒟 {Lo X}   ∘𝒟  Lm f  )        =[ ε $= left-id 𝒟 ]>
     ε ( Lm f                                          )        <[ ε $= right-id 𝒟 ]=
     ε ( Lm f   ∘𝒟     id 𝒟 {Lo X'}                    )        <[ ε $= (Lm f ∘𝒟= right-id 𝒟) ]=
     ε ( Lm f   ∘𝒟    (id 𝒟 {Lo X'}  ∘𝒟 id 𝒟 {Lo X'})  )        <[ ε $= (Lm f ∘𝒟= (id 𝒟 {Lo X'} ∘𝒟= L-id)) ]=
     ε ( Lm f   ∘𝒟    (id 𝒟 {Lo X'}  ∘𝒟 Lm (id 𝒞 {X'})))        =[ ε-nat (id 𝒞 {X'}, Lm f) =$ id 𝒟 {Lo X'} ]>
     Rm (Lm f)  ∘𝒞 (ε (id 𝒟 {Lo X'}) ∘𝒞     id 𝒞 {X'})          =[ Rm (Lm f) ∘𝒞= right-id 𝒞 ]>
     Rm (Lm f)  ∘𝒞  ε (id 𝒟 {Lo X'})                            ∎

   ε⁻¹ε=1 : {X : Obj 𝒞} {Y : Obj 𝒟} (g : Mph 𝒟 (Lo X) Y) -> ε⁻¹ (ε g) ≡ g
   ε⁻¹ε=1 g = Iso.leftInverse ε-iso =$ g

   εε⁻¹=1 : {X : Obj 𝒞} {Y : Obj 𝒟} (f : Mph 𝒞 X (Ro Y)) -> ε (ε⁻¹ f) ≡ f
   εε⁻¹=1 f = Iso.rightInverse ε-iso =$ f
   
   ε⁻¹[1]∘L[ε[1]]≡1 : {X : Obj 𝒞} -> (ε⁻¹ (id 𝒞 {Ro (Lo X)}) ∘𝒟 Lm (ε (id 𝒟 {Lo X})) ≡ id 𝒟 {Lo X})
   ε⁻¹[1]∘L[ε[1]]≡1 {X} =
                               ε⁻¹ (id 𝒞 {Ro (Lo X)}) ∘𝒟 Lm (ε (id 𝒟 {Lo X}))      <[ left-id 𝒟 ]=
              id 𝒟 {Lo X}  ∘𝒟 (ε⁻¹ (id 𝒞 {Ro (Lo X)}) ∘𝒟 Lm (ε (id 𝒟 {Lo X})))     <[ ε⁻¹-nat (ε (id 𝒟) , id 𝒟) =$ (id 𝒞) ]=
     ε⁻¹ (Rm (id 𝒟 {Lo X}) ∘𝒞 (     id 𝒞 {Ro (Lo X)}  ∘𝒞     ε (id 𝒟 {Lo X})))     =[ ε⁻¹ $= (R-id =∘𝒞= left-id 𝒞) ]>
     ε⁻¹ (id 𝒞 {Ro (Lo X)} ∘𝒞                                ε (id 𝒟 {Lo X}) )     =[ ε⁻¹ $= left-id 𝒞 ]>
     ε⁻¹ (                                                   ε (id 𝒟 {Lo X}) )     =[ ε⁻¹ε=1 (id 𝒟 {Lo X}) ]>
                                                                id 𝒟 {Lo X}        ∎

   R[ε⁻¹[1]]∘ε[1]≡1 : {Y : Obj 𝒟} -> (Rm (ε⁻¹ (id 𝒞 {Ro Y})) ∘𝒞 ε (id 𝒟 {Lo (Ro Y)}) ≡ id 𝒞 {Ro Y})
   R[ε⁻¹[1]]∘ε[1]≡1 {Y} =
     Rm (ε⁻¹ (id 𝒞 {Ro Y}))  ∘𝒞   ε (id 𝒟 {Lo (Ro Y)})                             <[ right-id 𝒞 ]=
    (Rm (ε⁻¹ (id 𝒞 {Ro Y}))  ∘𝒞   ε (id 𝒟 {Lo (Ro Y)}))  ∘𝒞  id 𝒞 {Ro Y}           =[ assoc 𝒞 ]>
     Rm (ε⁻¹ (id 𝒞 {Ro Y}))  ∘𝒞  (ε (id 𝒟 {Lo (Ro Y)})   ∘𝒞  id 𝒞 {Ro Y})          <[ ε-nat (id 𝒞 , ε⁻¹ (id 𝒞)) =$ id 𝒟 ]=
     ε  (ε⁻¹ (id 𝒞 {Ro Y})   ∘𝒟  (   id 𝒟 {Lo (Ro Y)}    ∘𝒟  Lm (id 𝒞 {Ro Y})))    =[ ε $= (_ ∘𝒟= (left-id 𝒟 =>>= L-id)) ]>
     ε  (ε⁻¹ (id 𝒞 {Ro Y})   ∘𝒟                              id 𝒟 {Lo (Ro Y)} )    =[ ε $= right-id 𝒟 ]>
     ε  (ε⁻¹ (id 𝒞 {Ro Y})                                                    )    =[ εε⁻¹=1 (id 𝒞) ]>
              id 𝒞 {Ro Y}                                                          ∎

unit-counit-adjunction : {k l m : Level} {𝒞 : Category k m} {𝒟 : Category l m} {L : 𝒞 => 𝒟} {R : 𝒟 => 𝒞}
                         (𝜆 : (L ⦾ R) ∸> Id) (ρ : Id ∸> (R ⦾ L)) ->
                         (𝜆 ⧁ L) ⦿ (L ⧀ ρ) ≡ 𝟙 -> (R ⧀ 𝜆) ⦿ (ρ ⧁ R) ≡ 𝟙 -> Adjoint L R
unit-counit-adjunction {𝒞 = 𝒞} {𝒟} {functor _ Lm _ L-cmp} {functor _ Rm _ R-cmp}
                       𝜆'@(natTrans 𝜆 witnessedBy 𝜆-nat) ρ'@(natTrans ρ witnessedBy ρ-nat)
                       𝜆L⦿Lρ=1 R𝜆⦿ρR=1 = record
  { ε = natEquiv (λ φ → Rm φ ∘𝒞 ρ)
        witnessedBy (λ {(f , g) → extensionality λ φ ->
          R-cmp =∘𝒞 ρ =>>= (assocC =>>= (Rm g ∘𝒞= (R-cmp =∘𝒞 ρ =>>= (assocC =>>= (Rm φ ∘𝒞= flipEq (ρ-nat f)) =>>= assocC'))))
        })
        and λ { {X , Y} ->
          iso (λ ψ -> 𝜆 ∘𝒟 Lm ψ)
              (extensionality λ φ -> 𝜆 ∘𝒟= L-cmp =>>= assocD' =>>= 𝜆-nat φ =∘𝒟 Lm ρ =>>= assocD =>>= φ ∘𝒟= (NatTrans.τ $= 𝜆L⦿Lρ=1 =$' X) =>>= r-idD)
              (extensionality λ ψ -> R-cmp =∘𝒞 ρ =>>= assocC =>>= (Rm 𝜆 ∘𝒞= flipEq (ρ-nat ψ)) =>>= assocC' =>>= NatTrans.τ $= R𝜆⦿ρR=1 =$' Y =∘𝒞 ψ =>>= l-idC)
        }
  ; 𝜆 = 𝜆'
  ; ρ = ρ'
  ; 𝜆L⦿Lρ=1 = 𝜆L⦿Lρ=1
  ; R𝜆⦿ρR=1 = R𝜆⦿ρR=1
  }
 where
  open Category 𝒞 using () renaming (_∘_ to _∘𝒞_ ; _=∘_ to _=∘𝒞_ ; _∘=_ to _∘𝒞=_ ; assoc to assocC ; assocRL to assocC' ; left-id to l-idC)
  open Category 𝒟 using () renaming (_∘_ to _∘𝒟_ ; _=∘_ to _=∘𝒟_ ; _∘=_ to _∘𝒟=_ ; assoc to assocD ; assocRL to assocD' ; right-id to r-idD)

