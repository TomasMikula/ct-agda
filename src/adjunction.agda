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
    𝜆 : (L ⊚ R) ∸> Id -- 𝜆 here is mathematical italic small lambda, Unicode U+1D706 (to avoid conflict with λ)
    ρ : Id ∸> (R ⊚ L)

  Lρ = L <⊙ ρ
  𝜆L = 𝜆 ⊙> L
  ρR = ρ ⊙> R
  R𝜆 = R <⊙ 𝜆

  field
    𝜆L⊙Lρ=1 : 𝜆L ⊙ Lρ ≡ 𝟙
    R𝜆⊙ρR=1 : R𝜆 ⊙ ρR ≡ 𝟙

homset-adjunction : {k l m : Level} {𝒞 : Category k m} {𝒟 : Category l m} {L : 𝒞 => 𝒟} {R : 𝒟 => 𝒞}
                    (ε : (L -Hom- Id) <∸> (Id -Hom- R)) -> Adjoint L R
homset-adjunction {𝒞 = 𝒞} {𝒟 = 𝒟} {L = L} {R = R} ε' @ (natEquiv ε witnessedBy ε-nat and ε-iso) = record
  { ε = ε'
  ; 𝜆 = natTrans ε⁻¹ (id 𝒞) witnessedBy 𝜆-nat
  ; ρ = natTrans ε   (id 𝒟) witnessedBy ρ-nat
  ; 𝜆L⊙Lρ=1 = equalNatTrans (extensionality' ε⁻¹[1]∘L[ε[1]]≡1)
  ; R𝜆⊙ρR=1 = equalNatTrans (extensionality' R[ε⁻¹[1]]∘ε[1]≡1)
  }
 where
   open NatEquiv (NatEquiv.reverse ε') renaming (τ to ε⁻¹ ; naturality to ε⁻¹-nat)
   open Functor L renaming (mapObj to Lo ; mapArr to Lm ; identity to L-id)
   open Functor R renaming (mapObj to Ro ; mapArr to Rm ; identity to R-id)
   open Category using (Obj ; Mph ; id ; assocRL ; assocLR)
   open Category 𝒞 using () renaming (_∘_ to _∘𝒞_ ; left-id to l-idC ; right-id to r-idC ; _=∘_ to _=∘𝒞_ ; _∘=_ to _∘𝒞=_ ; _=∘=_ to _=∘𝒞=_)
   open Category 𝒟 using () renaming (_∘_ to _∘𝒟_ ; left-id to l-idD ; right-id to r-idD ; _∘=_ to  _∘𝒟=_)
   
   𝜆-nat : {Y Y' : Obj 𝒟} (g : Mph 𝒟 Y Y') → (ε⁻¹ (id 𝒞) ∘𝒟 Lm (Rm g)) ≡ (g ∘𝒟 ε⁻¹ (id 𝒞))
   𝜆-nat {Y} {Y'} g = flipEq l-idD =>>= ((flipEq (ε⁻¹-nat _) =$ _) =>>= (ε⁻¹ $= ((_∘𝒞 (id 𝒞 ∘𝒞 Rm g)) $= R-id =>>= l-idC =>>= l-idC =>>= (flipEq r-idC =>>= (Rm g ∘𝒞_) $= flipEq l-idC)))) =>>= (ε⁻¹-nat (id 𝒞 , g)) =$ (id 𝒞) =>>= assocRL 𝒟 =>>= (_ ∘𝒟= L-id) =>>= r-idD

   ρ-nat : {X X' : Obj 𝒞} (f : Mph 𝒞 X' X) → (ε (id 𝒟) ∘𝒞 f) ≡ (Rm (Lm f) ∘𝒞 ε (id 𝒟))
   ρ-nat {X} {X'} f = flipEq l-idC =>>= (flipEq (R-id) =∘𝒞 _ =>>= (flipEq (ε-nat _) =$ _ =>>= (ε $= (l-idD =>>= l-idD =>>= flipEq r-idD =>>= flipEq r-idD =>>= ((Lm f ∘𝒟 id 𝒟) ∘𝒟= (flipEq L-id)) =>>= assocLR 𝒟) =>>= ((ε-nat _) =$ _ =>>= (assocRL 𝒞 =>>= r-idC)))))

   ε⁻¹ε=1 : {X : Obj 𝒞} {Y : Obj 𝒟} (g : Mph 𝒟 (Lo X) Y) -> ε⁻¹ (ε g) ≡ g
   ε⁻¹ε=1 g = Iso.leftInverse ε-iso =$ g

   εε⁻¹=1 : {X : Obj 𝒞} {Y : Obj 𝒟} (f : Mph 𝒞 X (Ro Y)) -> ε (ε⁻¹ f) ≡ f
   εε⁻¹=1 f = Iso.rightInverse ε-iso =$ f
   
   ε⁻¹[1]∘L[ε[1]]≡1 : {X : Obj 𝒞} -> (ε⁻¹ (id 𝒞) ∘𝒟 Lm (ε {X , Lo X} (id 𝒟)) ≡ id 𝒟)
   ε⁻¹[1]∘L[ε[1]]≡1 = flipEq (ε⁻¹-nat (ε (id 𝒟) , id 𝒟) =$ (id 𝒞) =>>= l-idD) =>>= (ε⁻¹ $= (R-id =∘𝒞= l-idC =>>= l-idC) =>>= ε⁻¹ε=1 (id 𝒟))

   R[ε⁻¹[1]]∘ε[1]≡1 : {Y : Obj 𝒟} -> (Rm (ε⁻¹ {Ro Y , Y} (id 𝒞)) ∘𝒞 ε (id 𝒟) ≡ id 𝒞)
   R[ε⁻¹[1]]∘ε[1]≡1 = (Rm (ε⁻¹ (id 𝒞)) ∘𝒞= (flipEq r-idC)) =>>= flipEq (ε-nat (id 𝒞 , ε⁻¹ (id 𝒞)) =$ (id 𝒟)) =>>= (ε $= ((ε⁻¹ (id 𝒞) ∘𝒟= (l-idD =>>= L-id)) =>>= r-idD)) =>>= εε⁻¹=1 (id 𝒞)

unit-counit-adjunction : {k l m : Level} {𝒞 : Category k m} {𝒟 : Category l m} {L : 𝒞 => 𝒟} {R : 𝒟 => 𝒞}
                         (𝜆 : (L ⊚ R) ∸> Id) (ρ : Id ∸> (R ⊚ L)) ->
                         (𝜆 ⊙> L) ⊙ (L <⊙ ρ) ≡ 𝟙 -> (R <⊙ 𝜆) ⊙ (ρ ⊙> R) ≡ 𝟙 -> Adjoint L R
unit-counit-adjunction {𝒞 = 𝒞} {𝒟} {functor _ Lm _ L-cmp} {functor _ Rm _ R-cmp} 𝜆'@(natTrans 𝜆 witnessedBy 𝜆-nat) ρ'@(natTrans ρ witnessedBy ρ-nat) 𝜆L⊙Lρ=1 R𝜆⊙ρR=1 = record
  { ε = natEquiv (λ φ → Rm φ ∘𝒞 ρ)
        witnessedBy (λ {(f , g) → extensionality λ φ -> R-cmp =∘𝒞 ρ =>>= (assocC =>>= (Rm g ∘𝒞= (R-cmp =∘𝒞 ρ =>>= (assocC =>>= (Rm φ ∘𝒞= flipEq (ρ-nat f)) =>>= assocC'))))})
        and λ { {X , Y} ->
          iso (λ ψ -> 𝜆 ∘𝒟 Lm ψ)
              (extensionality λ φ -> 𝜆 ∘𝒟= L-cmp =>>= assocD' =>>= 𝜆-nat φ =∘𝒟 Lm ρ =>>= assocD =>>= φ ∘𝒟= (NatTrans.τ $= 𝜆L⊙Lρ=1 =$' X) =>>= r-idD)
              (extensionality λ ψ -> R-cmp =∘𝒞 ρ =>>= assocC =>>= (Rm 𝜆 ∘𝒞= flipEq (ρ-nat ψ)) =>>= assocC' =>>= NatTrans.τ $= R𝜆⊙ρR=1 =$' Y =∘𝒞 ψ =>>= l-idC)
        }
  ; 𝜆 = 𝜆'
  ; ρ = ρ'
  ; 𝜆L⊙Lρ=1 = 𝜆L⊙Lρ=1
  ; R𝜆⊙ρR=1 = R𝜆⊙ρR=1
  }
 where
  open Category 𝒞 using () renaming (_∘_ to _∘𝒞_ ; _=∘_ to _=∘𝒞_ ; _∘=_ to _∘𝒞=_ ; assoc to assocC ; assocRL to assocC' ; left-id to l-idC)
  open Category 𝒟 using () renaming (_∘_ to _∘𝒟_ ; _=∘_ to _=∘𝒟_ ; _∘=_ to _∘𝒟=_ ; assoc to assocD ; assocRL to assocD' ; right-id to r-idD)

