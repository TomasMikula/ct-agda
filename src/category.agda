open import Data.Product
open import Function using (case_of_)
open import Prelude

record Category (n m : Level) : Set (lsuc (n ⊔ m)) where
  constructor category
  field
    Obj : Set n
    Mph : (A B : Obj) -> Set m
    
    id : {A : Obj} -> Mph A A
    _∘_  : {A B C : Obj} -> (Mph B C) -> (Mph A B) -> (Mph A C)
    
    left-id  : {A B : Obj} {f : Mph A B} -> (id ∘ f ≡ f)
    right-id : {A B : Obj} {f : Mph A B} -> (f ∘ id ≡ f)
    assoc : {A B C D : Obj} {f : Mph C D} {g : Mph B C} {h : Mph A B} -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

  syntax Mph A B = A ~> B

  HomSet = ∃[ A ] ∃[ B ] (A ~> B)

  _>>_ : {A B C : Obj} -> (A ~> B) -> (B ~> C) -> (A ~> C)
  f >> g  = g ∘ f

  assocLR = assoc
  assocRL : {A B C D : Obj} {f : C ~> D} {g : B ~> C} {h : A ~> B} -> f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  assocRL = flipEq assoc

  _=∘=_ : {A B C : Obj} {f₁ f₂ : B ~> C} {g₁ g₂ : A ~> B} -> f₁ ≡ f₂ -> g₁ ≡ g₂ -> f₁ ∘ g₁ ≡ f₂ ∘ g₂
  refl =∘= refl = refl

  _=∘_ : {A B C : Obj} {f₁ f₂ : B ~> C} -> f₁ ≡ f₂ -> (g : A ~> B) -> f₁ ∘ g ≡ f₂ ∘ g
  refl =∘ _ = refl

  _∘=_ : {A B C : Obj} (f : B ~> C) {g₁ g₂ : A ~> B} -> g₁ ≡ g₂ -> f ∘ g₁ ≡ f ∘ g₂
  _ ∘= refl = refl

  infixl 20 _=∘=_
  infixl 20 _=∘_
  infixl 20 _∘=_

-- Opposite category.
op : {n m : Level} -> Category n m -> Category n m
op 𝒞 = record
         { Obj = Obj
         ; Mph = λ A B → Mph B A
         ; id = id
         ; _∘_ = λ f g → g ∘ f
         ; left-id = right-id
         ; right-id = left-id
         ; assoc = flipEq (assoc)
         }
       where
         open Category 𝒞

op-involution : {n m : Level} {𝒞 : Category n m} -> op (op 𝒞) ≡ 𝒞
op-involution {𝒞 = 𝒞} = op-op-𝒞=𝒞 where
  open Category hiding (_∘_ ; assoc)
  open Category 𝒞 using (_∘_ ; assoc)
  open Category (op (op 𝒞)) using () renaming (assoc to op-op-assoc)

  op-op-assoc=assoc : (λ {A} {B} {C} {D} {f} {g} {h} -> op-op-assoc {A} {B} {C} {D} {f} {g} {h})
                      ≡
                      (λ {A} {B} {C} {D} {f} {g} {h} ->       assoc {A} {B} {C} {D} {f} {g} {h})
  op-op-assoc=assoc = ex' (ex' (ex' (ex' (ex' (ex' (ex' flipEq-involution))))))
    where ex' = extensionality'

  op-op-𝒞=𝒞 : op (op 𝒞) ≡ 𝒞
  op-op-𝒞=𝒞 = (λ (a : {A B C D : Obj 𝒞} {f : Mph 𝒞 C D} {g : Mph 𝒞 B C} {h : Mph 𝒞 A B} -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)) -> category (Obj 𝒞) (Mph 𝒞) (id 𝒞) (_∘_) (left-id 𝒞) (right-id 𝒞) a) $= op-op-assoc=assoc

-- Product of categories.
-- Unicode symbol U+2A09.
_⨉_ : {nc mc nd md : Level} (𝒞 : Category nc mc) (𝒟 : Category nd md) -> Category (nc ⊔ nd) (mc ⊔ md)
𝒞 ⨉ 𝒟 = category
  (Obj 𝒞 × Obj 𝒟)
  (λ { (C₁ , D₁) (C₂ , D₂) → Mph 𝒞 C₁ C₂ × Mph 𝒟 D₁ D₂ })
  (id 𝒞 , id 𝒟)
  (λ { (f₁ , g₁) (f₂ , g₂) -> (f₁ 𝒞∘ f₂ , g₁ 𝒟∘ g₂) })
  (𝒞-l-id =,= 𝒟-l-id)
  (𝒞-r-id =,= 𝒟-r-id)
  (𝒞-assoc =,= 𝒟-assoc)
 where
  open Category
  open Category 𝒞 using () renaming (_∘_ to _𝒞∘_ ; left-id to 𝒞-l-id ; right-id to 𝒞-r-id ; assoc to 𝒞-assoc)
  open Category 𝒟 using () renaming (_∘_ to _𝒟∘_ ; left-id to 𝒟-l-id ; right-id to 𝒟-r-id ; assoc to 𝒟-assoc)
