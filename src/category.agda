open import Data.Product
open import Function using (case_of_)
open import Prelude

record Category (n m : Level) : Set (lsuc (n ⊔ m)) where
  constructor category
  field
    Obj : Set n
    Hom : (A B : Obj) -> Set m
    
    id : {A : Obj} -> Hom A A
    _∘_  : {A B C : Obj} -> (Hom B C) -> (Hom A B) -> (Hom A C)
    
    left_id  : {A B : Obj} {f : Hom A B} -> (id ∘ f ≡ f)
    right_id : {A B : Obj} {f : Hom A B} -> (f ∘ id ≡ f)
    assoc : {A B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom A B} -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

  HomSet = Σ Obj (λ A -> Σ Obj (λ B -> Hom A B))

  _>>_ : {A B C : Obj} -> (Hom A B) -> (Hom B C) -> (Hom A C)
  f >> g  = g ∘ f

  assocLR = assoc
  assocRL : {A B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom A B} -> f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
  assocRL = flipEq assoc

-- Opposite category.
op : {n m : Level} -> Category n m -> Category n m
op 𝒞 = record
         { Obj = Obj
         ; Hom = λ A B → Hom B A
         ; id = id
         ; _∘_ = λ f g → g ∘ f
         ; left_id = right_id
         ; right_id = left_id
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
  op-op-𝒞=𝒞 = (λ (a : {A B C D : Obj 𝒞} {f : Hom 𝒞 C D} {g : Hom 𝒞 B C} {h : Hom 𝒞 A B} -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)) -> category (Obj 𝒞) (Hom 𝒞) (id 𝒞) (_∘_) (left_id 𝒞) (right_id 𝒞) a) $= op-op-assoc=assoc

-- Product of categories.
_⨂_ : {nc mc nd md : Level} (𝒞 : Category nc mc) (𝒟 : Category nd md) -> Category (nc ⊔ nd) (mc ⊔ md)
𝒞 ⨂ 𝒟 = category
  (Obj 𝒞 × Obj 𝒟)
  (λ { (C₁ , D₁) (C₂ , D₂) → Hom 𝒞 C₁ C₂ × Hom 𝒟 D₁ D₂ })
  (id 𝒞 , id 𝒟)
  (λ { (f₁ , g₁) (f₂ , g₂) -> (f₁ 𝒞∘ f₂ , g₁ 𝒟∘ g₂) })
  (𝒞-l-id =,= 𝒟-l-id)
  (𝒞-r-id =,= 𝒟-r-id)
  (𝒞-assoc =,= 𝒟-assoc)
 where
  open Category
  open Category 𝒞 using () renaming (_∘_ to _𝒞∘_ ; left_id to 𝒞-l-id ; right_id to 𝒞-r-id ; assoc to 𝒞-assoc)
  open Category 𝒟 using () renaming (_∘_ to _𝒟∘_ ; left_id to 𝒟-l-id ; right_id to 𝒟-r-id ; assoc to 𝒟-assoc)
