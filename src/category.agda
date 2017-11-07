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
