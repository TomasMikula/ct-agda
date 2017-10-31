open import Prelude
open import Data.Product

record Category {n m : Level} : Set (lsuc (n ⊔ m)) where
  field
    Obj : Set n
    Hom : (A B : Obj) -> Set m
    
    id : {A : Obj} -> Hom A A
    _∘_  : {A B C : Obj} -> (Hom B C) -> (Hom A B) -> (Hom A C)
    
    left_id  : {A B : Obj} {f : Hom A B} -> (id ∘ f ≡ f)
    right_id : {A B : Obj} {f : Hom A B} -> (f ∘ id ≡ f)
    assoc : {A B C D : Obj} {f : Hom C D} {g : Hom B C} {h : Hom A B} -> (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

  _>>_ : {A B C : Obj} -> (Hom A B) -> (Hom B C) -> (Hom A C)
  f >> g  = g ∘ f

  HomSet = Σ Obj (λ A -> Σ Obj (λ B -> Hom A B))

op : {n m : Level} -> Category {n} {m} -> Category {n} {m}
op 𝒞 = record
         { Obj = Obj
         ; Hom = λ A B → Hom B A
         ; id = id
         ; _∘_ = λ f g → g ∘ f
         ; left_id = right_id
         ; right_id = left_id
         ; assoc = λ {f g h} → flipEq (assoc)
         }
       where
         open Category 𝒞

