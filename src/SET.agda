open import Prelude
open import category

-- Category of sets and functions
SET : (l : Level) -> Category _ _
SET l = record
  { Obj = Set l
  ; Mph = λ A B → (A -> B)
  ; id = λ x → x
  ; _∘_ = λ f g x → f (g x)

  ; left_id = λ {f} → refl
  ; right_id = λ {f} → refl
  ; assoc = λ {f g h} → refl
  }
