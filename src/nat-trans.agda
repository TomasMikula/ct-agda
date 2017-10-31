open import Prelude
open import category
open import functor

record NatTrans {nc mc nd md : Level} {C : Category nc mc} {D : Category nd md}  (F G : Functor C D) : Set (nc ⊔ mc ⊔ nd ⊔ md) where
  open Category hiding (_∘_)
  open Category D using (_∘_)
  open Functor F renaming (mapObj to Fobj ; mapArr to Farr)
  open Functor G renaming (mapObj to Gobj ; mapArr to Garr)
  field
    τ : {A : Obj C} -> Hom D (Fobj A) (Gobj A)
    naturality : {A B : Obj C} (f : Hom C A B) -> τ ∘ (Farr f) ≡ (Garr f) ∘ τ
