open import Data.Product
open import Prelude
open import category
open import functor
open import functor-category
open import hom-functors
open import nat-trans
open import SET
open import morphisms
open import full-faithful

open Category
open Functor

-- Natural transformation corresponding to an element of F(B)
Y-trans : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) (B : Obj 𝒞) -> (mapObj F B) -> ((Hom 𝒞 [-, B ]) ∸> F)
Y-trans {𝒞 = 𝒞} (functor Fo Fm F-id F-cmp) B b =
  natTrans (λ f -> Fm f b)
  witnessedBy λ f -> extensionality λ g -> ((Fm $= left-id 𝒞) =>>= F-cmp) =$ b

-- Element of F(B) corresponding to a natural transformation from 𝒞(-, B) to F
Y-elem : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) (B : Obj 𝒞) -> ((Hom 𝒞 [-, B ]) ∸> F) -> (mapObj F B)
Y-elem {𝒞 = 𝒞} (functor Fo Fm F-id F-cmp) B (natTrans α witnessedBy _) = α {B} (id 𝒞 {B})

-- Yoneda lemma.
Yoneda : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) (B : Obj 𝒞) -> Invertible (Y-trans F B)
Yoneda {𝒞 = 𝒞} F@(functor _ Fm F-id _) B =
  isInvertible
    (Y-elem F B)
    (extensionality λ b -> F-id =$ b)
    (extensionality λ { (natTrans α witnessedBy α-nat) ->
      equalNatTrans (extensionality' (extensionality λ f ->
        Fm f (α (id 𝒞))
          <[ α-nat f =$ id 𝒞 ]=
        α (id 𝒞 ∘𝒞 (id 𝒞 ∘𝒞 f))
          =[ α $= left-id 𝒞 ]>
        α (id 𝒞 ∘𝒞 f)
          =[ α $= left-id 𝒞 ]>
        α f
      ∎ ))
    })
  where
    open Category 𝒞 using () renaming (_∘_ to _∘𝒞_)

-- Yoneda embedding
Y-embed : ∀ {k l} (𝒞 : Category k l) -> (𝒞 => Funct (op 𝒞) (SET l))
Y-embed 𝒞 =
  functor
    (λ B -> Hom 𝒞 [-, B ])
    (λ {B} {A} g -> Y-trans (Hom 𝒞 [-, A ]) B g)
    (equalNatTrans (extensionality' (extensionality λ f -> left-id 𝒞 =>>= left-id 𝒞)))
    (equalNatTrans (extensionality' (extensionality λ f -> id 𝒞 ∘𝒞= (assoc 𝒞 =>>= (_ ∘𝒞= (flipEq (left-id 𝒞)))))))
  where
    open Category 𝒞 using () renaming (_∘=_ to _∘𝒞=_)

-- Yoneda embedding is a full and faithful functor.
Y-fully-faithful : ∀ {k l} (𝒞 : Category k l) -> FullyFaithful (Y-embed 𝒞)
Y-fully-faithful 𝒞 = fullyFaithfulFromInvertible {F = Y-embed 𝒞} λ {A B} -> Yoneda (Hom 𝒞 [-, B ]) A


-- Next is a formulation of the Yoneda lemma as a family of isomorphisms in the category of sets
-- and subsequently as a natural equivalence.
-- For that we need that the sets F(B) and the sets of natural transformations from 𝒞(-, B) to F
-- live in the same universe of sets. To that end we will lift the sets F(B) to the universe
-- containing the sets of mentioned natural transformations.

-- Like Y-trans, but the set F(B) is lifted from universe `Set l` to universe `Set (k ⊔ lsuc l)`.
Y-trans' : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) (B : Obj 𝒞) -> Lift {l} {k ⊔ lsuc l} (mapObj F B) -> ((Hom 𝒞 [-, B ]) ∸> F)
Y-trans' F B (lift b) = Y-trans F B b

-- Like Y-elem, but the set F(B) is lifted from universe `Set l` to universe `Set (k ⊔ lsuc l)`.
Y-elem' : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) (B : Obj 𝒞) -> ((Hom 𝒞 [-, B ]) ∸> F) -> Lift {l} {k ⊔ lsuc l} (mapObj F B)
Y-elem' F B α = lift (Y-elem F B α)

-- Yoneda lemma as an isomorphism
Yoneda' : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) (B : Obj 𝒞) -> Iso (SET (lsuc l ⊔ k)) (Y-trans' F B)
Yoneda' F B with Yoneda F B
... | isInvertible el el∘tr=id tr∘el=id =
  iso
    (λ α -> lift (el α))
    (extensionality λ { (lift b) -> lift $= (el∘tr=id =$ b) })
    tr∘el=id

-- Returns a functor mapping each object B of 𝒞ᵒᵖ to the set of natural transformations from 𝒞(-, B) to F.
Hom-to-F : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) -> ((op 𝒞) => SET (lsuc l ⊔ k))
Hom-to-F {𝒞 = 𝒞} F@(functor Fo Fm F-id F-cmp) =
  functor
    (λ B -> (Hom 𝒞 [-, B ]) ∸> F)
    (λ {f (natTrans α witnessedBy α-nat) ->
      natTrans (λ g -> α (f ∘𝒞 g))
      witnessedBy λ g -> extensionality λ h ->
        α (f ∘𝒞 (id 𝒞 ∘𝒞 (h ∘𝒞 g)))
          =[ α $= (f ∘𝒞= left-id 𝒞) ]>
        α (f ∘𝒞 (h ∘𝒞 g))
          <[ α $= left-id 𝒞 ]=
        α (id 𝒞 ∘𝒞 (f ∘𝒞 (h ∘𝒞 g)))
          <[ α $= (id 𝒞 ∘𝒞= assoc 𝒞) ]=
        α (id 𝒞 ∘𝒞 ((f ∘𝒞 h) ∘𝒞 g))
          =[ α-nat g =$ (f ∘𝒞 h) ]>
        Fm g (α (f ∘𝒞 h))
      ∎
    })
    (extensionality λ { (natTrans α witnessedBy _) ->
      equalNatTrans (extensionality' (extensionality λ f -> α $= left-id 𝒞)) })
    (extensionality λ { (natTrans α witnessedBy _) ->
      equalNatTrans (extensionality' (extensionality λ f -> α $= assoc 𝒞)) })
  where
    open Category 𝒞 using () renaming (_∘_ to _∘𝒞_ ; _∘=_ to _∘𝒞=_)

-- Lift set-valued functor to sets from a bigger universe.
liftF : ∀ {k l m} {𝒞 : Category k l} (F : 𝒞 => SET m) {n : Level} -> (𝒞 => SET (m ⊔ n))
liftF {m = m} (functor Fo Fm F-id F-cmp) {n} =
  functor
    (λ C -> Lift {m} {n} (Fo C))
    (λ f -> λ { (lift x) → lift (Fm f x) })
    (extensionality λ { (lift x) -> lift $= (F-id =$ x) })
    (extensionality λ { (lift x) -> lift $= (F-cmp =$ x) })

-- Yoneda lemma as a natural equivalence.
YonedaEquiv : ∀ {k l} {𝒞 : Category k l} (F : (op 𝒞) => (SET l)) -> NatEquiv (liftF F) (Hom-to-F F)
YonedaEquiv {𝒞 = 𝒞} F@(functor _ _ _ F-cmp) =
  natEquiv (λ {B} b -> Y-trans' F B b) witnessedBy
    ( (λ f -> extensionality λ { (lift b) ->
        equalNatTrans (extensionality' (extensionality λ g -> flipEq F-cmp =$ b))
      })
    , λ {A} -> Yoneda' F A
    )
