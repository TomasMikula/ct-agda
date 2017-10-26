open import Agda.Primitive
open import Relation.Binary.Core public using (_≡_; refl)
open import Data.Product

_=$=_ : {n m : Level} {A : Set n} {B : Set m} {f g : A -> B} {a1 a2 : A} (p : f ≡ g) (q : a1 ≡ a2) -> (f a1) ≡ (g a2)
refl =$= refl = refl

_$=_ : {n m : Level} {A : Set n} {B : Set m} {a1 a2 : A} (f : A -> B) (q : a1 ≡ a2) -> (f a1) ≡ (f a2)
f $= refl = refl

_=>>=_ : {n : Level} {A : Set n} {a b c : A} (p : a ≡ b) (q : b ≡ c) -> (a ≡ c)
refl =>>= refl = refl

infixl 20 _=$=_
infixl 20 _$=_
infixl 20 _=>>=_

flipEq : {n : Level} {A : Set n} {a b : A} (p : a ≡ b) -> b ≡ a
flipEq refl = refl

coerce : {n : Level} {A B : Set n} -> A ≡ B -> A -> B
coerce refl a = a


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


-- Category of sets and functions
Sets : Category
Sets = record
         { Obj = Set
         ; Hom = λ A B → (A -> B)
         ; id = λ x → x
         ; _∘_ = λ f g x → f (g x)

         ; left_id = λ {f} → refl
         ; right_id = λ {f} → refl
         ; assoc = λ {f g h} → refl
         }


module Morphisms {n m : Level} (𝒞 : Category {n} {m}) where
  open Category 𝒞
  
  record Mono {A B : Obj} (f : Hom A B) : Set (m ⊔ n) where
    constructor mono
    field
      elimL : { X : Obj } {g h : Hom X A} -> ((f ∘ g) ≡ (f ∘ h)) -> (g ≡ h)

  record Epi {A B : Obj} (f : Hom A B) : Set (m ⊔ n) where
    constructor epi
    field
      elimR : { X : Obj } {g h : Hom B X} -> ((g ∘ f) ≡ (h ∘ f)) -> (g ≡ h)
    
  record Section {A B : Obj} (s : Hom A B) : Set m where
    field
      retraction : Hom B A
      evidence : (retraction ∘ s) ≡ id

  record Retraction {A B : Obj} (r : Hom A B) : Set m where
    field
      section : Hom B A
      evidence : (r ∘ section) ≡ id

  record Iso {A B : Obj} (f : Hom A B) : Set m where
    field
      inverse : Hom B A
      leftInverse  : (inverse ∘ f) ≡ id
      rightInverse : (f ∘ inverse) ≡ id

  section_is_mono : {A B : Obj} {f : Hom A B} -> Section f -> Mono f
  section_is_mono {f = f} s = mono λ {x} → λ {g} → λ {h} → λ p → 
    let
      p1 = (λ fg -> retraction ∘ fg) $= p
      p2 = assoc =>>= p1 =>>= flipEq assoc
      p3 = flipEq ((λ i -> i ∘ g) $= evidence) =>>= p2 =>>= ((λ i -> i ∘ h) $= evidence)
      p4 = flipEq left_id =>>= p3 =>>= left_id
    in p4 where
      open Section s

  retraction_is_epi : {A B : Obj} {f : Hom A B} -> Retraction f -> Epi f
  retraction_is_epi {f = f} r = epi λ {x} → λ {g} → λ {h} → λ p → 
    let
      p1 = (λ gf -> gf ∘ section) $= p
      p2 = flipEq assoc =>>= p1 =>>= assoc
      p3 = flipEq ((λ i -> g ∘ i) $= evidence) =>>= p2 =>>= ((λ i -> h ∘ i) $= evidence)
      p4 = flipEq right_id =>>= p3 =>>= right_id
    in p4 where
      open Retraction r

  iso_is_retraction : {A B : Obj} {f : Hom A B} -> Iso f -> Retraction f
  iso_is_retraction i = record { section = Iso.inverse i ; evidence = Iso.rightInverse i }

  iso_is_section : {A B : Obj} {f : Hom A B} -> Iso f -> Section f
  iso_is_section i = record { retraction = Iso.inverse i ; evidence = Iso.leftInverse i }

  mono_retraction_is_iso : {A B : Obj} {f : Hom A B} -> Mono f -> Retraction f -> Iso f
  mono_retraction_is_iso {f = f} m r =
    record { inverse = section
           ; leftInverse = elimL (flipEq assoc =>>= ((λ i -> i ∘ f) $= evidence) =>>= left_id =>>= flipEq right_id)
           ; rightInverse = evidence
           }
    where
      open Mono m
      open Retraction r

  epi_section_is_iso : {A B : Obj} {f : Hom A B} -> Epi f -> Section f -> Iso f
  epi_section_is_iso {f = f} e s =
    record { inverse = retraction
           ; leftInverse = evidence
           ; rightInverse = elimR (assoc =>>= ((λ i -> f ∘ i) $= evidence) =>>= right_id =>>= flipEq left_id)
           }
    where
      open Epi e
      open Section s


module Limits {n m : Level} (𝒞 : Category {n} {m}) where
  open Category 𝒞

  record Span (A A₁ A₂ : Obj) : Set m where
    constructor span
    field
      f₁ : Hom A A₁
      f₂ : Hom A A₂

  record SpanReduction {X A A₁ A₂ : Obj} (s : Span X A₁ A₂) (r : Span A A₁ A₂) : Set m where
    open Span s renaming (f₁ to s₁ ; f₂ to s₂)
    open Span r renaming (f₁ to r₁ ; f₂ to r₂)
    field
      u : Hom X A
      ev₁ : (r₁ ∘ u) ≡ s₁
      ev₂ : (r₂ ∘ u) ≡ s₂

  composeSpanReductions : {X Y Z A₁ A₂ : Obj} {x : Span X A₁ A₂} {y : Span Y A₁ A₂} {z : Span Z A₁ A₂} -> SpanReduction y z -> SpanReduction x y -> SpanReduction x z
  composeSpanReductions = λ yz xy →
    let
      open SpanReduction yz renaming (u to u_yz ; ev₁ to ev_yz₁ ; ev₂ to ev_yz₂)
      open SpanReduction xy renaming (u to u_xy ; ev₁ to ev_xy₁ ; ev₂ to ev_xy₂)
    in record { u = u_yz ∘ u_xy
              ; ev₁ = flipEq assoc =>>= ((λ y -> y ∘ u_xy) $= ev_yz₁) =>>= ev_xy₁
              ; ev₂ = flipEq assoc =>>= ((λ y -> y ∘ u_xy) $= ev_yz₂) =>>= ev_xy₂
              }

  identitySpanReduction : {A A₁ A₂ : Obj} (s : Span A A₁ A₂) -> SpanReduction s s
  identitySpanReduction s = record { u = id ; ev₁ = right_id ; ev₂ = right_id }

  record UniqueSpanReduction {X A A₁ A₂ : Obj} (s : Span X A₁ A₂) (r : Span A A₁ A₂) : Set m where
    field
      reduction : SpanReduction s r
      unique : (red₂ : SpanReduction s r) -> SpanReduction.u red₂ ≡ SpanReduction.u reduction

    u   = SpanReduction.u   reduction
    ev₁ = SpanReduction.ev₁ reduction
    ev₂ = SpanReduction.ev₂ reduction

  record Product (A B : Obj) : Set (n ⊔ m) where
    field
      P : Obj
      cone : Span P A B
      universal : {X : Obj} (s : Span X A B) -> UniqueSpanReduction s cone

    π₁ = Span.f₁ cone
    π₂ = Span.f₂ cone

    reduceCone : {X : Obj} (s : Span X A B) -> SpanReduction s cone
    reduceCone = λ s → UniqueSpanReduction.reduction (universal s)

    proveId : (red : SpanReduction cone cone) -> SpanReduction.u red ≡ id
    proveId red =
      let
        open UniqueSpanReduction (universal cone)
        u_id  = unique (identitySpanReduction cone)
        u_red = unique red
      in u_red =>>= flipEq u_id


  record Equalizing {A B : Obj} (f g : Hom A B) : Set (n ⊔ m) where
    constructor equalizing
    field
      E : Obj
      e : Hom E A
      comm : f ∘ e ≡ g ∘ e

  record EqualizingReduction {A B : Obj} {f g : Hom A B} (eq₂ : Equalizing f g) (eq : Equalizing f g) : Set (n ⊔ m) where
    open Equalizing(eq)
    open Equalizing(eq₂) renaming (E to E₂ ; e to e₂)
    field
      u : Hom E₂ E
      ev : e ∘ u ≡ e₂

  composeEqualizingReductions : {A B : Obj} {f g : Hom A B} {c d e : Equalizing f g} -> EqualizingReduction d e -> EqualizingReduction c d -> EqualizingReduction c e
  composeEqualizingReductions de cd =
    record { u = u_de ∘ u_cd
           ; ev = flipEq assoc =>>= ((λ u -> u ∘ u_cd) $= ev_de) =>>= ev_cd
           } where
               open EqualizingReduction de renaming (u to u_de ; ev to ev_de)
               open EqualizingReduction cd renaming (u to u_cd ; ev to ev_cd)

  identityEqualizingReduction : {A B : Obj} {f g : Hom A B} (e : Equalizing f g) -> EqualizingReduction e e
  identityEqualizingReduction e = record { u = id ; ev = right_id }

  record UniqueEqualizingReduction {A B : Obj} {f g : Hom A B} (eq₂ : Equalizing f g) (eq : Equalizing f g) : Set (n ⊔ m) where
    field
      reduction : EqualizingReduction eq₂ eq
      unique : (red₂ : EqualizingReduction eq₂ eq) -> EqualizingReduction.u red₂ ≡ EqualizingReduction.u reduction

    u = EqualizingReduction.u reduction
    ev = EqualizingReduction.ev reduction

  record Equalizer {A B : Obj} (f g : Hom A B) : Set (n ⊔ m) where
    field
      cone : Equalizing f g
      universal : (eq₂ : Equalizing f g) -> UniqueEqualizingReduction eq₂ cone

    E    = Equalizing.E    cone
    e    = Equalizing.e    cone
    comm = Equalizing.comm cone

    reduceCone : (e2 : Equalizing f g) -> EqualizingReduction e2 cone
    reduceCone e2 = reduction where open UniqueEqualizingReduction (universal e2)

    proveId : (red : EqualizingReduction cone cone) -> EqualizingReduction.u red ≡ id
    proveId red =
      let
        open UniqueEqualizingReduction (universal cone)
        u_id = unique (identityEqualizingReduction cone)
        u_red = unique red
      in u_red =>>= flipEq u_id

  idEqualizer : {A B : Obj} {f g : Hom A B} -> f ≡ g -> Equalizer f g
  idEqualizer {A} f=g =
    record { cone = equalizing A id ((λ h -> h ∘ id) $= f=g)
           ; universal = λ eq →
               let
                 open Equalizing eq using (e)
               in record { reduction = record { u = e
                                              ; ev = left_id
                                              }
                         ; unique = λ red₂ → flipEq left_id =>>= EqualizingReduction.ev red₂
                         }
           }

  record PullingBack {C A B : Obj} (f : Hom A C) (g : Hom B C) : Set (n ⊔ m) where
    field
      P : Obj
      f' : Hom P B
      g' : Hom P A
      comm : f ∘ g' ≡ g ∘ f'

  record PullingBackReduction {C A B : Obj} {f : Hom A C} {g : Hom B C} (pb₂ : PullingBack f g) (pb : PullingBack f g) : Set m where
    open PullingBack pb
    open PullingBack pb₂ renaming (P to P₂ ; f' to f₂' ; g' to g₂')
    field
      u : Hom P₂ P
      ev₁ : f' ∘ u ≡ f₂'
      ev₂ : g' ∘ u ≡ g₂'

  composePullingBackReductions : {C A B : Obj} {f : Hom A C} {g : Hom B C} {p q r : PullingBack f g} -> PullingBackReduction q r -> PullingBackReduction p q -> PullingBackReduction p r
  composePullingBackReductions qr pq =
    record { u = u_qr ∘ u_pq
           ; ev₁ = flipEq assoc =>>= ((λ f -> f ∘ u_pq) $= ev_qr₁) =>>= ev_pq₁
           ; ev₂ = flipEq assoc =>>= ((λ g -> g ∘ u_pq) $= ev_qr₂) =>>= ev_pq₂
           } where
               open PullingBackReduction qr renaming (u to u_qr ; ev₁ to ev_qr₁ ; ev₂ to ev_qr₂)
               open PullingBackReduction pq renaming (u to u_pq ; ev₁ to ev_pq₁ ; ev₂ to ev_pq₂)

  identityPullingBackReduction : {C A B : Obj} {f : Hom A C} {g : Hom B C} (pb : PullingBack f g) -> PullingBackReduction pb pb
  identityPullingBackReduction pb = record { u = id ; ev₁ = right_id ; ev₂ = right_id }

  record UniquePullingBackReduction {C A B : Obj} {f : Hom A C} {g : Hom B C} (pb₂ : PullingBack f g) (pb : PullingBack f g) : Set m where
    field
      reduction : PullingBackReduction pb₂ pb
      unique : (red₂ : PullingBackReduction pb₂ pb) -> PullingBackReduction.u red₂ ≡ PullingBackReduction.u reduction

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
  record PullbackSquareReduction {P₁ P₂ A B C : Obj}{f : Hom A C}{g : Hom B C}{f₂ : Hom P₂ B}{g₂ : Hom P₂ A}{f₁ : Hom P₁ B}{g₁ : Hom P₁ A}
                                 (sq₂ : CommutingSquare g₂ f f₂ g) (sq₁ : CommutingSquare g₁ f f₁ g) : Set m where
    field
      u : Hom P₂ P₁
      ev₁ : g₂ ≡ g₁ ∘ u
      ev₂ : f₂ ≡ f₁ ∘ u

  record UniquePullbackSquareReduction {P₁ P₂ A B C : Obj}{f : Hom A C}{g : Hom B C}{f₂ : Hom P₂ B}{g₂ : Hom P₂ A}{f₁ : Hom P₁ B}{g₁ : Hom P₁ A}
                                       (sq₂ : CommutingSquare g₂ f f₂ g) (sq₁ : CommutingSquare g₁ f f₁ g) : Set m where
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

  record PullbackOf {C A B : Obj} (f : Hom A C) (g : Hom B C) : Set (n ⊔ m) where
    field
      cone : PullingBack f g
      universal : (pb₂ : PullingBack f g) -> UniquePullingBackReduction pb₂ cone

    P = PullingBack.P cone
    f' = PullingBack.f' cone
    g' = PullingBack.g' cone
    comm = PullingBack.comm cone

    reduceCone : (pb : PullingBack f g) -> PullingBackReduction pb cone
    reduceCone pb = reduction where open UniquePullingBackReduction (universal pb)

    proveId : (red : PullingBackReduction cone cone) -> PullingBackReduction.u red ≡ id
    proveId red =
      let
        open UniquePullingBackReduction (universal cone)
        u_id = unique (identityPullingBackReduction cone)
        u_red = unique red
      in u_red =>>= flipEq u_id


  open Morphisms 𝒞

  product_uniqueness : {A B : Obj} (p1 p2 : Product A B) -> Σ (Hom (Product.P p1) (Product.P p2)) Iso
  product_uniqueness p1 p2 =
    let
      open Product p1 renaming (cone to cone1 ; reduceCone to reduceCone1 ; proveId to proveId1)
      open Product p2 renaming (cone to cone2 ; reduceCone to reduceCone2 ; proveId to proveId2)

      r12 : SpanReduction cone1 cone2
      r12 = reduceCone2 cone1

      r21 : SpanReduction cone2 cone1
      r21 = reduceCone1 cone2

      u12 = SpanReduction.u r12
      u21 = SpanReduction.u r21

    in u12 , record { inverse = u21
                    ; leftInverse  = proveId1 (composeSpanReductions r21 r12)
                    ; rightInverse = proveId2 (composeSpanReductions r12 r21)
                    }

  equalizer_uniqueness : {A B : Obj} {f g : Hom A B} (e1 e2 : Equalizer f g) -> Σ (EqualizingReduction (Equalizer.cone e1) (Equalizer.cone e2)) (λ red -> Iso (EqualizingReduction.u red))
  equalizer_uniqueness e1 e2 =
    let
      open Equalizer e1 renaming (cone to cone1 ; reduceCone to redEq1 ; proveId to proveId1)
      open Equalizer e2 renaming (cone to cone2 ; reduceCone to redEq2 ; proveId to proveId2)

      r12 : EqualizingReduction cone1 cone2
      r12 = redEq2 cone1

      r21 : EqualizingReduction cone2 cone1
      r21 = redEq1 cone2

      u21 = EqualizingReduction.u r21
    in r12 , record { inverse = u21
                    ; leftInverse  = proveId1 (composeEqualizingReductions r21 r12)
                    ; rightInverse = proveId2 (composeEqualizingReductions r12 r21)
                    }

  pullback_uniqueness : {C A B : Obj} {f : Hom A C} {g : Hom B C} (p1 p2 : PullbackOf f g) -> Σ (Hom (PullbackOf.P p1) (PullbackOf.P p2)) Iso
  pullback_uniqueness p1 p2 =
    let
      open PullbackOf p1 renaming (cone to pb1 ; reduceCone to reduce1 ; proveId to proveId1)
      open PullbackOf p2 renaming (cone to pb2 ; reduceCone to reduce2 ; proveId to proveId2)

      r12 : PullingBackReduction pb1 pb2
      r12 = reduce2 pb1

      r21 : PullingBackReduction pb2 pb1
      r21 = reduce1 pb2

      u12 = PullingBackReduction.u r12
      u21 = PullingBackReduction.u r21
    in u12 , record { inverse = u21
                    ; leftInverse  = proveId1 (composePullingBackReductions r21 r12)
                    ; rightInverse = proveId2 (composePullingBackReductions r12 r21)
                    }


  equalizer_is_mono : {A B : Obj} {f g : Hom A B} (eq : Equalizer f g) -> Mono (Equalizer.e eq)
  equalizer_is_mono {f = f} {g = g} eq = Morphisms.mono λ {X α β} eα=eβ →
    let
      open Equalizer eq

      fe=ge : f ∘ e ≡ g ∘ e
      fe=ge = Equalizer.comm eq

      feβ=geβ : f ∘ (e ∘ β) ≡ g ∘ (e ∘ β)
      feβ=geβ = flipEq assoc =>>= ((λ h -> h ∘ β) $= fe=ge) =>>= assoc

      eqβ = equalizing X (e ∘ β) feβ=geβ

      redα : EqualizingReduction eqβ cone
      redα = record { u = α ; ev = eα=eβ }

      redβ : EqualizingReduction eqβ cone
      redβ = record { u = β ; ev = refl }

      open UniqueEqualizingReduction (universal eqβ)
      α=u = unique redα
      β=u = unique redβ
    in α=u =>>= flipEq β=u

  epi_equalizer_is_iso : {A B : Obj} {f g : Hom A B} (eq : Equalizer f g) -> Epi (Equalizer.e eq) -> Iso (Equalizer.e eq)
  epi_equalizer_is_iso {f = f} {g = g} eq isEpi =
    let
      open Equalizer eq renaming (comm to fe=ge)

      f=g = Epi.elimR isEpi fe=ge

      idEq : Equalizing f g
      idEq = equalizing _ id ((λ h -> h ∘ id) $= f=g)

      id_to_eq : EqualizingReduction idEq cone
      id_to_eq = UniqueEqualizingReduction.reduction (universal idEq)

      r : Retraction e
      r = record { section = EqualizingReduction.u id_to_eq ; evidence = EqualizingReduction.ev id_to_eq }
    in mono_retraction_is_iso (equalizer_is_mono eq) r

  -- A different proof of the same fact.
  epi_equalizer_is_iso' : {A B : Obj} {f g : Hom A B} (eq : Equalizer f g) -> Epi (Equalizer.e eq) -> Iso (Equalizer.e eq)
  epi_equalizer_is_iso' {f = f} {g = g} eq isEpi =
    let
      open Equalizer eq using (e) renaming (cone to eCone ; comm to fe=ge)

      f=g = Epi.elimR isEpi fe=ge

      idEq : Equalizer f g
      idEq = idEqualizer f=g

      open Equalizer idEq hiding (e) renaming (universal to idUniversal)
      open UniqueEqualizingReduction (idUniversal eCone) renaming (reduction to red ; unique to redUnique)

      open Σ (equalizer_uniqueness eq idEq) renaming (proj₁ to red' ; proj₂ to iso_red')
      u_red'=u_red = redUnique red'
      u_red=e = flipEq (redUnique (record { u = e ; ev = left_id }))
      u_red'=e = u_red'=u_red =>>= u_red=e
    in coerce (Iso $= u_red'=e) iso_red'

  section_is_equalizer : {A B : Obj} {s : Hom A B} (sec : Section s) -> Equalizer (s ∘ Section.retraction sec) id
  section_is_equalizer {A} {B} {s} sec =
    let
      open Section sec renaming (retraction to r ; evidence to rs=id)
    in record { cone = equalizing A s (assoc =>>= ((λ f -> s ∘ f) $= rs=id) =>>= right_id =>>= flipEq left_id)
              ; universal = λ eq₂ →
                let
                  open Equalizing eq₂ renaming (e to e ; comm to sre=e)
                in record { reduction = record { u = r ∘ e
                                               ; ev = flipEq assoc =>>= sre=e =>>= left_id
                                               }
                          ; unique = λ red₂ →
                            let
                              open EqualizingReduction red₂
                            in flipEq left_id =>>= ((λ f -> f ∘ u) $= (flipEq rs=id)) =>>= assoc =>>= ((λ f -> r ∘ f) $= ev)
                          }
              }


  pullback_of_mono_is_mono : {A B C : Obj} {f : Hom A C} {g : Hom B C} -> (p : PullbackOf f g) -> Mono f -> Mono (PullbackOf.f' p)
  pullback_of_mono_is_mono {f = f} {g = g} p m =
    let
      open PullbackOf p
      fg'=gf' = comm
    in mono λ {X} {α} {β} f'α=f'β ->
      let
        gf'α=gf'β = (λ γ -> g ∘ γ) $= f'α=f'β
        fg'α=gf'β = flipEq assoc =>>= ((λ γ -> γ ∘ α) $= fg'=gf') =>>=  assoc =>>= gf'α=gf'β
        fg'α=fg'β = fg'α=gf'β =>>= flipEq assoc =>>= flipEq ((λ γ -> γ ∘ β) $= fg'=gf') =>>= assoc

        p2 : PullingBack f g
        p2 = record { P = X ; f' = f' ∘ β ; g' = g' ∘ α ; comm = fg'α=gf'β }

        αr : PullingBackReduction p2 cone
        αr = record { u = α ; ev₁ = f'α=f'β ; ev₂ = refl }

        βr : PullingBackReduction p2 cone
        βr = record { u = β ; ev₁ = refl ; ev₂ = flipEq (Mono.elimL m  fg'α=fg'β) }

        open UniquePullingBackReduction (universal p2)
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
    in record { commuting = flipEq assoc =>>= ((λ f -> f ∘ ab) $= cf∘bc=ef∘be) =>>= assoc =>>= ((λ f -> ef ∘ f) $= be∘ab=de∘ad) =>>= flipEq assoc
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
                  in record { reduction = record { u = qa
                                                 ; ev₁ = qc=bc∘qb =>>= ((λ f -> bc ∘ f) $= qb=ab∘qa) =>>= flipEq assoc
                                                 ; ev₂ = qd=ad∘qa
                                                 }
                            ; unique = λ red →
                              let
                                open PullbackSquareReduction red renaming (u to qa' ; ev₁ to qc=bc∘ab∘qa' ; ev₂ to qd=ad∘qa')
                                red₁ : PullbackSquareReduction sq₁ square1
                                red₁ = record { u = ab ∘ qa'
                                              ; ev₁ =  qc=bc∘ab∘qa' =>>= assoc
                                              ; ev₂ = ((λ f -> de ∘ f) $= qd=ad∘qa') =>>= flipEq assoc =>>= ((λ f -> f ∘ qa') $= (flipEq be∘ab=de∘ad)) =>>= assoc
                                              }
                                ab∘qa'=qb = unique1 red₁

                                red₂ : PullbackSquareReduction sq₂ square2
                                red₂ = record { u = qa'
                                              ; ev₁ = flipEq ab∘qa'=qb
                                              ; ev₂ = qd=ad∘qa'
                                              }
                                qa'=qa = unique2 red₂
                              in qa'=qa }
              }

  pullback_construction : ((A B : Obj) -> Product A B) ->
                          ({A B : Obj} -> (f g : Hom A B) -> Equalizer f g) ->
                          {A₁ A₂ C : Obj} -> (f : Hom A₁ C) -> (g : Hom A₂ C) -> PullbackOf f g
  pullback_construction prod equ {A₁} {A₂} {C} f g =
    let
      open Product (prod A₁ A₂) renaming (P to A₁xA₂ ; universal to prodUniversal)
      open Equalizer (equ (f ∘ π₁) (g ∘ π₂)) renaming (E to P ; comm to f∘π₁∘e=g∘π₂∘e ; universal to equUniversal)
    in record { cone = record { P = P
                              ; f' = π₂ ∘ e
                              ; g' = π₁ ∘ e
                              ; comm = flipEq assoc =>>= f∘π₁∘e=g∘π₂∘e =>>= assoc
                              }
              ; universal = λ pb₂ →
                let
                  open PullingBack pb₂ renaming (P to P₂ ; f' to f' ; g' to g' ; comm to fg'=gf')
                  open UniqueSpanReduction (prodUniversal (span g' f')) renaming (u to u₀ ; ev₁ to π₁u₀=g' ; ev₂ to π₂u₀=f' ; unique to prodUnique)

                  fπ₁u₀=gπ₂u₀ : ((f ∘ π₁) ∘ u₀) ≡ ((g ∘ π₂) ∘ u₀)
                  fπ₁u₀=gπ₂u₀ = assoc =>>= ((λ h -> f ∘ h) $= π₁u₀=g') =>>= fg'=gf' =>>= ((λ h -> g ∘ h) $= (flipEq π₂u₀=f')) =>>= (flipEq assoc)
                  open UniqueEqualizingReduction (equUniversal (equalizing P₂ u₀ fπ₁u₀=gπ₂u₀)) renaming (u to u ; ev to eu=u₀ ; unique to equUnique)
                in record { reduction = record { u = u
                                               ; ev₁ = assoc =>>= ((λ h -> π₂ ∘ h) $= eu=u₀) =>>= π₂u₀=f'
                                               ; ev₂ = assoc =>>= ((λ h -> π₁ ∘ h) $= eu=u₀) =>>= π₁u₀=g'
                                               }
                          ; unique = λ red₂ →
                              let
                                open PullingBackReduction red₂ renaming (u to u₂ ; ev₁ to π₂eu₂=f' ; ev₂ to π₁eu₂=g')

                                eu₂=u₀ = prodUnique (record { u = e ∘ u₂ ; ev₁ = flipEq assoc =>>= π₁eu₂=g' ; ev₂ = flipEq assoc =>>= π₂eu₂=f' })
                                u₂=u = equUnique (record { u = u₂ ; ev =  eu₂=u₀ })
                              in u₂=u
                          }
              }
