open import Data.Empty
open import Data.Product
open import Data.Sum
open import Prelude
open import category
open import equalizers
open import functor
open import nat-trans
open import products
open import pullbacks
open import patterns

module limits {k l : Level} (𝒞 : Category k l) where
  open Category using (Obj ; Mph ; HomSet ; id)
  open Category 𝒞 using (_∘_ ; assocLR ; assocRL) renaming (id to idC ; left_id to l-id ; right_id to r-id)

  Diagram : {nj mj : Level} (J : Category nj mj) -> Set (k ⊔ l ⊔ nj ⊔ mj)
  Diagram J = Functor J 𝒞
      
  record Cone {nj mj : Level} {J : Category nj mj} (D : Diagram J) : Set (k ⊔ l ⊔ nj ⊔ mj) where
    constructor coneFrom_by_
    field
      C : Obj 𝒞
      trans : NatTrans (ConstFunctor C) D
    τ = NatTrans.τ trans
    naturality = NatTrans.naturality trans

  record ConeReduction {nj mj : Level} {J : Category nj mj} {D : Diagram J} (c₁ : Cone D) (c₂ : Cone D) : Set (l ⊔ nj) where
    constructor reduceConeBy_witnessedBy_
    open Cone c₁ renaming (C to C₁ ; τ to τ₁)
    open Cone c₂ renaming (C to C₂ ; τ to τ₂)
    field
      u : Mph 𝒞 C₁ C₂
      ev : {A : Obj J} -> τ₁ {A} ≡ τ₂ ∘ u
      
  record UniqueConeReduction {nj mj : Level} {J : Category nj mj} {D : Diagram J} (C₁ : Cone D) (C₂ : Cone D) : Set (l ⊔ nj) where
    constructor _uniquely_
    field
      reduction : ConeReduction C₁ C₂
      unique : (r : ConeReduction C₁ C₂) -> ConeReduction.u r ≡ ConeReduction.u reduction
    u = ConeReduction.u reduction
    ev = ConeReduction.ev reduction
      
  record Limit {nj mj : Level} {J : Category nj mj} {D : Diagram J} (C : Cone D) : Set (k ⊔ l ⊔ mj ⊔ nj) where
    field
      universal : (C₂ : Cone D) -> UniqueConeReduction C₂ C

  record LimitOf {nj mj : Level} {J : Category nj mj} (D : Diagram J) : Set (k ⊔ l ⊔ mj ⊔ nj) where
    field
      cone : Cone D
      universal : (c : Cone D) -> UniqueConeReduction c cone
    C = Cone.C cone
    τ = Cone.τ cone

  -- Discrete category on a set of objects.
  discrete : {n : Level} -> Set n -> Category n n
  discrete {n} Obj = record
                       { Obj = Obj
                       ; Mph = λ A B → A ≡ B
                       ; id = refl
                       ; _∘_ = λ g f → f =>>= g
                       ; left_id = eqUnicity
                       ; right_id = eqUnicity
                       ; assoc = eqUnicity
                       }

  discretize : {k l : Level} -> Category k l -> Category k k
  discretize C = discrete (Obj C)

  discreteDiagram : {nj mj : Level} {J : Category nj mj} -> Diagram J -> Diagram (discretize J)
  discreteDiagram D = record
    { mapObj = DObj
    ; mapArr = λ { {A} {.A} refl → idC {DObj A} }
    ; identity = refl
    ; composition = λ {A B C} -> λ { {g = refl} {refl} → flipEq l-id }
    }
    where
      open Functor D renaming (mapObj to DObj ; mapArr to DArr ; identity to Did ; composition to Dcomp)

  discreteCone : {nj mj : Level} {J : Category nj mj} {D : Diagram J} -> Cone D -> Cone (discreteDiagram D)
  discreteCone {J = J} c = record
    { C = Cone.C c
    ; trans = record
        { τ = λ {A} → Cone.τ c {A}
        ; naturality = λ { refl -> r-id =>>= flipEq (l-id)}
        }
    }
                                 
  powerDiagram : {n : Level} (A : Obj 𝒞) (X : Set n) -> Diagram (discrete X)
  powerDiagram A X = ConstFunctor {𝒞₁ = discrete X} A

  Δ-cone : {A : Obj 𝒞} {n : Level} {X : Set n} -> Cone (powerDiagram A X)
  Δ-cone {A} {n} {X} = record { C = A ; trans = record { τ = idC ; naturality = λ f -> l-id =>>= flipEq r-id } }
  
  Δ : {A : Obj 𝒞} {n : Level} {X : Set n} -> (L : LimitOf (powerDiagram A X)) -> Mph 𝒞 A (LimitOf.C L)
  Δ {A} {n} {X} L = UniqueConeReduction.u (LimitOf.universal L Δ-cone)

  pᵢΔ=id : {A : Obj 𝒞} {n : Level} {I : Set n} {i : I} {L : LimitOf (powerDiagram A I)} -> (LimitOf.τ L {i}) ∘ (Δ L) ≡ idC
  pᵢΔ=id {A} {n} {I} {i} {L} = flipEq (UniqueConeReduction.ev (LimitOf.universal L Δ-cone) {i})

  open import morphisms 𝒞
  
  Δ-is-mono : {A : Obj 𝒞} {n : Level} {X : Set n} (x : X) -> (L : LimitOf (powerDiagram A X)) -> Mono (Δ L)
  Δ-is-mono {A} {n} {X} x L = mono λ {Z g h} Δg=Δh → 
    let
      open LimitOf L renaming (C to P ; τ to p)
      pₓ : Mph 𝒞 P A
      pₓ = p {x}
      pₓΔ=id : (pₓ ∘ (Δ L)) ≡ idC
      pₓΔ=id = pᵢΔ=id {L = L}
      pₓΔg=pₓΔh = assocLR =>>= ((pₓ ∘_) $= Δg=Δh) =>>= assocRL
      id∘g=id∘h = ((_∘ g) $= (flipEq pₓΔ=id)) =>>= pₓΔg=pₓΔh =>>= ((_∘ h) $= pₓΔ=id)
    in (flipEq l-id) =>>= id∘g=id∘h =>>= l-id

  equal-under-projections : {A : Obj 𝒞} {n : Level} {X : Set n} {D : Diagram (discrete X)} (L : LimitOf D) {f g : Mph 𝒞 A (LimitOf.C L)} ->
                            ((x : X) -> (LimitOf.τ L {x}) ∘ f ≡ (LimitOf.τ L {x}) ∘ g) -> f ≡ g
  equal-under-projections {A} {_} {X} {D} L {f} {g} pf=pg =
    let
      open LimitOf L renaming (cone to Lcone ; τ to p)
      open Functor D renaming (identity to Did)
      fCone : Cone D
      fCone = record { C = A ; trans = record
                                 { τ = p ∘ f
                                 ; naturality = λ { refl → r-id =>>= (flipEq l-id) =>>= ((_∘ (p ∘ f)) $= flipEq Did)} }
                                 }
      fRed : ConeReduction fCone Lcone
      fRed = record { u = f ; ev = refl }
      gRed : ConeReduction fCone Lcone
      gRed = record { u = g ; ev = pf=pg _ }
      open UniqueConeReduction (universal fCone)
      f=u = unique fRed
      g=u = unique gRed
    in f=u =>>= flipEq g=u

  binaryProductDiagram : (A B : Obj 𝒞) -> Diagram (discrete (Doubleton A B))
  binaryProductDiagram A B = record
    { mapObj = λ { (inl .A) → A ; (inr .B) → B }
    ; mapArr = λ { {inl _} refl → idC ; {inr _} refl → idC}
    ; identity = λ { {inl _} → refl ; {inr _} → refl}
    ; composition = λ { {inl _} {g = refl} {refl} → flipEq l-id
                      ; {inr _} {g = refl} {refl} → flipEq l-id
                      }
    }

  binaryProductFromLimit : {A B : Obj 𝒞} -> LimitOf (binaryProductDiagram A B) -> Product 𝒞 A B
  binaryProductFromLimit {A} {B} L = record { P = P ; π₁ = pa ; π₂ = pb ; universal = universality } where
    open LimitOf L renaming (C to P ; τ to p)
    pa = p {inl A}
    pb = p {inr B}
    universality : {X : Obj 𝒞} (x₁ : Mph 𝒞 X A) (x₂ : Mph 𝒞 X B) → UniqueSpanReduction 𝒞 x₁ x₂ pa pb
    universality {X} x₁ x₂ = record
      { reduction = record
          { u = u
          ; ev₁ = flipEq ev
          ; ev₂ = flipEq ev
          }
      ; unique = sUnique
      }
      where
        sCone : Cone (binaryProductDiagram A B)
        sCone = record
          { C = X
          ; trans = record
            { τ = λ { {inl _} → x₁ ; {inr _} → x₂ }
            ; naturality = λ { {inl _} refl → r-id =>>= flipEq l-id
                             ; {inr _} refl → r-id =>>= flipEq l-id
                             }
            }
          }
        open UniqueConeReduction (universal sCone)
        sUnique : (red₂ : SpanReduction 𝒞 x₁ x₂ pa pb) → SpanReduction.u red₂ ≡ u
        sUnique red₂ = unique (record
          { u = SpanReduction.u red₂
          ; ev = λ { {inl _} → flipEq (SpanReduction.ev₁ red₂)
                   ; {inr _} → flipEq (SpanReduction.ev₂ red₂)
                   }
          })

  -- Freyd theorem
  limits-from-products-and-pullbacks :
    -- Given arbitrary products
    ({l : Level} {X : Set l} (D : Diagram (discrete X)) -> LimitOf D) ->
    -- and binary pullbacks,
    ({A B C : Obj 𝒞} (f : Mph 𝒞 A C) (g : Mph 𝒞 B C) -> PullbackOf 𝒞 f g) ->
    -- for any diagram
    {k l : Level} {K : Category k l} -> (D : Diagram K) ->
    -- with at least two objects
    (c₁ c₂ : Obj K) -> c₂ ≢ c₁ ->
    -- and decidable equality of objects,
    ((a b : Obj K) -> a ≡ b ⊎ a ≢ b) ->
    -- we have a limit.
    LimitOf D
  limits-from-products-and-pullbacks prod pb {K = K} D c₁ c₂ c₂≠c₁ cmp =
    record { cone = gCone ; universal = gUniversal }
   where
    open Functor D renaming (mapObj to DObj ; mapArr to DArr)
    
    P' = prod (discreteDiagram D)
    open LimitOf P' renaming ( C to P ; cone to Pcone ; universal to Puniversal )
    p : (a : Obj K) -> Mph 𝒞 P (DObj a)
    p a = LimitOf.τ P' {a}

    M = HomSet K
    Pᴹdiagram = powerDiagram P M
    Pᴹ' = prod Pᴹdiagram
    open LimitOf Pᴹ' renaming ( C to Pᴹ ; cone to Pᴹcone ; universal to Pᴹuniversal )
    q' : M -> Mph 𝒞 Pᴹ P
    q' α = LimitOf.τ Pᴹ' {α}
    q : {a c : Obj K} (α : Mph K a c) -> Mph 𝒞 Pᴹ P
    q {a} {c} α = q' (a , c , α)

    -- If two morphisms into Pᴹ behave equally under projections q and p, they are equal.
    equal-under-q-p : {X : Obj 𝒞} {f g : Mph 𝒞 X Pᴹ} ->
                      ({a c : Obj K} (α : Mph K a c) (b : Obj K) -> p b ∘ (q α ∘ f) ≡ p b ∘ (q α ∘ g)) ->
                      f ≡ g
    equal-under-q-p {_} {f} {g} pqf=pqg = equal-under-projections Pᴹ' qf=qg where
      qf=qg : (α : M) -> q' α ∘ f ≡ q' α ∘ g
      qf=qg (a , c , α) = equal-under-projections P' (pqf=pqg α)

    -- define morphism m by how it behaves under projections q and p
    pqm : {a c : Obj K} (α : Mph K a c) (b : Obj K) -> Mph 𝒞 P (DObj b)
    pqm {a} {c} α b with cmp c b
    ...                | inj₁ c=b rewrite c=b = DArr(α) ∘ (p a)
    ...                | inj₂ c≠b             = p b
    
    Dspan : {a c : Obj K} -> Mph K a c -> Cone (discreteDiagram D)
    Dspan α = coneFrom P by (natTrans (pqm α _) witnessedBy λ { refl → r-id =>>= (flipEq l-id) })

    Pᴹspan : Cone Pᴹdiagram
    Pᴹspan = coneFrom P by (
               natTrans (λ { {(a , c , α)} → UniqueConeReduction.u (Puniversal (Dspan α)) })
                 witnessedBy λ { refl → r-id =>>= flipEq l-id } )

    open UniqueConeReduction (Pᴹuniversal Pᴹspan) renaming (u to m ; ev to qm=q∘m)

    pqm=p∘q∘m : {a c : Obj K} (α : Mph K a c) (b : Obj K) -> (pqm α b) ≡ (p b ∘ q α) ∘ m
    pqm=p∘q∘m {a} {c} α b = pqmαb=pb∘qmα =>>= pb∘qmα=pb∘qα∘m where
      open UniqueConeReduction (Puniversal (Dspan α)) renaming (u to qmα ; ev to pqmα=p∘qmα)
      pqmαb=pb∘qmα : pqm α b ≡ p b ∘ qmα
      pqmαb=pb∘qmα = pqmα=p∘qmα {b}
      pb∘qmα=pb∘qα∘m : p b ∘ qmα ≡ (p b ∘ q α) ∘ m
      pb∘qmα=pb∘qα∘m = ((p b ∘_) $= qm=q∘m {a , c , α}) =>>= assocRL

    pqm=Dp : {b a : Obj K} (α : Mph K a b) -> (p b ∘ q α) ∘ m ≡ DArr α ∘ p a
    pqm=Dp {b} {a} α = flipEq (pqm=p∘q∘m α b) =>>= pqmbα=Dα∘pa where
      pqmbα=Dα∘pa : pqm α b ≡ DArr α ∘ p a
      pqmbα=Dα∘pa with cmp b b
      ...            | inj₁ refl = refl
      ...            | inj₂ b≠b  = ⊥-elim (b≠b refl)

    pqm=p : {b a c : Obj K} (α : Mph K a c) -> c ≢ b -> (p b ∘ q α) ∘ m ≡ p b
    pqm=p {b} {a} {c} α c≠b = flipEq (pqm=p∘q∘m α b) =>>= pqmbα=pb where
      pqmbα=pb : pqm α b ≡ p b
      pqmbα=pb with cmp c b
      ...         | inj₁ c=b = ⊥-elim (c≠b c=b)
      ...         | inj₂ c≠b = refl

    ΔP : Mph 𝒞 P Pᴹ
    ΔP = Δ Pᴹ'
    mono-ΔP : Mono ΔP
    mono-ΔP = Δ-is-mono {P} {_} {M} (c₁ , c₁ , id K {c₁}) Pᴹ'

    qΔ=id : {a c : Obj K} {α : Mph K a c} -> q α ∘ ΔP ≡ idC
    qΔ=id = pᵢΔ=id {L = Pᴹ'}

    open PullbackOf (pb ΔP m) renaming (P to L ; f' to Δ' ; g' to m' ; commuting to Δm'=mΔ' ; universal to Luniversal)

    mono-Δ' : Mono Δ'
    mono-Δ' = pullback_of_mono_is_mono' 𝒞 (pb ΔP m) mono-ΔP

    -- For any b, pick α : a -> c such that c ≠ b.
    acα≠ : (b : Obj K) -> ∃[ a ] ∃[ c ] ((Mph K a c) × (c ≢ b))
    acα≠ b with cmp c₁ b
    ...       | inj₁ refl = (c₂ , c₂ , id K {c₂} , c₂≠c₁)
    ...       | inj₂ c₁≠b = (c₁ , c₁ , id K {c₁} , c₁≠b )
       
    pm'=pΔ' : (b : Obj K) → (p b ∘ m') ≡ (p b ∘ Δ')
    pm'=pΔ' b with acα≠ b
    ...          | (a , c , α , c≠b) = flipEq pbΔ'=pbm'
      where
        pb=pbqαm : p b ≡ (p b ∘ q α) ∘ m
        pb=pbqαm = flipEq (pqm=p α c≠b)
        pbΔ'=pbqαmΔ' = ((_∘ Δ') $= pb=pbqαm) =>>= assocLR
        pbΔ'=pbqαΔm' = pbΔ'=pbqαmΔ' =>>= (((p b ∘ q α) ∘_) $= (flipEq Δm'=mΔ')) =>>= assocLR
        qαΔm'=m' = assocRL =>>= ((_∘ m') $= qΔ=id) =>>= l-id
        pbΔ'=pbm' = pbΔ'=pbqαΔm' =>>= (((p b) ∘_) $= qαΔm'=m')
    
    m'=Δ' : m' ≡ Δ'
    m'=Δ' = equal-under-projections P' pm'=pΔ'

    g : (a : Obj K) -> Mph 𝒞 L (DObj a)
    g a = p a ∘ Δ'

    Dg=g : {a b : Obj K} (α : Mph K a b) -> (DArr α) ∘ g a ≡ g b
    Dg=g {a} {b} α = Dαga=DαpaΔ' =>>= DαpaΔ'=pbqαmΔ' =>>= pbqαmΔ'=pbqαΔm' =>>= pbqαΔm'=pbm' =>>= pbm'=gb
      where
        Dαga=DαpaΔ'     : (DArr α) ∘ g a ≡ (DArr α ∘ p a) ∘ Δ'
        Dαga=DαpaΔ'     = assocRL
        DαpaΔ'=pbqαmΔ'  : (DArr α ∘ p a) ∘ Δ' ≡ (p b ∘ q α) ∘ (m ∘ Δ')
        DαpaΔ'=pbqαmΔ'  = (_∘ Δ') $= flipEq (pqm=Dp α) =>>= assocLR
        pbqαmΔ'=pbqαΔm' : (p b ∘ q α) ∘ (m ∘ Δ') ≡ p b ∘ (q α ∘ (ΔP ∘ m'))
        pbqαmΔ'=pbqαΔm' = ((p b ∘ q α) ∘_) $= flipEq Δm'=mΔ' =>>= assocLR
        pbqαΔm'=pbm'    : p b ∘ (q α ∘ (ΔP ∘ m')) ≡ p b ∘ m'
        pbqαΔm'=pbm'    = ((p b ∘_) $= (assocRL =>>= ((_∘ m') $= qΔ=id) =>>= l-id))
        pbm'=gb         : p b ∘ m' ≡ g b
        pbm'=gb         = pm'=pΔ' b
    
    gCone : Cone D
    gCone = coneFrom L by (natTrans (g _) witnessedBy λ α → r-id =>>= flipEq (Dg=g α))

    gUniversal : (fCone : Cone D) -> UniqueConeReduction fCone gCone
    gUniversal fCone @ (coneFrom C by (natTrans f witnessedBy f=Df)) = (reduceConeBy h witnessedBy f=gh) uniquely h-uniqueness where
      open UniqueConeReduction (Puniversal (discreteCone fCone)) renaming (u to f' ; unique to f'unique ; ev to f=pf')

      Δf'=mf' : ΔP ∘ f' ≡ m ∘ f'
      Δf'=mf' = equal-under-q-p pqΔf'=pqmf' where
        pqΔf'=f : {a c : Obj K} (α : Mph K a c) (b : Obj K) -> (p b ∘ q α) ∘ (ΔP ∘ f') ≡ f {b}
        pqΔf'=f α b = assocLR =>>= ((p b ∘_) $= (assocRL =>>= ((_∘ f') $= qΔ=id =>>= l-id)) =>>= (flipEq f=pf'))
        
        pqmf'=f : {a c : Obj K} (α : Mph K a c) (b : Obj K) -> (p b ∘ q α) ∘ (m ∘ f') ≡ f {b}
        pqmf'=f {a} {c} α b with cmp c b
        ...                    | inj₁ refl = pbqαmf'=Dαpaf' =>>= Dαpaf'=Dαfa =>>= Dαfa=fb where
                                   pbqαmf'=Dαpaf' = assocRL =>>= ((_∘ f') $= (pqm=Dp α))
                                   Dαpaf'=Dαfa = assocLR =>>= ((DArr α ∘_) $= flipEq f=pf')
                                   Dαfa=fb = flipEq (f=Df α) =>>= r-id
        ...                    | inj₂ c≠b  = assocRL =>>= ((_∘ f') $= (pqm=p α c≠b)) =>>= flipEq f=pf'

        pqΔf'=pqmf' : {a c : Obj K} (α : Mph K a c) (b : Obj K) -> p b ∘ (q α ∘ (ΔP ∘ f')) ≡ p b ∘ (q α ∘ (m ∘ f'))
        pqΔf'=pqmf' {a} {c} α b = assocRL =>>= (pqΔf'=f α b) =>>= flipEq (pqmf'=f α b) =>>= assocLR

      f'Cone : CommutingSquare 𝒞 f' ΔP f' m
      f'Cone = commutingSquare Δf'=mf'

      open UniqueSpanReduction (Luniversal f'Cone) renaming (u to h ; ev₂ to Δ'h=f')

      f=pΔ'h : {a : Obj K} -> f {a} ≡ p a ∘ (Δ' ∘ h)
      f=pΔ'h {a} = f=pf' =>>= flipEq ((p a ∘_) $= Δ'h=f')

      f=gh : {a : Obj K} -> f {a} ≡ g a ∘ h
      f=gh {a} = f=pΔ'h {a} =>>= assocRL

      h-uniqueness : (h'red : ConeReduction fCone gCone) -> ConeReduction.u h'red ≡ h
      h-uniqueness (reduceConeBy h' witnessedBy f=gh') = h'=h where
        Δ'h'red : ConeReduction (discreteCone fCone) Pcone
        Δ'h'red = reduceConeBy (Δ' ∘ h') witnessedBy (f=gh' =>>= assocLR)

        Δ'h'=f' : Δ' ∘ h' ≡ f'
        Δ'h'=f' = f'unique Δ'h'red

        Δ'h'=Δ'h = Δ'h'=f' =>>= flipEq Δ'h=f'
        h'=h = Mono.elimL mono-Δ' Δ'h'=Δ'h

  -- Maranda theorem
  limits-from-products-and-equalizers :
    -- Given arbitrary products
    ({l : Level} {X : Set l} (D : Diagram (discrete X)) -> LimitOf D) ->
    -- and binary equalizers,
    ({A B : Obj 𝒞} (f g : Mph 𝒞 A B) -> EqualizerOf 𝒞 f g) ->
    -- for any diagram
    {k l : Level} {K : Category k l} -> (D : Diagram K) ->
    -- with at least two objects
    (c₁ c₂ : Obj K) -> c₂ ≢ c₁ ->
    -- and decidable equality of objects,
    ((a b : Obj K) -> a ≡ b ⊎ a ≢ b) ->
    -- we have a limit.
    LimitOf D
  limits-from-products-and-equalizers prod equ {K = K} D c₁ c₂ c₂≠c₁ cmp =
    limits-from-products-and-pullbacks prod pb D c₁ c₂ c₂≠c₁ cmp
   where
     pb : {A B C : Obj 𝒞} (f : Mph 𝒞 A C) (g : Mph 𝒞 B C) -> PullbackOf 𝒞 f g
     pb f g = pullbacks_from_products_and_equalizers 𝒞 binProd equ f g where
       binProd : (A B : Obj 𝒞) -> Product 𝒞 A B
       binProd A B = binaryProductFromLimit (prod (binaryProductDiagram A B))
