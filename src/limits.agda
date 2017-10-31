open import Data.Empty
open import Data.Product
open import Data.Sum
open import Prelude
open import category
open import functor
open import nat-trans
open import pullbacks

module limits {k l : Level} (𝒞 : Category {k} {l}) where
  open Category using (Obj ; Hom ; HomSet ; id)
  open Category 𝒞 using (_∘_) renaming (id to idC ; left_id to left_idC ; right_id to right_idC ; assoc to assocC)

  record Diagram {nj mj : Level} (J : Category {nj} {mj}) : Set (k ⊔ l ⊔ nj ⊔ mj) where
    constructor diagram
    field
      functor : Functor J 𝒞

    identity = Functor.identity functor
      
  record Cone {nj mj : Level} {J : Category {nj} {mj}} (D : Diagram J) : Set (k ⊔ l ⊔ nj ⊔ mj) where
    open Diagram D renaming (functor to F)
    field
      C : Obj 𝒞
      trans : NatTrans (ConstFunctor C) F
    τ = NatTrans.τ trans
    naturality = NatTrans.naturality trans

  record ConeReduction {nj mj : Level} {J : Category {nj} {mj}} {D : Diagram J} (c₁ : Cone D) (c₂ : Cone D) : Set (l ⊔ nj) where
    open Cone c₁ renaming (C to C₁ ; τ to τ₁)
    open Cone c₂ renaming (C to C₂ ; τ to τ₂)
    field
      u : Hom 𝒞 C₁ C₂
      ev : {A : Obj J} -> τ₁ {A} ≡ τ₂ ∘ u
      
  record UniqueConeReduction {nj mj : Level} {J : Category {nj} {mj}} {D : Diagram J} (C₁ : Cone D) (C₂ : Cone D) : Set (l ⊔ nj) where
    field
      reduction : ConeReduction C₁ C₂
      unique : (r : ConeReduction C₁ C₂) -> ConeReduction.u r ≡ ConeReduction.u reduction
    u = ConeReduction.u reduction
    ev = ConeReduction.ev reduction
      
  record Limit {nj mj : Level} {J : Category {nj} {mj}} {D : Diagram J} (C : Cone D) : Set (k ⊔ l ⊔ mj ⊔ nj) where
    field
      universal : (C₂ : Cone D) -> UniqueConeReduction C₂ C

  record LimitOf {nj mj : Level} {J : Category {nj} {mj}} (D : Diagram J) : Set (k ⊔ l ⊔ mj ⊔ nj) where
    field
      cone : Cone D
      universal : (c : Cone D) -> UniqueConeReduction c cone
    C = Cone.C cone
    τ = Cone.τ cone

  -- Discrete category on a set of objects.
  discrete : {n : Level} -> Set n -> Category {n} {n}
  discrete {n} Obj = record
                       { Obj = Obj
                       ; Hom = λ A B → A ≡ B
                       ; id = refl
                       ; _∘_ = λ g f → f =>>= g
                       ; left_id = eqUnicity
                       ; right_id = eqUnicity
                       ; assoc = eqUnicity
                       }

  discretize : {k l : Level} -> Category {k} {l} -> Category {k} {k}
  discretize C = discrete (Obj C)

  discreteDiagram : {nj mj : Level} {J : Category {nj} {mj}} -> Diagram J -> Diagram (discretize J)
  discreteDiagram D = diagram (record
                                 { mapObj = DObj
                                 ; mapArr = λ { {A} {.A} refl → idC {DObj A} }
                                 ; identity = refl
                                 ; composition = λ {A B C} -> λ { {g = refl} {refl} → flipEq left_idC }
                                 })
                               where
                                 open Diagram D renaming (functor to DF)
                                 open Functor DF renaming (mapObj to DObj ; mapArr to DArr ; identity to Did ; composition to Dcomp)

  discreteCone : {nj mj : Level} {J : Category {nj} {mj}} {D : Diagram J} -> Cone D -> Cone (discreteDiagram D)
  discreteCone {J = J} c = record
    { C = Cone.C c
    ; trans = record
        { τ = λ {A} → Cone.τ c {A}
        ; naturality = λ { refl -> right_idC =>>= flipEq (left_idC)}
        }
    }
                                 
  powerDiagram : {n : Level} (A : Obj 𝒞) (X : Set n) -> Diagram (discrete X)
  powerDiagram A X = diagram (ConstFunctor {𝒞₁ = discrete X} A)

  Δ-cone : {A : Obj 𝒞} {n : Level} {X : Set n} -> Cone (powerDiagram A X)
  Δ-cone {A} {n} {X} = record { C = A ; trans = record { τ = idC ; naturality = λ f -> left_idC =>>= flipEq right_idC } }
  
  Δ : {A : Obj 𝒞} {n : Level} {X : Set n} -> (L : LimitOf (powerDiagram A X)) -> Hom 𝒞 A (LimitOf.C L)
  Δ {A} {n} {X} L = UniqueConeReduction.u (LimitOf.universal L Δ-cone)

  pᵢΔ=id : {A : Obj 𝒞} {n : Level} {I : Set n} {i : I} {L : LimitOf (powerDiagram A I)} -> (LimitOf.τ L {i}) ∘ (Δ L) ≡ idC
  pᵢΔ=id {A} {n} {I} {i} {L} = flipEq (UniqueConeReduction.ev (LimitOf.universal L Δ-cone) {i})

  open import morphisms 𝒞
  
  Δ-is-mono : {A : Obj 𝒞} {n : Level} {X : Set n} (x : X) -> (L : LimitOf (powerDiagram A X)) -> Mono (Δ L)
  Δ-is-mono {A} {n} {X} x L = mono λ {Z g h} Δg=Δh → 
    let
      open LimitOf L renaming (C to P ; τ to p)
      pₓ : Hom 𝒞 P A
      pₓ = p {x}
      pₓΔ=id : (pₓ ∘ (Δ L)) ≡ idC
      pₓΔ=id = pᵢΔ=id {L = L}
      pₓΔg=pₓΔh = assocC =>>= ((pₓ ∘_) $= Δg=Δh) =>>= flipEq assocC
      id∘g=id∘h = ((_∘ g) $= (flipEq pₓΔ=id)) =>>= pₓΔg=pₓΔh =>>= ((_∘ h) $= pₓΔ=id)
    in (flipEq left_idC) =>>= id∘g=id∘h =>>= left_idC

  equal-under-projections : {A : Obj 𝒞} {n : Level} {X : Set n} {D : Diagram (discrete X)} (L : LimitOf D) {f g : Hom 𝒞 A (LimitOf.C L)} ->
                            ((x : X) -> (LimitOf.τ L {x}) ∘ f ≡ (LimitOf.τ L {x}) ∘ g) -> f ≡ g
  equal-under-projections {A} {_} {X} {D} L {f} {g} pf=pg =
    let
      open LimitOf L renaming (cone to Lcone ; τ to p)
      open Diagram D renaming (identity to Did)
      fCone : Cone D
      fCone = record { C = A ; trans = record
                                 { τ = p ∘ f
                                 ; naturality = λ { refl → right_idC =>>= (flipEq left_idC) =>>= ((_∘ (p ∘ f)) $= flipEq Did)} }
                                 }
      fRed : ConeReduction fCone Lcone
      fRed = record { u = f ; ev = refl }
      gRed : ConeReduction fCone Lcone
      gRed = record { u = g ; ev = pf=pg _ }
      open UniqueConeReduction (universal fCone)
      f=u = unique fRed
      g=u = unique gRed
    in f=u =>>= flipEq g=u
  
  -- Freyd theorem
  limits-from-products-and-pullbacks :
    -- Given arbitrary products
    ({l : Level} {X : Set l} (D : Diagram (discrete X)) -> LimitOf D) ->
    -- and binary pullbacks,
    ({A B C : Obj 𝒞} (f : Hom 𝒞 A C) (g : Hom 𝒞 B C) -> PullbackOf 𝒞 f g) ->
    -- for any diagram
    {nj mj : Level} {J : Category {nj} {mj}} -> (D : Diagram J) ->
    -- with at least two objects
    (c₁ c₂ : Obj J) -> c₂ ≢ c₁ ->
    -- and decidable equality of objects,
    ((A B : Obj J) -> A ≡ B ⊎ A ≢ B) ->
    -- we have a limit.
    LimitOf D
  limits-from-products-and-pullbacks prod pb {J = J} D c₁ c₂ c₂≠c₁ cmp =
    record { cone = gCone ; universal = gUniversal }
   where
    open Diagram D renaming (functor to DF)
    open Functor DF renaming (mapObj to DObj ; mapArr to DArr)
    
    P' = prod (discreteDiagram D)
    open LimitOf P' renaming ( C to P
                             ; cone to Pcone
                             ; universal to Puniversal )
    p : (A : Obj J) -> Hom 𝒞 P (DObj A)
    p a = LimitOf.τ P' {a}

    M = HomSet J
    Pᴹdiagram = powerDiagram P M
    Pᴹ' = prod Pᴹdiagram
    open LimitOf Pᴹ' renaming ( C to Pᴹ
                              ; cone to Pᴹcone
                              ; universal to Pᴹuniversal )
    q' : HomSet J -> Hom 𝒞 Pᴹ P
    q' α = LimitOf.τ Pᴹ' {α}
    q : {a c : Obj J} (α : Hom J a c) -> Hom 𝒞 Pᴹ P
    q {a} {c} α = q' (a , c , α)

    -- If two morphisms into Pᴹ behave equally under projections q and p, they are equal.
    equal-under-q-p : {X : Obj 𝒞} {f g : Hom 𝒞 X Pᴹ} ->
                      ({a c : Obj J} (α : Hom J a c) (b : Obj J) -> p b ∘ (q α ∘ f) ≡ p b ∘ (q α ∘ g)) ->
                      f ≡ g
    equal-under-q-p {_} {f} {g} pqf=pqg = equal-under-projections Pᴹ' qf=qg where
      qf=qg : (α : HomSet J) -> q' α ∘ f ≡ q' α ∘ g
      qf=qg (a , c , α) = equal-under-projections P' (pqf=pqg α)

    -- define morphism m by how it behaves under projections q and p
    pqm : {a c : Obj J} (α : Hom J a c) (b : Obj J) -> Hom 𝒞 P (DObj b)
    pqm {a} {c} α b with cmp c b
    ...                | inj₁ c=b rewrite c=b = DArr(α) ∘ (p a)
    ...                | inj₂ c≠b             = p b
    
    Dspan : {a c : Obj J} -> Hom J a c -> Cone (discreteDiagram D)
    Dspan α = record
      { C = P
      ; trans = record
          { τ = pqm α _
          ; naturality = λ { refl → right_idC =>>= (flipEq left_idC)}
          }
      }

    Pᴹspan : Cone Pᴹdiagram
    Pᴹspan = record
      { C = P
      ; trans = record
          { τ = λ { {(a , c , α)} → UniqueConeReduction.u (Puniversal (Dspan α)) }
          ; naturality = λ { refl → right_idC =>>= flipEq left_idC }
          }
      }

    open UniqueConeReduction (Pᴹuniversal Pᴹspan) renaming (u to m ; ev to qm=q∘m)

    pqm=p∘q∘m : {a c : Obj J} (α : Hom J a c) (b : Obj J) -> (pqm α b) ≡ (p b ∘ q α) ∘ m
    pqm=p∘q∘m {a} {c} α b = pqmαb=pb∘qmα =>>= pb∘qmα=pb∘qα∘m
      where
        open UniqueConeReduction (Puniversal (Dspan α)) renaming (u to qmα ; ev to pqmα=p∘qmα)
        pqmαb=pb∘qmα : pqm α b ≡ p b ∘ qmα
        pqmαb=pb∘qmα = pqmα=p∘qmα {b}
        pb∘qmα=pb∘qα∘m : p b ∘ qmα ≡ (p b ∘ q α) ∘ m
        pb∘qmα=pb∘qα∘m = ((p b ∘_) $= qm=q∘m {a , c , α}) =>>= (flipEq assocC)

    pqm=Dp : {b a : Obj J} (α : Hom J a b) -> (p b ∘ q α) ∘ m ≡ DArr α ∘ p a
    pqm=Dp {b} {a} α = flipEq (pqm=p∘q∘m α b) =>>= pqmbα=Dα∘pa
      where
        pqmbα=Dα∘pa : pqm α b ≡ DArr α ∘ p a
        pqmbα=Dα∘pa with cmp b b
        ...            | inj₁ refl = refl
        ...            | inj₂ b≠b  = ⊥-elim (b≠b refl)

    pqm=p : {b a c : Obj J} (α : Hom J a c) -> c ≢ b -> (p b ∘ q α) ∘ m ≡ p b
    pqm=p {b} {a} {c} α c≠b = flipEq (pqm=p∘q∘m α b) =>>= pqmbα=pb
      where
        pqmbα=pb : pqm α b ≡ p b
        pqmbα=pb with cmp c b
        ...         | inj₁ c=b = ⊥-elim (c≠b c=b)
        ...         | inj₂ c≠b = refl

    ΔP : Hom 𝒞 P Pᴹ
    ΔP = Δ Pᴹ'
    mono-ΔP : Mono ΔP
    mono-ΔP = Δ-is-mono {P} {_} {M} (c₁ , c₁ , id J {c₁}) Pᴹ'

    qΔ=id : {a c : Obj J} {α : Hom J a c} -> q α ∘ ΔP ≡ idC
    qΔ=id = pᵢΔ=id {L = Pᴹ'}
    
    open PullbackOf (pb ΔP m) renaming (P to L ; f' to Δ' ; g' to m' ; comm to Δm'=mΔ' ; universal to Luniversal)

    mono-Δ' : Mono Δ'
    mono-Δ' = pullback_of_mono_is_mono 𝒞 (pb ΔP m) mono-ΔP

    -- For any b, pick α : a -> c such that c ≠ b.
    acα≠ : (b : Obj J) -> Σ ((Obj J) × (Obj J)) λ {(a , c) -> (Hom J a c) × (c ≢ b)} 
    acα≠ b with cmp c₁ b
    ...       | inj₁ refl = (c₂ , c₂) , (id J {c₂} , c₂≠c₁)
    ...       | inj₂ c₁≠b = (c₁ , c₁) , (id J {c₁} , c₁≠b)
       
    pm'=pΔ' : (b : Obj J) → (p b ∘ m') ≡ (p b ∘ Δ')
    pm'=pΔ' b with acα≠ b
    ...          | ((a , c) , α , c≠b) =
      let
        pb=pbqαm : p b ≡ (p b ∘ q α) ∘ m
        pb=pbqαm = flipEq (pqm=p α c≠b)
        pbΔ'=pbqαmΔ' = ((_∘ Δ') $= pb=pbqαm) =>>= assocC
        pbΔ'=pbqαΔm' = pbΔ'=pbqαmΔ' =>>= (((p b ∘ q α) ∘_) $= (flipEq Δm'=mΔ')) =>>= assocC
        qαΔm'=m' = flipEq assocC =>>= ((_∘ m') $= qΔ=id) =>>= left_idC
        pbΔ'=pbm' = pbΔ'=pbqαΔm' =>>= (((p b) ∘_) $= qαΔm'=m')
      in flipEq pbΔ'=pbm'
    
    m'=Δ' : m' ≡ Δ'
    m'=Δ' = equal-under-projections P' pm'=pΔ'

    g : (a : Obj J) -> Hom 𝒞 L (DObj a)
    g a = p a ∘ Δ'

    Dg=g : {a b : Obj J} (α : Hom J a b) -> (DArr α) ∘ g a ≡ g b
    Dg=g {a} {b} α = Dαga=DαpaΔ' =>>= DαpaΔ'=pbqαmΔ' =>>= pbqαmΔ'=pbqαΔm' =>>= pbqαΔm'=pbm' =>>= pbm'=gb
      where
        Dαga=DαpaΔ'     : (DArr α) ∘ g a ≡ (DArr α ∘ p a) ∘ Δ'
        Dαga=DαpaΔ'     = flipEq assocC
        DαpaΔ'=pbqαmΔ'  : (DArr α ∘ p a) ∘ Δ' ≡ (p b ∘ q α) ∘ (m ∘ Δ')
        DαpaΔ'=pbqαmΔ'  = (_∘ Δ') $= flipEq (pqm=Dp α) =>>= assocC
        pbqαmΔ'=pbqαΔm' : (p b ∘ q α) ∘ (m ∘ Δ') ≡ p b ∘ (q α ∘ (ΔP ∘ m'))
        pbqαmΔ'=pbqαΔm' = ((p b ∘ q α) ∘_) $= flipEq Δm'=mΔ' =>>= assocC
        pbqαΔm'=pbm'    : p b ∘ (q α ∘ (ΔP ∘ m')) ≡ p b ∘ m'
        pbqαΔm'=pbm'    = ((p b ∘_) $= (flipEq assocC =>>= ((_∘ m') $= qΔ=id) =>>= left_idC))
        pbm'=gb         : p b ∘ m' ≡ g b
        pbm'=gb         = pm'=pΔ' b
    
    gCone : Cone D
    gCone = record
      { C = L
      ; trans = record
          { τ = λ {a} → g a
          ; naturality = λ α → right_idC =>>= flipEq (Dg=g α)
          }
      }

    gUniversal : (fCone : Cone D) -> UniqueConeReduction fCone gCone
    gUniversal fCone = record { reduction = f-to-g ; unique = f-to-g-uniqueness }
      where
        open Cone fCone renaming (C to X ; τ to f ; naturality to f=Df)
        open UniqueConeReduction (Puniversal (discreteCone fCone)) renaming (u to f' ; unique to f'unique ; ev to f=pf')

        Δf'=mf' : ΔP ∘ f' ≡ m ∘ f'
        Δf'=mf' = equal-under-q-p pqΔf'=pqmf'
          where
            pqΔf'=f : {a c : Obj J} (α : Hom J a c) (b : Obj J) -> (p b ∘ q α) ∘ (ΔP ∘ f') ≡ f {b}
            pqΔf'=f α b = assocC =>>= ((p b ∘_) $= (flipEq assocC =>>= ((_∘ f') $= qΔ=id =>>= left_idC)) =>>= (flipEq f=pf'))
            
            pqmf'=f : {a c : Obj J} (α : Hom J a c) (b : Obj J) -> (p b ∘ q α) ∘ (m ∘ f') ≡ f {b}
            pqmf'=f {a} {c} α b with cmp c b
            ...                    | inj₁ refl = flipEq assocC =>>= ((_∘ f') $= (pqm=Dp α)) =>>= assocC =>>= ((DArr α ∘_) $= flipEq f=pf') =>>= (flipEq (f=Df α) =>>= right_idC)
            ...                    | inj₂ c≠b  = flipEq assocC =>>= ((_∘ f') $= (pqm=p α c≠b)) =>>= flipEq f=pf'
            
            pqΔf'=pqmf' : {a c : Obj J} (α : Hom J a c) (b : Obj J) -> p b ∘ (q α ∘ (ΔP ∘ f')) ≡ p b ∘ (q α ∘ (m ∘ f'))
            pqΔf'=pqmf' {a} {c} α b = flipEq assocC =>>= (pqΔf'=f α b) =>>= flipEq (pqmf'=f α b) =>>= assocC

        f'Cone : PullingBack 𝒞 ΔP m
        f'Cone = record { P = X ; f' = f' ; g' = f' ; comm = Δf'=mf' }

        open UniquePullingBackReduction (Luniversal f'Cone) renaming (u to h ; ev₂ to Δ'h=f')

        f=pΔ'h : {a : Obj J} -> f {a} ≡ p a ∘ (Δ' ∘ h)
        f=pΔ'h {a} = f=pf' =>>= ((p a ∘_) $= flipEq Δ'h=f')

        f=gh : {a : Obj J} -> f {a} ≡ g a ∘ h
        f=gh {a} = f=pΔ'h {a} =>>= (flipEq assocC)
        
        f-to-g : ConeReduction fCone gCone
        f-to-g = record { u = h ; ev = f=gh }

        f-to-g-uniqueness : (h'red : ConeReduction fCone gCone) -> ConeReduction.u h'red ≡ h
        f-to-g-uniqueness h'red = h'=h
          where
            open ConeReduction h'red renaming (u to h' ; ev to f=gh')
            Δ'h'red : ConeReduction (discreteCone fCone) Pcone
            Δ'h'red = record { u =  Δ' ∘ h' ; ev = λ {a} -> f=gh' {a} =>>= assocC }
            
            Δ'h'=f' : Δ' ∘ h' ≡ f'
            Δ'h'=f' = f'unique Δ'h'red

            Δ'h'=Δ'h = Δ'h'=f' =>>= flipEq Δ'h=f'
            h'=h = Mono.elimL mono-Δ' Δ'h'=Δ'h
