module CoherentSpace where

open import Data.Sum using (_⊎_)

open import Function hiding (_⇔_)
open import Relation.Binary hiding (_⇒_ ; _⇔_) 
open import Relation.Binary.Lattice
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Bool
open import Relation.Nullary using (¬_)
open import Relation.Unary
open import Level

open import Categories.Category

_⇔_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₃} → (Pred A ℓ₁) → (Pred A ℓ₂) → Set _
P ⇔ Q = (P ⊆ Q) × (Q ⊆ P)   

record CoherentSpace c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    -- The token set
    TokenSet : Set c
    -- The setoid equivalence
    _≈_      : Rel TokenSet c
    -- The consistency relation
    _∼_      : Rel TokenSet ℓ
    
    ∼-respˡ-≈ : _∼_ Respectsˡ _≈_
    ≈→∼ : ∀ {a b} → (a ≈ b) → (a ∼ b)
    ∼-sym  : Symmetric _∼_

    ≈-isEquivalence : (IsEquivalence _≈_)

  -- The inconsistency relation
  _≁_ : Rel TokenSet _
  a ≁ b = (a ≈ b) ⊎ ¬ (a ∼ b)

  ≁-sym : Symmetric _≁_
  --[[[
  ≁-sym {a} {b} (inj₁ a≈b) = inj₁ (sym a≈b)
    where
      open IsEquivalence ≈-isEquivalence
  ≁-sym {a} {b} (inj₂ ¬a∼b) = inj₂ (¬b∼a)
    where
      ¬b∼a : ¬ (b ∼ a)
      ¬b∼a b∼a = ¬a∼b (∼-sym b∼a)
  --]]]

  setoid : Setoid c _
  setoid = record
    { Carrier = TokenSet
    ; _≈_ = _≈_
    ; isEquivalence = ≈-isEquivalence
    }

  isPoint : ∀ {ℓ} → Pred TokenSet ℓ → Set _
  isPoint {ℓ} P = (p₁ p₂ : TokenSet) → p₁ ∈ P → p₂ ∈ P → p₁ ∼ p₂

  Point : Set _
  Point = Σ[ p ∈ Pred TokenSet c ] (isPoint p) × (p Respects _≈_) 

  downwardClosed : ∀ {ℓ₃ ℓ₄} → (P : Pred TokenSet ℓ₃) → isPoint P → (Q : Pred TokenSet ℓ₄) → Q ⊆ P → isPoint Q 
  downwardClosed P isPointP Q Q⊆P p₁ p₂ p₁∈Q p₂∈Q = isPointP p₁ p₂ p₁∈P p₂∈P
    where
      p₁∈P : p₁ ∈ P
      p₁∈P = Q⊆P p₁∈Q

      p₂∈P : p₂ ∈ P
      p₂∈P = Q⊆P p₂∈Q

  coherent : ∀ {ℓ₃ ℓ₄} → (IndexSet : Set ℓ₃) → (P : IndexSet → Pred TokenSet ℓ₄) → 
             (∀ {i j} → (isPoint $ (P i) ∪ (P j))) → (isPoint $ ⋃ IndexSet P)
  coherent {ℓ₃} {ℓ₄} IndexSet P ∪-closed p₁ p₂ (i , p₁∈Pᵢ) (j , p₂∈Pⱼ) = ∪-closed p₁ p₂ p₁∈Pᵢ∪Pⱼ p₂∈Pᵢ∪Pⱼ
      where
        p₁∈Pᵢ∪Pⱼ : p₁ ∈ (P i) ∪ (P j)
        p₁∈Pᵢ∪Pⱼ = Data.Sum.inj₁ p₁∈Pᵢ

        p₂∈Pᵢ∪Pⱼ : p₂ ∈ (P i) ∪ (P j)
        p₂∈Pᵢ∪Pⱼ = Data.Sum.inj₂ p₂∈Pⱼ 

CoherentSpaceBool : CoherentSpace _ _
CoherentSpace.TokenSet CoherentSpaceBool = Bool
CoherentSpace._≈_ CoherentSpaceBool = _≡_
CoherentSpace._∼_ CoherentSpaceBool = _≡_
CoherentSpace.∼-respˡ-≈ CoherentSpaceBool {a} {b} {c} b≡c b≡a = PE.trans (PE.sym b≡c) b≡a
CoherentSpace.≈→∼ CoherentSpaceBool a≡b = a≡b
CoherentSpace.∼-sym CoherentSpaceBool = PE.sym
CoherentSpace.≈-isEquivalence CoherentSpaceBool = PE.isEquivalence

_⇒ₗ_ : ∀ {c ℓ c' ℓ'} → (P : CoherentSpace c ℓ) → (Q : CoherentSpace c' ℓ') → 
       (CoherentSpace _ _)

_⇒ₗ_ {c} {ℓ} {c'} {ℓ'} P Q = space
  where
    open CoherentSpace P renaming 
      (TokenSet to |P| ; _∼_ to _∼p_ ; _≁_ to _≁p_ ; _≈_ to _≈p_ ; ∼-refl to ∼p-refl ; ∼-sym to ∼p-sym ;
       ∼-respˡ-≈ to ∼p-respˡ-≈p)
    open CoherentSpace Q renaming 
      (TokenSet to |Q| ; _∼_ to _∼q_ ; _≁_ to _≁q_ ; _≈_ to _≈q_ ; ∼-refl to ∼q-refl ; ∼-sym to ∼q-sym  ;
       ∼-respˡ-≈ to ∼q-respˡ-≈q)

    open IsEquivalence (CoherentSpace.≈-isEquivalence P) renaming (sym to ≈p-sym ; trans to ≈p-trans)
    open IsEquivalence (CoherentSpace.≈-isEquivalence Q) renaming (sym to ≈q-sym ; trans to ≈q-trans)

    open import Data.Product.Relation.Binary.Pointwise.NonDependent

    _∼p×q_ : Rel (|P| × |Q|) _ -- (ℓ₁ ⊔ ℓ₁' ⊔ ℓ₂ ⊔ ℓ₂' ⊔ c ⊔ c')
    (p , q) ∼p×q (p' , q') = ((p ∼p p') → (q ∼q q')) × ((q ≁q q') → (p ≁p p'))

    space : CoherentSpace _ _
    space = record 
      { TokenSet = |P| × |Q| 
      ; _≈_ = _≈p×q_
      ; _∼_ = _∼p×q_
      ; ≈-isEquivalence = isEquivalence-≈p×q
      ; ∼-sym = ∼-sym
      ; ∼-respˡ-≈ = ∼p×q-respˡ-≈p×q
      ; ≈→∼ = ≈p×q→∼p×q
      }
      where
        _≈p×q_ : Rel (|P| × |Q|) _ -- (c ⊔ ℓ₁ ⊔ c' ⊔ ℓ₁')
        _≈p×q_ = Pointwise _≈p_ _≈q_ 
        
        isEquivalence-≈p×q : IsEquivalence (Pointwise _≈p_ _≈q_ )
        isEquivalence-≈p×q = ×-isEquivalence (CoherentSpace.≈-isEquivalence P) (CoherentSpace.≈-isEquivalence Q)

        ∼p×q-respˡ-≈p×q : _∼p×q_ Respectsˡ _≈p×q_   
        ∼p×q-respˡ-≈p×q {p , q} {r , s} {r' , s'} (r≈r' , s≈s') (r∼p→s∼q , s≁q→r≁p) = r'∼p→s'∼q , s'≁q→r'≁p 
          where
            r'∼p→s'∼q : (r' ∼p p) → (s' ∼q q) 
            r'∼p→s'∼q r'∼p = ∼q-respˡ-≈q s≈s' s∼q
              where
                r∼p : r ∼p p
                r∼p = ∼p-respˡ-≈p (≈p-sym r≈r') r'∼p

                s∼q : s ∼q q
                s∼q = r∼p→s∼q r∼p

            s'≁q→r'≁p : s' ≁q q → r' ≁p p
            s'≁q→r'≁p (inj₁ s'≈q) with r≁p 
              where
                s≁q : s ≁q q
                s≁q = inj₁ (≈q-trans s≈s' s'≈q)

                r≁p : r ≁p p
                r≁p = s≁q→r≁p s≁q
            s'≁q→r'≁p (inj₁ s'≈q) | inj₁ r≈p = inj₁ (≈p-trans (≈p-sym r≈r') r≈p)
            s'≁q→r'≁p (inj₁ s'≈q) | (inj₂ ¬r∼p) = inj₂ ¬r'∼p
              where
                ¬r'∼p : ¬ (r' ∼p p)
                ¬r'∼p r'∼p = ¬r∼p (∼p-respˡ-≈p (≈p-sym r≈r') r'∼p)
            s'≁q→r'≁p (inj₂ ¬s'∼q) = inj₂ ¬r'∼p
              where
                ¬r'∼p : ¬ (r' ∼p p)
                ¬r'∼p r'∼p = ⊥-elim (¬s'∼q s'∼q) 
                  where
                    r∼p : r ∼p p
                    r∼p = ∼p-respˡ-≈p (≈p-sym r≈r') r'∼p

                    s∼q : s ∼q q
                    s∼q = r∼p→s∼q r∼p

                    s'∼q : s' ∼q q
                    s'∼q = ∼q-respˡ-≈q s≈s' s∼q 

        ≈p×q→∼p×q : ∀ {pq : |P| × |Q|} {p'q' : |P| × |Q|} → pq ≈p×q p'q' → pq ∼p×q p'q'
        --[[[
        ≈p×q→∼p×q {(p , q)} {(p' , q')} (p≈p' , q≈q') = p∼p'→q∼q' , p≁p'→q≁q'
          where
            open IsEquivalence (CoherentSpace.≈-isEquivalence P) renaming (refl to ≈p-refl) 
            open IsEquivalence (CoherentSpace.≈-isEquivalence Q) renaming (refl to ≈q-refl)

            p∼p' : p ∼p p'
            p∼p' = (CoherentSpace.≈→∼ P) p≈p'

            q∼q' : q ∼q q'
            q∼q' = (CoherentSpace.≈→∼ Q) q≈q'

            p∼p'→q∼q' : (p ∼p p') → (q ∼q q')
            p∼p'→q∼q' p∼p' = q∼q'

            p≁p'→q≁q' : (q ≁q q') → (p ≁p p')
            p≁p'→q≁q' q≁q' = inj₁ p≈p'
        --]]]
        
        ∼-sym : Symmetric _∼p×q_
        ∼-sym {p , q} {p' , q'} (p∼p'→q∼q' , q≁q'→p≁p') = p'∼p→q'∼q , q'≁q→p'≁p
          where
            p'∼p→q'∼q : (p' ∼p p) → (q' ∼q q)
            p'∼p→q'∼q p'∼p = ∼q-sym q∼q'
              where
                q∼q' : q ∼q q'
                q∼q' = p∼p'→q∼q' (∼p-sym p'∼p)

            q'≁q→p'≁p : (q' ≁q q) → (p' ≁p p)
            q'≁q→p'≁p q'≁q = CoherentSpace.≁-sym P (q≁q'→p≁p' q≁q')
              where
                q≁q' : q ≁q q'
                q≁q' = CoherentSpace.≁-sym Q q'≁q


CohL : ∀ {c ℓ} → Category _ _ _
CohL {c} {ℓ} = record
  { Obj = CoherentSpace c ℓ 
  ; _⇒_ = _⇒'_
  ; _≈_ = (λ {A} {B} → _≈'_ {A} {B})
  ; id = (λ {A} → identity {A})
  ; _∘_ = (λ {A} {B} {C} → comp {A} {B} {C})
  ; assoc = (λ {A} {B} {C} {D} {f} {g} {h} → assoc {A} {B} {C} {D} {f} {g} {h})
  ; sym-assoc = (λ {A} {B} {C} {D} {f} {g} {h} → sym-assoc {A} {B} {C} {D} {f} {g} {h})
  ; identityˡ = (λ {A} {B} {f} → identityˡ {A} {B} {f})
  ; identityʳ = (λ {A} {B} {f} → identityʳ {A} {B} {f})
  ; identity² = (λ {A} → identityˡ {A} {A} {identity {A}}) 
  ; equiv = λ {A} {B} → equiv {A} {B}
  ; ∘-resp-≈ = λ {A} {B} {C} {f} {g} {h} {i} →  ∘-resp-≈ {A} {B} {C} {f} {g} {h} {i}
  }
  where
    

    _⇒'_ : CoherentSpace c ℓ → CoherentSpace c ℓ → Set _
    _⇒'_ P Q = CoherentSpace.Point (P ⇒ₗ Q)

    _≈'_ : {A B : CoherentSpace c ℓ} → Rel (A ⇒' B) c
    _≈'_ f g = (proj₁ f) ⇔ (proj₁ g)

    equiv : ∀ {A B : CoherentSpace c ℓ} → IsEquivalence (_≈'_ {A} {B})
    equiv {A} {B} = record { sym = λ {f} {g} → sym {f} {g} ; trans = λ {f} {g} {h} → trans {f} {g} {h} ; refl = λ {f} → refl {f}}
      where
        open CoherentSpace (A ⇒ₗ B)

        _eq_ : Rel (CoherentSpace.Point $ A ⇒ₗ B) _
        _eq_ = _≈'_ {A} {B}

        refl : ∀ {f : A ⇒' B} → (f eq f)
        refl {f} = (λ f⊆f → f⊆f) , (λ f⊆f → f⊆f)
        
        sym : ∀ {f g : A ⇒' B} → (f eq g) → (g eq f)
        sym {f} {g} (f⊆g , g⊆f) = g⊆f , f⊆g

        trans : ∀ {f g h : A ⇒' B} → (f eq g) → (g eq h) → (f eq h)
        trans {f} {g} {h} (f⊆g , g⊆f) (g⊆h , h⊆g) = ((λ {ab} ab∈f → g⊆h (f⊆g ab∈f)) , (λ {ab} ab∈h → g⊆f (h⊆g ab∈h)))  

    identity : {A : CoherentSpace c ℓ} → (A ⇒' A)
    identity {A} = (pred , (predIsPoint , pred-Respects-≈))
      where
        open CoherentSpace A

        pred : Pred (CoherentSpace.TokenSet (A ⇒ₗ A)) _
        pred (a , a') = a ≈ a'

        predIsPoint : CoherentSpace.isPoint (A ⇒ₗ A) pred
        predIsPoint (a , a') (a'' , a''') a≈a' a''≈a''' = a∼a''→a'∼a''' , a'≁a'''→a≁a''
          where
            a∼a' : a ∼ a'
            a∼a' = ≈→∼ a≈a'

            a≁a' : a ≁ a'
            a≁a' = inj₁ a≈a'
            
            a∼a''→a'∼a''' : a ∼ a'' → a' ∼ a'''
            a∼a''→a'∼a''' a∼a'' = ∼-sym (∼-respˡ-≈ a''≈a''' (∼-sym a'∼a''))
              where
                a'∼a'' : a' ∼ a''
                a'∼a'' = ∼-respˡ-≈ a≈a' a∼a''

            a'≁a'''→a≁a'' : (a' ≁ a''') → (a ≁ a'')
            a'≁a'''→a≁a'' (inj₁ a'≈a''') = inj₁ a≈a''
              where
                open IsEquivalence ≈-isEquivalence

                a≈a''' : a ≈ a'''
                a≈a''' = trans a≈a' a'≈a'''

                a≈a'' : a ≈ a''
                a≈a'' = trans a≈a''' (sym a''≈a''') 
            a'≁a'''→a≁a'' (inj₂ ¬a'∼a''') = inj₂ ¬a∼a''
              where
                ¬a∼a'' : ¬ (a ∼ a'')
                ¬a∼a'' a∼a'' = ⊥-elim (¬a'∼a''' a'∼a''')
                  where
                    a∼a''' : a ∼ a'''
                    a∼a''' = ∼-sym (∼-respˡ-≈ a''≈a''' (∼-sym a∼a''))

                    a'∼a''' : a' ∼ a'''
                    a'∼a''' = ∼-respˡ-≈ a≈a' a∼a'''
        
        pred-Respects-≈ : pred Respects (CoherentSpace._≈_ (A ⇒ₗ A))
        pred-Respects-≈ {(a₁ , a₂)} {(a₁' , a₂')} (a₁≈a₁' , a₂≈a₂') a₁≈a₂ = trans (trans (sym a₁≈a₁') a₁≈a₂) a₂≈a₂'
          where
            open IsEquivalence (CoherentSpace.≈-isEquivalence A)

    comp : ∀ {A B C : CoherentSpace c ℓ} → (B ⇒' C) → (A ⇒' B) → (A ⇒' C)
    comp {A} {B} {C} (g , (g-isPoint , g-Respects-≈)) (f , (f-isPoint , f-Respects-≈)) = pred , isPoint , pred-respects-≈
      where
        pred : Pred (CoherentSpace.TokenSet (A ⇒ₗ C)) _
        pred (a , c) =  Σ[ b ∈ (CoherentSpace.TokenSet B) ] ((a , b) ∈ f) × ((b , c) ∈ g)
        
        pred-respects-≈ : pred Respects CoherentSpace._≈_ (A ⇒ₗ C)
        pred-respects-≈ {(a , c)} {(a' , c')} (a≈a' , c≈c') (b , (ab∈f , bc∈g)) = (b , (a'b∈f , bc'∈g))
          where
            open CoherentSpace (A ⇒ₗ B) renaming (_≈_ to _≈ab_) 
            open CoherentSpace (B ⇒ₗ C) renaming (_≈_ to _≈bc_) 
            open IsEquivalence (CoherentSpace.≈-isEquivalence B) renaming (refl to ≈b-refl)
 
            ab≈a'b : (a , b) ≈ab (a' , b)
            ab≈a'b = (a≈a' , ≈b-refl)

            a'b∈f : (a' , b) ∈ f
            a'b∈f = f-Respects-≈ ab≈a'b ab∈f  
            
            bc≈bc' : (b , c) ≈bc (b , c')
            bc≈bc' = (≈b-refl , c≈c')

            bc'∈g : (b , c') ∈ g
            bc'∈g = g-Respects-≈ bc≈bc' bc∈g

        isPoint : CoherentSpace.isPoint (A ⇒ₗ C) pred 
        isPoint (a , c) (a' , c') (b , (ab∈f , bc∈g)) (b' , (a'b'∈f , b'c'∈g)) = a∼a'→c∼c' , c≁c'→a≁a'
          where
            open CoherentSpace A renaming (_∼_ to _∼a_ ; _≈_ to _≈a_ ; _≁_ to _≁a_)
            open CoherentSpace B renaming (_∼_ to _∼b_ ; _≈_ to _≈b_ ; _≁_ to _≁b_)
            open CoherentSpace C renaming (_∼_ to _∼c_ ; _≈_ to _≈c_ ; _≁_ to _≁c_)

            a∼a'→c∼c' : (a ∼a a') → (c ∼c c')
            a∼a'→c∼c' a∼a' = proj₁ (g-isPoint (b , c) (b' , c') bc∈g b'c'∈g) b∼b'
              where
                b∼b' : b ∼b b'
                b∼b' = proj₁ (f-isPoint (a , b) (a' , b') ab∈f a'b'∈f) a∼a'

            c≁c'→a≁a' : (c ≁c c') → (a ≁a a')
            c≁c'→a≁a' c≁c' = proj₂ (f-isPoint (a , b) (a' , b') ab∈f a'b'∈f) b≁b'
              where
                b≁b' : b ≁b b'
                b≁b' = proj₂ (g-isPoint (b , c) (b' , c') bc∈g b'c'∈g) c≁c' 

    assoc : ∀ {A B C D} {f : A ⇒' B} {g : B ⇒' C} {h : C ⇒' D} → 
            _≈'_ {A} {D} (comp {A} {B} {D} (comp {B} {C} {D} h g) f) 
                         (comp {A} {C} {D} h (comp {A} {B} {C} g f))
    assoc {A} {B} {C} {D} {f} {g} {h} = hg∘f⊆h∘gf , h∘gf⊆hg∘f
      where
        _∘ABD_ = comp {A} {B} {D}
        _∘BCD_ = comp {B} {C} {D}
        _∘ACD_ = comp {A} {C} {D}
        _∘ABC_ = comp {A} {B} {C}
 
        hg∘f : Pred (CoherentSpace.TokenSet (A ⇒ₗ D)) _
        hg∘f = proj₁ ((h ∘BCD g) ∘ABD f)

        h∘gf : Pred (CoherentSpace.TokenSet (A ⇒ₗ D)) _
        h∘gf = proj₁ (h ∘ACD (g ∘ABC f))

        hg∘f⊆h∘gf : hg∘f ⊆ h∘gf
        hg∘f⊆h∘gf {(a , d)} (b , (ab∈f , (c , (bc∈g , cd∈h)))) = (c , (ac∈g∘f , cd∈h))
          where
            ac∈g∘f : (a , c) ∈ (proj₁ $ g ∘ABC f)
            ac∈g∘f = (b , (ab∈f , bc∈g))

        h∘gf⊆hg∘f : h∘gf ⊆ hg∘f
        h∘gf⊆hg∘f {(a , d)} (c , ((b , (ab∈f , bc∈g)), cd∈h)) = (b , (ab∈f , bd∈h∘g))
          where
            bd∈h∘g : (b , d) ∈ (proj₁ $ h ∘BCD g)
            bd∈h∘g = (c , (bc∈g , cd∈h))

    sym-assoc : ∀ {A B C D} {f} {g} {h} → 
                  _≈'_ {A} {D} (comp {A} {C} {D} h (comp {A} {B} {C} g f))  
                  (comp {A} {B} {D} (comp {B} {C} {D} h g) f)
    sym-assoc {A} {B} {C} {D} {f} {g} {h} with (assoc {A} {B} {C} {D} {f} {g} {h}) 
    sym-assoc {A} {B} {C} {D} {f} {g} {h} | (hg∘f⊆h∘gf , h∘gf⊆hg∘f) = (h∘gf⊆hg∘f , hg∘f⊆h∘gf) 

    identityˡ : ∀ {A B} {f : A ⇒' B} → _≈'_ {A} {B} (comp {A} {B} {B} (identity {B}) f) f
    identityˡ {A} {B} {f} = ab∈id∘f→ab∈f , ab∈f→ab∈id∘f
      where
        f-respˡ-≈ = proj₂ (proj₂ f)
        _∘ABB_ = comp {A} {B} {B}
        id-B = identity {B}
        
        ab∈f→ab∈id∘f : {ab : CoherentSpace.TokenSet (A ⇒ₗ B)} → (ab ∈ (proj₁ f)) → (ab ∈ (proj₁ $ id-B ∘ABB f)) 
        ab∈f→ab∈id∘f {a , b} ab∈f  = (b , (ab∈f , ≈b-refl))
          where
            open IsEquivalence (CoherentSpace.≈-isEquivalence B) renaming (refl to ≈b-refl)
            
        ab∈id∘f→ab∈f : {ab : CoherentSpace.TokenSet (A ⇒ₗ B)} → (ab ∈ (proj₁ $ id-B ∘ABB f)) → (ab ∈ (proj₁ f))
        ab∈id∘f→ab∈f {a , b} (b' , (ab'∈f , b'≈b)) = f-respˡ-≈ (≈ab-sym ab≈ab') ab'∈f 
          where
            open CoherentSpace A renaming (_≈_ to _≈a_)
            open CoherentSpace B renaming (_≈_ to _≈b_)
            open IsEquivalence (CoherentSpace.≈-isEquivalence A) renaming (refl to ≈a-refl)
            open IsEquivalence (CoherentSpace.≈-isEquivalence B) renaming (sym to ≈b-sym)
            open IsEquivalence (CoherentSpace.≈-isEquivalence $ A ⇒ₗ B) renaming (sym to ≈ab-sym)
            open CoherentSpace (A ⇒ₗ B) renaming (_≈_ to _≈ab_ ; ∼-respˡ-≈ to ∼AB-respˡ-≈AB)

            ab≈ab' : (a , b) ≈ab (a , b')
            ab≈ab' = (≈a-refl , ≈b-sym b'≈b)

    identityʳ : ∀ {A B} {f : A ⇒' B} → _≈'_ {A} {B} (comp {A} {A} {B} f (identity {A})) f
    identityʳ {A} {B} {f} = ab∈f∘id→ab∈f , ab∈f→ab∈f∘id
      where
        f-respˡ-≈ = proj₂ (proj₂ f)
        _∘AAB_ = comp {A} {A} {B}
        id-A = identity {A}

        ab∈f→ab∈f∘id : {ab : CoherentSpace.TokenSet (A ⇒ₗ B)} → (ab ∈ (proj₁ f)) → (ab ∈ (proj₁ $ f ∘AAB id-A))
        ab∈f→ab∈f∘id {a , b} ab∈f = (a , (≈a-refl , ab∈f))
          where
            open IsEquivalence (CoherentSpace.≈-isEquivalence A) renaming (refl to ≈a-refl)

        ab∈f∘id→ab∈f : {ab : CoherentSpace.TokenSet (A ⇒ₗ B)} → (ab ∈ (proj₁ $ f ∘AAB id-A)) → (ab ∈ (proj₁ f))
        ab∈f∘id→ab∈f {a , b} (a' , (a≈a' , a'b∈f)) = f-respˡ-≈ (≈ab-sym ab≈a'b) a'b∈f
          where
            open CoherentSpace A renaming (_≈_ to _≈a_)
            open CoherentSpace B renaming (_≈_ to _≈b_)
            open IsEquivalence (CoherentSpace.≈-isEquivalence A) renaming (sym to ≈a-sym)
            open IsEquivalence (CoherentSpace.≈-isEquivalence B) renaming (refl to ≈b-refl)
            open IsEquivalence (CoherentSpace.≈-isEquivalence $ A ⇒ₗ B) renaming (sym to ≈ab-sym)
            open CoherentSpace (A ⇒ₗ B) renaming (_≈_ to _≈ab_ ; ∼-respˡ-≈ to ∼AB-respˡ-≈AB)
            
            ab≈a'b : (a , b) ≈ab (a' , b)
            ab≈a'b = (a≈a' , ≈b-refl)

    ∘-resp-≈ : {A B C : CoherentSpace c ℓ} {f h : B ⇒' C} {g i : A ⇒' B} → (_≈'_ {B} {C} f h) → (_≈'_ {A} {B} g i) → (_≈'_ {A} {C} (comp {A} {B} {C} f g) (comp {A} {B} {C} h i))
    ∘-resp-≈ {A} {B} {C} {f} {h} {g} {i} (bc∈f→bc∈h , bc∈h→bc∈f) (ab∈g→ab∈i , ab∈i→ab∈g) = ac∈f∘g→ac∈h∘i , ac∈h∘i→ac∈f∘g
      where
        _∘ABC_ = comp {A} {B} {C}
        |A| = CoherentSpace.TokenSet A
        |C| = CoherentSpace.TokenSet C

        ac∈f∘g→ac∈h∘i : ∀ {a : |A|} {c : |C|} → (a , c) ∈ (proj₁ $ f ∘ABC g) → (a , c) ∈ (proj₁ $ h ∘ABC i)
        ac∈f∘g→ac∈h∘i {a} {c} (b , (ab∈g , bc∈f)) = b , ab∈g→ab∈i ab∈g , bc∈f→bc∈h bc∈f 

        ac∈h∘i→ac∈f∘g : ∀ {a : |A|} {c : |C|} → (a , c) ∈ (proj₁ $ h ∘ABC i) → (a , c) ∈ (proj₁ $ f ∘ABC g)
        ac∈h∘i→ac∈f∘g {a} {c} (b , (ab∈i , bc∈h)) = b , ab∈i→ab∈g ab∈i , bc∈h→bc∈f bc∈h
