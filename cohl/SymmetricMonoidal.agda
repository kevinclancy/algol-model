module SymmetricMonoidal where

open import Level

open import Function using (_$_)
open import Data.Product
open import Data.Sum hiding ([_,_])
open import Data.Empty

open import Relation.Binary
open import Relation.Unary
open import Relation.Unary.Properties using (⊆-refl)
open import Relation.Nullary

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal.Core
open import Categories.Category.Monoidal.Structure
open import Categories.Functor.Bifunctor

open import CoherentSpace


SMCC-CohL : ∀ {c} {ℓ} → SymmetricMonoidalCategory _ _ _
SMCC-CohL {c} {ℓ} = record
  { U = CohL {c} {ℓ} 
  ; monoidal = monoidal
  ; symmetric = {!!}
  }
  where
    CohL' = CohL {c} {ℓ}
    Obj = Category.Obj CohL'

    monoidal : Monoidal CohL'
    monoidal = record
      { ⊗ = ⊗
      ; unit = {!!}
      ; unitorˡ = {!!}
      ; unitorʳ = {!!}
      ; associator = {!!}
      ; unitorˡ-commute-from = {!!}
      ; unitorˡ-commute-to = {!!}
      ; unitorʳ-commute-from = {!!}
      ; unitorʳ-commute-to = {!!}
      ; assoc-commute-from = {!!}
      ; assoc-commute-to = {!!}
      ; triangle = {!!}
      ; pentagon = {!!}
      }
      where
       TokenSet = CoherentSpace.TokenSet

       ⊗ : Bifunctor CohL' CohL' CohL'
       ⊗ = record
         { F₀ = F₀
         ; F₁ = λ {A×B} {C×D} → F₁ {A×B} {C×D} 
         ; identity = λ {A} → identity {A}
         ; homomorphism = {!!} 
         ; F-resp-≈ = {!!}
         }
         where
           F₀ : (Obj × Obj) → Obj
           F₀ (A , B) = A⊗B
             --[[[
             where
               |A| = CoherentSpace.TokenSet A
               |B| = CoherentSpace.TokenSet B
               _≈A_ = CoherentSpace._≈_ A
               _≈B_ = CoherentSpace._≈_ B
               _∼A_ = CoherentSpace._∼_ A
               _∼B_ = CoherentSpace._∼_ B
               ∼A-sym = CoherentSpace.∼-sym A
               ∼A-refl = CoherentSpace.∼-refl A
               ∼B-sym = CoherentSpace.∼-sym B
               ∼B-refl = CoherentSpace.∼-refl B
               ∼A-respˡ-≈A = CoherentSpace.∼-respˡ-≈ A
               ∼A-respʳ-≈A = CoherentSpace.∼-respʳ-≈ A
               ∼B-respˡ-≈B = CoherentSpace.∼-respˡ-≈ B
               ∼B-respʳ-≈B = CoherentSpace.∼-respʳ-≈ B

               A⊗B : Obj
               A⊗B = record
                 { TokenSet = |A⊗B| 
                 ; _≈_ = _≈A⊗B_
                 ; _∼_ = _∼A⊗B_
                 ; ∼-respˡ-≈ = ∼A⊗B-respˡ-≈A⊗B
                 ; ≈→∼ = a,a'≈b,b'→a,a'∼b,b' 
                 ; ∼-sym = ∼A⊗B-sym
                 ; ∼-refl = ∼A⊗B-refl
                 ; ≈-isEquivalence = ≈A⊗B-isEquivalence
                 }
                 where
                   open import Data.Product.Relation.Binary.Pointwise.NonDependent

                   |A⊗B| : Set _
                   |A⊗B| = |A| × |B|
                 
                   _≈A⊗B_ : Rel |A⊗B| _ 
                   _≈A⊗B_ = Pointwise _≈A_ _≈B_

                   _∼A⊗B_ : Rel |A⊗B| _
                   _∼A⊗B_ = Pointwise _∼A_ _∼B_

                   ∼A⊗B-respˡ-≈A⊗B : _∼A⊗B_ Respectsˡ _≈A⊗B_ 
                   ∼A⊗B-respˡ-≈A⊗B {a , b} {a' , b'} {a'' , b''} (a'≈a'' , b'≈b'') (a'∼a , b'∼b) = ∼A-respˡ-≈A a'≈a'' a'∼a , ∼B-respˡ-≈B b'≈b'' b'∼b 
                       
                   a,a'≈b,b'→a,a'∼b,b'  : {(a , b) (a' , b') : |A⊗B|} → (a , b) ≈A⊗B (a' , b') → (a , b) ∼A⊗B (a' , b')
                   a,a'≈b,b'→a,a'∼b,b'  {a , b} {a' , b'} (a≈a' , b≈b') = a∼a' , b∼b'
                     where
                       a∼a' : a ∼A a'
                       a∼a' = ∼A-respʳ-≈A a≈a' $ ∼A-refl {a} 
                       
                       b∼b' : b ∼B b'
                       b∼b' = ∼B-respʳ-≈B b≈b' $ ∼B-refl {b}
               
                   ∼A⊗B-sym : Symmetric _∼A⊗B_
                   ∼A⊗B-sym {a , b} {a' , b'} (a∼a' , b∼b') = ∼A-sym a∼a' , ∼B-sym b∼b'

                   ∼A⊗B-refl : Reflexive _∼A⊗B_
                   ∼A⊗B-refl = ∼A-refl , ∼B-refl

                   ≈A⊗B-isEquivalence : IsEquivalence _≈A⊗B_
                   ≈A⊗B-isEquivalence = record
                     { sym = ≈A⊗B-sym
                     ; refl = ≈A⊗B-refl
                     ; trans = ≈A⊗B-trans
                     }
                     where
                       open IsEquivalence (CoherentSpace.≈-isEquivalence A) renaming 
                         (refl to ≈A-refl ; sym to ≈A-sym ; trans to ≈A-trans)

                       open IsEquivalence (CoherentSpace.≈-isEquivalence B) renaming 
                         (refl to ≈B-refl ; sym to ≈B-sym ; trans to ≈B-trans)

                       ≈A⊗B-sym : Symmetric _≈A⊗B_
                       ≈A⊗B-sym {a , b} {a' , b'} (a≈a' , b≈b') = ≈A-sym a≈a' , ≈B-sym b≈b'

                       ≈A⊗B-refl : Reflexive _≈A⊗B_
                       ≈A⊗B-refl {a , b} = ≈A-refl {a} , ≈B-refl {b} 

                       ≈A⊗B-trans : Transitive _≈A⊗B_
                       ≈A⊗B-trans {a , b} {a' , b'} {a'' , c''} (a≈a' , b≈b') (a'≈a'' , b'≈b'') = ≈A-trans a≈a' a'≈a'' , ≈B-trans b≈b' b'≈b''
                           
             --]]]

           F₁ : {(A , B) : Obj × Obj} → {(C , D) : Obj × Obj} → 
                (Product CohL' CohL' [ (A , B) , (C , D) ]) → 
                (CohL' [ F₀ (A , B) , F₀ (C , D) ])  
           F₁ {A , B} {C , D} ((f , f-isPoint , f-Respects-≈A⊗C) , (g , g-isPoint , g-Respects-≈B⊗D)) = f⊗g 
             where
               --[[[
               A⊗B⇒ₗC⊗D : CoherentSpace _ _ 
               A⊗B⇒ₗC⊗D = ((F₀ $ A , B) ⇒ₗ (F₀ $ C , D))
               
               _≈_ = CoherentSpace._≈_ A⊗B⇒ₗC⊗D 
      
               |A⊗B⇒ₗC⊗D| : Set _
               |A⊗B⇒ₗC⊗D| = CoherentSpace.TokenSet A⊗B⇒ₗC⊗D
               
               f⊗g : Σ[ P ∈ Pred |A⊗B⇒ₗC⊗D| _ ] ((CoherentSpace.isPoint A⊗B⇒ₗC⊗D P) × (P Respects _≈_)) 
               f⊗g = P , isPoint , P-Respects-≈
                 where
                   P : Pred |A⊗B⇒ₗC⊗D| _
                   P ((a , b) , (c , d)) = ((a , c) ∈ f) × ((b , d) ∈ g) 

                   isPoint : CoherentSpace.isPoint A⊗B⇒ₗC⊗D P
                   isPoint ((a , b) , (c , d)) ((a' , b') , (c' , d')) (ac∈f , bd∈g) (a'c'∈f , b'd'∈g) = 
                     ab∼a'b'→cd∼c'd' , cd≁c'd'→ab≁a'b'
                     where
                       _∼A⊗B_ = CoherentSpace._∼_ $ F₀ (A , B)
                       _≁A⊗B_ = CoherentSpace._≁_ $ F₀ (A , B)
                       _∼A⇒C_ = CoherentSpace._∼_ (A ⇒ₗ C)
                       _∼C⊗D_ = CoherentSpace._∼_ $ F₀ (C , D)
                       _≁C⊗D_ = CoherentSpace._≁_ $ F₀ (C , D)
                       _∼B⇒D_ = CoherentSpace._∼_ (B ⇒ₗ D)
                       _∼A_ = CoherentSpace._∼_ A
                       _∼B_ = CoherentSpace._∼_ B
                       _∼C_ = CoherentSpace._∼_ C
                       _∼D_ = CoherentSpace._∼_ D
                       _≁A_ = CoherentSpace._≁_ A
                       _≁B_ = CoherentSpace._≁_ B
                       _≁C_ = CoherentSpace._≁_ C
                       _≁D_ = CoherentSpace._≁_ D
               
                       ac∼a'c'  : (a , c) ∼A⇒C (a' , c')
                       ac∼a'c' = f-isPoint (a , c) (a' , c') ac∈f a'c'∈f 

                       a∼a'→c∼c' : a ∼A a' → c ∼C c'
                       a∼a'→c∼c' = proj₁ ac∼a'c'

                       c≁c'→a≁a' : c ≁C c' → a ≁A a'
                       c≁c'→a≁a' = proj₂ ac∼a'c' 

                       bd∼b'd' : (b , d) ∼B⇒D (b' , d')
                       bd∼b'd' = g-isPoint (b , d) (b' , d') bd∈g b'd'∈g

                       b∼b'→d∼d' : b ∼B b' → d ∼D d'
                       b∼b'→d∼d' = proj₁ bd∼b'd'

                       d≁d'→b≁b' : d ≁D d' → b ≁B b'
                       d≁d'→b≁b' = proj₂ bd∼b'd' 
                           
                       ab∼a'b'→cd∼c'd' : (a , b) ∼A⊗B (a' , b') → (c , d) ∼C⊗D (c' , d')
                       ab∼a'b'→cd∼c'd' (a∼a' , b∼b') = a∼a'→c∼c' a∼a'  , b∼b'→d∼d' b∼b'

                       cd≁c'd'→ab≁a'b' : (c , d) ≁C⊗D (c' , d') → (a , b) ≁A⊗B (a' , b')
                       cd≁c'd'→ab≁a'b' (inj₁ (c≈c' , d≈d')) with a≁a' | b≁b' 
                         where
                           a≁a' : a ≁A a'
                           a≁a' = c≁c'→a≁a' $ inj₁ c≈c'

                           b≁b' : b ≁B b'
                           b≁b' = d≁d'→b≁b' $ inj₁ d≈d' 
                       cd≁c'd'→ab≁a'b' (inj₁ (c≈c' , d≈d')) | inj₁ a≈a' | inj₁ b≈b' = inj₁ $ a≈a' , b≈b'
                       cd≁c'd'→ab≁a'b' (inj₁ (c≈c' , d≈d')) | inj₁ a≈a' | inj₂ ¬b∼b' = inj₂ ¬ab∼a'b'
                         where
                           ¬ab∼a'b' : ¬ (a , b) ∼A⊗B (a' , b')
                           ¬ab∼a'b' (a∼a' , b∼b') = ⊥-elim $ ¬b∼b' b∼b'
                       cd≁c'd'→ab≁a'b' (inj₁ (c≈c' , d≈d')) | inj₂ ¬a∼a' | b≁b' = inj₂ ¬ab∼a'b'
                         where
                           ¬ab∼a'b' : ¬ (a , b) ∼A⊗B (a' , b')
                           ¬ab∼a'b' (a∼a' , b∼b') = ⊥-elim $ ¬a∼a' a∼a'                           
                       cd≁c'd'→ab≁a'b' (inj₂ ¬cd∼c'd') = inj₂ ¬ab∼a'b'
                         where
                           ¬ab∼a'b' : ¬ (a , b) ∼A⊗B (a' , b')
                           ¬ab∼a'b' (a∼a' , b∼b') = ⊥-elim $ ¬cd∼c'd' (a∼a'→c∼c' a∼a' , b∼b'→d∼d' b∼b') 

                   P-Respects-≈ : P Respects _≈_  
                   P-Respects-≈ ((a , b) , (c , d)) (ac∈f , bd∈g) = f-Respects-≈A⊗C (a , c) ac∈f , g-Respects-≈B⊗D (b , d) bd∈g
               --]]]

           identity : {(A , B) : Obj × Obj} → _[_≈_] CohL' {F₀ $ A , B} {F₀ $ A , B} (F₁ {A , B} {A , B} (Category.id (Product CohL' CohL') {A , B})) (Category.id CohL' {F₀ $ A , B})
           identity {A , B} = (λ {x} → id⊗id⊆id {x}) , (λ {x} → id⊆id⊗id {x})
             where
               id  = proj₁ (Category.id {suc c ⊔ suc ℓ} {suc c ⊔ ℓ} {c} CohL' {F₀ $ A , B})
               id⊗id  = proj₁ (F₁ {A , B} {A , B} (Category.id {suc c ⊔ suc ℓ ⊔ (suc c ⊔ suc ℓ)} {suc c ⊔ ℓ ⊔ (suc c ⊔ ℓ)} {c ⊔ c} (Product CohL' CohL') {A , B}))

               id⊗id⊆id : id⊗id ⊆ id
               id⊗id⊆id {(a , b) , (a' , b')} (a≈a' , b≈b') = (a≈a' , b≈b')

               id⊆id⊗id : id ⊆ id
               id⊆id⊗id {(a , b) , (a' , b')} (a≈a' , b≈b') = (a≈a' , b≈b')

