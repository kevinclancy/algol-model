{-# OPTIONS --without-K --safe #-}

module SymmetricMonoidal where

open import Level

open import Function using (_$_)
open import Data.Product
open import Data.Sum hiding ([_,_])
open import Data.Empty

open import Relation.Binary using 
  (Rel ; _Respectsˡ_ ; Symmetric ; Transitive ; Reflexive ; IsEquivalence ; 
   _Respects_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Unary
open import Relation.Unary.Properties using (⊆-refl)
open import Relation.Nullary

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Structure using (SymmetricMonoidalCategory)
open import Categories.Functor.Bifunctor

open import CoherentSpace


_∣_⇒_⇒_[_∘_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y Z : Category.Obj C) → (g : C [ Y , Z ]) → (f : C [ X , Y ]) → C [ X , Z ]
C ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ C g f) 

_∣_⇒_[_≈_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y : Category.Obj C) → (g : C [ X , Y ]) → (f : C [ X , Y ]) → Set _
C ∣ X ⇒ Y [ g ≈ f ] = (Category._≈_ C g f) 



SMCC-CohL : ∀ {c} → SymmetricMonoidalCategory _ _ _
SMCC-CohL {c} = record
  { U = CohL {c} {c} 
  ; monoidal = monoidal
  ; symmetric = {!!}
  }
  where
    
    CohL' = CohL {c} {c}
    open Category CohL' using (Obj)
    
    monoidal : Monoidal CohL'
    monoidal = record
      { ⊗ = ⊗
      ; unit = unit
      ; unitorˡ = unitorˡ
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
       ⊗ : Bifunctor CohL' CohL' CohL'
       ⊗ = record
         { F₀ = F₀
         ; F₁ = λ {A×B} {C×D} → F₁ {A×B} {C×D} 
         ; identity = λ {A} → identity {A}
         ; homomorphism = λ {X} {Y} {Z} {f} {g} → hom {X} {Y} {Z} {f} {g}
         ; F-resp-≈ = λ {A} {B} {f} {g} → F-resp-≈ {A} {B} {f} {g}
         }
         where
           open Category.Equiv CohL' 

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
                           ¬ab∼a'b' (a∼a' , b∼b') = ¬b∼b' b∼b'
                       cd≁c'd'→ab≁a'b' (inj₁ (c≈c' , d≈d')) | inj₂ ¬a∼a' | b≁b' = inj₂ ¬ab∼a'b'
                         where
                           ¬ab∼a'b' : ¬ (a , b) ∼A⊗B (a' , b')
                           ¬ab∼a'b' (a∼a' , b∼b') = ¬a∼a' a∼a'                           
                       cd≁c'd'→ab≁a'b' (inj₂ ¬cd∼c'd') = inj₂ ¬ab∼a'b'
                         where
                           ¬ab∼a'b' : ¬ (a , b) ∼A⊗B (a' , b')
                           ¬ab∼a'b' (a∼a' , b∼b') = ¬cd∼c'd' (a∼a'→c∼c' a∼a' , b∼b'→d∼d' b∼b') 

                   P-Respects-≈ : P Respects _≈_  
                   P-Respects-≈ ((a , b) , (c , d)) (ac∈f , bd∈g) = f-Respects-≈A⊗C (a , c) ac∈f , g-Respects-≈B⊗D (b , d) bd∈g

               --]]]

           identity : {(A , B) : Obj × Obj} → _[_≈_] CohL' {F₀ $ A , B} {F₀ $ A , B} (F₁ {A , B} {A , B} (Category.id (Product CohL' CohL') {A , B})) (Category.id CohL' {F₀ $ A , B})
           --[[[
           identity {A , B} = (λ {x} → id⊗id⊆id {x}) , (λ {x} → id⊆id⊗id {x})
             where
               id  = proj₁ (Category.id CohL' {F₀ $ A , B})
               id⊗id  = proj₁ (F₁ {A , B} {A , B} (Category.id (Product CohL' CohL') {A , B}))

               id⊗id⊆id : id⊗id ⊆ id
               id⊗id⊆id {(a , b) , (a' , b')} (a≈a' , b≈b') = (a≈a' , b≈b')

               id⊆id⊗id : id ⊆ id⊗id
               id⊆id⊗id {(a , b) , (a' , b')} (a≈a' , b≈b') = (a≈a' , b≈b')
           --]]]
           
           module _ {X Y Z : Obj × Obj} {f : Product CohL' CohL' [ X , Y ]} {g : Product CohL' CohL' [ Y , Z ]} where

             _∘CC_ = Category._∘_ (Product CohL' CohL') {X} {Y} {Z}
             _∘C_ = Category._∘_ CohL' {F₀ X} {F₀ Y} {F₀ Z}
             _≈C_ = Category._≈_ CohL' {F₀ X} {F₀ Z}

             hom : (F₁ {X} {Z} $ g ∘CC f) ≈C ((F₁ {Y} {Z} g) ∘C (F₁ {X} {Y} f))
             --[[[
             hom = F[g∘f]⊆F[g]∘F[f] , F[g]∘F[f]⊆F[g∘f]
               where
                 pred-F[g∘f] = proj₁ (F₁ {X} {Z} (g ∘CC f))
                 pred-F[g]∘F[f] = proj₁ ((F₁ {Y} {Z} g) ∘C (F₁ {X} {Y} f))
                 
                 F[g∘f]⊆F[g]∘F[f] : pred-F[g∘f] ⊆ pred-F[g]∘F[f]  
                 F[g∘f]⊆F[g]∘F[f] {((x₁ , x₂) , (z₁ , z₂))} ((y₁ , x₁y₁∈f₁ , y₁z₁∈g₁) , (y₂ , x₂y₂∈f₂ , y₂z₂∈g₂)) = p
                   where
                     p : ((x₁ , x₂) , (z₁ , z₂)) ∈ pred-F[g]∘F[f] 
                     p = (y₁ , y₂) , (x₁y₁∈f₁ , x₂y₂∈f₂) , (y₁z₁∈g₁ , y₂z₂∈g₂)


                 F[g]∘F[f]⊆F[g∘f] : pred-F[g]∘F[f] ⊆ pred-F[g∘f]  
                 F[g]∘F[f]⊆F[g∘f] {((x₁ , x₂) , (z₁ , z₂))} ((y₁ , y₂) , (x₁y₁∈f₁ , x₂y₂∈f₂) , (y₁z₁∈g₁ , y₂z₂∈g₂)) = p
                   where
                     p : ((x₁ , x₂) , (z₁ , z₂)) ∈ pred-F[g∘f]
                     p = (y₁ , x₁y₁∈f₁ , y₁z₁∈g₁) , (y₂ , x₂y₂∈f₂ , y₂z₂∈g₂)
             --]]]

           module _ {A B : Obj × Obj} {f g : Product CohL' CohL' [ A , B ]} where
             
             F-resp-≈ : (Product CohL' CohL' ∣ A ⇒ B [ f ≈ g ]) → (CohL' ∣ (F₀ A) ⇒ (F₀ B) [ (F₁ {A} {B} f) ≈ (F₁ {A} {B} g) ])
             F-resp-≈ ((f₁⊆g₁ , g₁⊆f₁) , (f₂⊆g₂ , g₂⊆f₂)) = F[f]⊆F[g] , F[g]⊆F[f]
               where
                 F[f]⊆F[g] : proj₁ (F₁ {A} {B} f) ⊆ proj₁ (F₁ {A} {B} g)
                 F[f]⊆F[g] {(a₁ , a₂) , (b₁ , b₂)} (a₁b₁∈f₁ , a₂b₂∈f₂) = f₁⊆g₁ a₁b₁∈f₁ , f₂⊆g₂ a₂b₂∈f₂ 

                 F[g]⊆F[f] : proj₁ (F₁ {A} {B} g) ⊆ proj₁ (F₁ {A} {B} f)
                 F[g]⊆F[f] {(a₁ , a₂) , (b₁ , b₂)} (a₁b₁∈g₁ , a₂b₂∈g₂) = g₁⊆f₁ a₁b₁∈g₁ , g₂⊆f₂ a₂b₂∈g₂

       data |1| : Set c where
         ∗ : |1|

       data _≈1_ : |1| → |1| → Set c where
         ∗≈∗ : ∗ ≈1 ∗

       unit : Obj
       unit = record 
         { TokenSet = |1| 
         ; _≈_ = _≈1_
         ; _∼_ = _≈1_
         ; ∼-respˡ-≈ = λ {x} {y} {y'} y≈y' x≈y → ≈-trans (≈-sym y≈y') x≈y
         ; ≈→∼ = λ a≈b → a≈b
         ; ∼-sym = ≈-sym
         ; ∼-refl = ≈-refl
         ; ≈-isEquivalence = record 
             { refl = ≈-refl 
             ; sym = ≈-sym
             ; trans = ≈-trans 
             } 
         }
         where
           ≈-trans : ∀ {x y z : |1|} → x ≈1 y → y ≈1 z → x ≈1 z
           ≈-trans {∗} {∗} {∗} refl₁ refl₂  = ∗≈∗
 
           ≈-sym : ∀ {x y : |1|} → x ≈1 y → y ≈1 x
           ≈-sym {∗} {∗} ∗≈∗ = ∗≈∗
  
           ≈-refl : ∀ {x : |1|} → x ≈1 x
           ≈-refl {∗} = ∗≈∗ 

       module _ {X : Obj} where
         open import Categories.Morphism using (_≅_)
         import Categories.Functor
         open Categories.Functor.Functor ⊗
         _≅CohL_ = _≅_ CohL'
         _≈X_ = CoherentSpace._≈_ X
         ≈X-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X)

         unitorˡ : F₀ (unit , X) ≅CohL X
         unitorˡ = record
           { from = from , from-isPoint , from-resp-≈
           ; to = to , to-isPoint , to-resp-≈
           ; iso = iso
           }
           where
             unit⊗X⇒X = F₀ (unit , X) ⇒ₗ X
             X⇒unit⊗X = X ⇒ₗ F₀ (unit , X)

             _∼1⊗X_ = CoherentSpace._∼_ (F₀ $ unit , X)  
             _≁1⊗X_ = CoherentSpace._≁_ (F₀ $ unit , X) 

             _∼X_ = CoherentSpace._∼_ X
             ∼X-respˡ-≈X = CoherentSpace.∼-respˡ-≈ X
             ∼X-respʳ-≈X = CoherentSpace.∼-respʳ-≈ X

             _≁X_ = CoherentSpace._≁_ X

             from : Pred (CoherentSpace.TokenSet unit⊗X⇒X) c
             from ((_ , x) , x') = x ≈X x'

             from-isPoint : CoherentSpace.isPoint unit⊗X⇒X from
             --[[[

             from-isPoint ((∗ , a) , a') ((∗ , b) , b') a≈a' b≈b' = p , q
               where
                 p : (∗ , a) ∼1⊗X (∗ , b) → a' ∼X b'
                 p (_ , a∼b) = ∼X-respˡ-≈X a≈a' (∼X-respʳ-≈X b≈b' a∼b)

                 q : (a' ≁X b') → (∗ , a) ≁1⊗X (∗ , b)
                 q (inj₁ a'≈b') = inj₁ (∗≈∗  , a≈b)
                   where
                     import Relation.Binary.Reasoning.Setoid as SetR
                     open SetR (CoherentSpace.setoid X)
                     a≈b : a ≈X b
                     a≈b = begin 
                         a   ≈⟨ a≈a' ⟩
                         a'  ≈⟨ a'≈b' ⟩
                         b' ≈˘⟨ b≈b' ⟩
                         b
                       ∎
                 q (inj₂ ¬a'∼b') = inj₂ ¬∗a∼∗b
                   where
                     ¬∗a∼∗b : ¬ (∗ , a) ∼1⊗X (∗ , b)
                     ¬∗a∼∗b (_ , a∼b) = ¬a'∼b' (∼X-respʳ-≈X b≈b' a'∼b)
                       where
                         a'∼b : a' ∼X b
                         a'∼b = ∼X-respˡ-≈X a≈a' a∼b

             --]]]

             from-resp-≈ : from Respects (CoherentSpace._≈_ unit⊗X⇒X) 
             --[[[
             from-resp-≈ {(∗ , a) , a' } {(∗ , b) , b'} ((_ , a≈b) , a'≈b') a≈a' = begin
                 b ≈˘⟨ a≈b ⟩
                 a  ≈⟨ a≈a' ⟩
                 a' ≈⟨ a'≈b' ⟩
                 b'
               ∎
               where
                 import Relation.Binary.Reasoning.Setoid as SetR
                 open SetR (CoherentSpace.setoid X)               
             --]]]

             to : Pred (CoherentSpace.TokenSet X⇒unit⊗X) c
             to (x , (_ , x')) = x ≈X x'

             to-isPoint : CoherentSpace.isPoint X⇒unit⊗X to
             --[[[
             to-isPoint (a , (∗ , a')) (b , (∗ , b')) a≈a' b≈b' = p , q
               where
                 p : a ∼X b → (∗ , a') ∼1⊗X (∗ , b')
                 p a∼b = ∗≈∗ , ∼X-respʳ-≈X b≈b' a'∼b 
                   where
                     a'∼b : a' ∼X b
                     a'∼b = ∼X-respˡ-≈X a≈a' a∼b

                 q : (∗ , a') ≁1⊗X (∗ , b') → a ≁X b
                 q (inj₁ (∗≈∗ , a'≈b')) = inj₁ r
                   where
                     import Relation.Binary.Reasoning.Setoid as SetR
                     open SetR (CoherentSpace.setoid X)

                     r : a ≈X b
                     r = begin
                         a   ≈⟨ a≈a' ⟩
                         a'  ≈⟨ a'≈b' ⟩
                         b' ≈˘⟨ b≈b' ⟩
                         b
                       ∎ 
                 q (inj₂ ¬∗a'∼∗b') = inj₂ ¬a∼b
                   where
                     import Relation.Binary.Reasoning.Setoid as SetR
                     open SetR (CoherentSpace.setoid X)

                     ¬a∼b : ¬ (a ∼X b)
                     ¬a∼b a∼b = ¬∗a'∼∗b' (∗≈∗ , a'∼b')
                       where
                         a'∼b : a' ∼X b
                         a'∼b = ∼X-respˡ-≈X a≈a' a∼b

                         a'∼b' : a' ∼X b'
                         a'∼b' = ∼X-respʳ-≈X b≈b' a'∼b
             --]]]

             to-resp-≈ : to Respects (CoherentSpace._≈_ X⇒unit⊗X) 
             --[[[
             to-resp-≈ {(a , (∗ , a'))} {(b , (∗ , b'))} (a≈b , (∗≈∗ , a'≈b')) a≈a' = b≈b'
               where
                 import Relation.Binary.Reasoning.Setoid as SetR
                 open SetR (CoherentSpace.setoid X)

                 b≈b' : b ≈X b'
                 b≈b' = begin
                     b ≈˘⟨ a≈b ⟩
                     a  ≈⟨ a≈a' ⟩ 
                     a' ≈⟨ a'≈b' ⟩
                     b'
                   ∎
             --]]]

             unit⊗X≅X = Categories.Morphism.Iso CohL' {F₀ (unit , X)} {X} 

             to-⇒ : CohL' [ X , (F₀ $ unit , X) ]
             to-⇒ = to , to-isPoint , to-resp-≈

             from-⇒ : CohL' [ (F₀ $ unit , X) , X ]             
             from-⇒ = from , from-isPoint , from-resp-≈

             iso : unit⊗X≅X from-⇒ to-⇒
             iso = record 
               { isoˡ = isoˡ 
               ; isoʳ = isoʳ
               }
               where
                 _≈1⊗X⇒1⊗X_ = Category._≈_ CohL' {F₀ (unit , X)} {F₀ (unit , X)}
                 _≈X⇒X_ = Category._≈_ CohL' {X} {X}
               
                 _∘₁_ = CohL' ∣ X ⇒ F₀ (unit , X) ⇒ X [_∘_]
                 _∘₂_ = CohL' ∣ F₀ (unit , X) ⇒ X ⇒ F₀ (unit , X) [_∘_]

                 f-⇒ = from-⇒ ∘₁ to-⇒
                 g-⇒ = to-⇒ ∘₂ from-⇒
                 idX-⇒ = Category.id CohL' {X}
                 id1⊗X-⇒ = Category.id CohL' {F₀ (unit , X)}

                 isoˡ : g-⇒ ≈1⊗X⇒1⊗X id1⊗X-⇒
                 isoˡ = g⊆id , id⊆g
                   where
                     g = proj₁ g-⇒
                     id = proj₁ id1⊗X-⇒

                     open IsEquivalence (CoherentSpace.≈-isEquivalence X)

                     g⊆id : g ⊆ id
                     g⊆id {(∗ , x) , (∗ , x')} (y , x≈y , y≈x') = ∗≈∗ , trans x≈y y≈x'

                     id⊆g : id ⊆ g
                     id⊆g {(∗ , x) , (∗ , x')} (∗≈∗ , x≈x') = x , refl , x≈x'

                 isoʳ : f-⇒ ≈X⇒X idX-⇒
                 isoʳ = f⊆id , id⊆f
                   where
                     f = proj₁ f-⇒
                     id = proj₁ idX-⇒

                     open IsEquivalence (CoherentSpace.≈-isEquivalence X)

                     f⊆id : f ⊆ id
                     f⊆id {x , x'} ((∗ , y) , x≈y , y≈x') = trans x≈y y≈x'

                     id⊆f : id ⊆ f
                     id⊆f {x , x'} x≈x' = (∗ , x) , refl , x≈x'
