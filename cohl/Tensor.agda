{-# OPTIONS --without-K --safe #-}
open import Level

module Tensor {c} where

open import Data.Product
open import Data.Sum hiding ([_,_])
open import Data.Empty

open import Relation.Binary using 
  (Rel ; _Respectsˡ_ ; Symmetric ; Transitive ; Reflexive ; IsEquivalence ; 
   _Respects_)
open import Relation.Unary
open import Relation.Nullary using (¬_)

open import Function using (_$_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Functor.Bifunctor

open import CoherentSpace

private
  CohL' = CohL {c} {c}
  open Category CohL' using (Obj)
  open Category.Equiv CohL' 

  _∣_⇒_⇒_[_∘_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y Z : Category.Obj C) → (g : C [ Y , Z ]) → (f : C [ X , Y ]) → C [ X , Z ]
  C ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ C g f) 

  _∣_⇒_[_≈_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y : Category.Obj C) → (g : C [ X , Y ]) → (f : C [ X , Y ]) → Set _
  C ∣ X ⇒ Y [ g ≈ f ] = (Category._≈_ C g f) 

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

⊗ : Bifunctor CohL' CohL' CohL'
⊗ = record
  { F₀ = F₀
  ; F₁ = λ {A×B} {C×D} → F₁ {A×B} {C×D} 
  ; identity = λ {A} → identity {A}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → hom {X} {Y} {Z} {f} {g}
  ; F-resp-≈ = λ {A} {B} {f} {g} → F-resp-≈ {A} {B} {f} {g}
  }
