{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level

module ObjectFunctor {c : Level} where

open import Categories.Category renaming (_[_,_] to _[_,,_]) 
open import Categories.Functor.Core using (Functor)
open import CoherentSpace using (CohL ; CoherentSpace ; _⇒ₗ_ ; _⇒'_)

open import Relation.Binary using (
  _Respects_ ; _Respectsˡ_ ; tri< ; tri> ; tri≈)
open import Relation.Binary.Core renaming (Rel to BinRel)
open import Relation.Binary.PropositionalEquality.Core as PE
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Unary using (Pred ; _∈_ ; _⊆_)
open import Relation.Unary.Properties using (⊆-refl)
open import Relation.Binary using 
  (Rel ; _Respectsˡ_ ; Symmetric ; Transitive ; Reflexive ; IsEquivalence ; 
   _Respects_)

open import Function using (_$_)

open import Data.List
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise) renaming (_∷_ to _∷PW_ ; [] to []PW)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥ ; ⊥-elim)

private
  CohL' = CohL {c}
  CoherentSpace' = CoherentSpace c
  open Category CohL' using (_⇒_; _∘_; id)
  CohL'[_∘_] = _[_∘_] CohL'
  open Commutation CohL'

  variable
    A B : CoherentSpace'

module ObjectSpace {A : CoherentSpace'} where
  
  |A| = CoherentSpace.TokenSet A
  |†A| = List |A|
  _∼A_ = CoherentSpace._∼_ A
  _≁A_ = CoherentSpace._≁_ A
  _≈A_ = CoherentSpace._≈_ A

  ≈A-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence A)
  ≈A-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence A)
  ≈A-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence A) 
  ≈A-decidable = CoherentSpace.≈-decidable A
 
  data _∼†A_ : List |A| → List |A| → Set c where
    EmptyLeft : ∀ {r} → [] ∼†A r
    EmptyRight : ∀ {l} → l ∼†A []
    HeadEqual : ∀ {l l' r r'} → (l ≈A r) → (l' ∼†A r') → (l ∷ l') ∼†A (r ∷ r')
    NotHeadEqual : ∀ {l l' r r'} → ¬ (l ≈A r) → (l ∼A r) → (l ∷ l') ∼†A (r ∷ r') 

  _≈†A_ = Pointwise _≈A_

  _≁†A_ : BinRel |†A| _
  _≁†A_ a₀ a₁ = (a₀ ≈†A a₁) ⊎ ¬ (a₀ ∼†A a₁)  

F₀ : CoherentSpace' → CoherentSpace'
F₀ A = †A 
  where
    ∼A-respˡ-≈A = CoherentSpace.∼-respˡ-≈ A
    ∼A-sym = CoherentSpace.∼-sym A
    ∼A-refl = CoherentSpace.∼-refl A

    open ObjectSpace {A}

    †A : CoherentSpace _
    †A = record
      { TokenSet = |†A|
      ; _≈_ = _≈†A_
      ; _∼_ = _∼†A_
      ; ≈-isEquivalence = PW.isEquivalence (CoherentSpace.≈-isEquivalence A)
      ; ≈-decidable = PW.decidable (CoherentSpace.≈-decidable A)
      ; ∼-respˡ-≈ = ∼-respˡ-≈
      ; ≈→∼ = ≈→∼
      ; ∼-sym = ∼-sym
      ; ∼-refl = ∼-refl
      }
      where
        ≈→∼ : {a b : |†A|} → Pointwise _≈A_ a b → a ∼†A b
        ≈→∼ {.[]} {.[]} Pointwise.[] = EmptyLeft
        ≈→∼ {a ∷ a'} {b ∷ b'} (a≈b ∷PW a'≈b') = HeadEqual a≈b (≈→∼ a'≈b')

        ∼-respˡ-≈ : _∼†A_ Respectsˡ _≈†A_
        ∼-respˡ-≈ {z} {.[]} {.[]} Pointwise.[] EmptyLeft = EmptyLeft
        ∼-respˡ-≈ {.[]} {x} {y} x≈y EmptyRight = EmptyRight
        ∼-respˡ-≈ {z ∷ z'} {x ∷ x'} {y ∷ y'} (x≈y ∷PW x'≈y') (HeadEqual x≈z x'∼z') = HeadEqual y≈z (∼-respˡ-≈ x'≈y' x'∼z')
          where
            y≈z : y ≈A z
            y≈z = ≈A-trans (≈A-sym x≈y) x≈z             
        ∼-respˡ-≈ {z ∷ z'} {x ∷ x'} {y ∷ y'} (x≈y ∷PW x'≈y') (NotHeadEqual ¬x≈z x∼z) = NotHeadEqual ¬y≈z (∼A-respˡ-≈A x≈y x∼z)
          where
            ¬y≈z : ¬ (y ≈A z)
            ¬y≈z y≈z = ¬x≈z (≈A-trans x≈y y≈z)

        ∼-sym : Symmetric _∼†A_
        ∼-sym {.[]} {y} EmptyLeft = EmptyRight
        ∼-sym {x} {.[]} EmptyRight = EmptyLeft
        ∼-sym {x ∷ x'} {y ∷ y'} (HeadEqual x≈y x'∼y') = HeadEqual (≈A-sym x≈y) (∼-sym x'∼y')
        ∼-sym {x ∷ x'} {y ∷ y'} (NotHeadEqual ¬x≈y x∼y) = NotHeadEqual ¬y≈x (∼A-sym x∼y)
          where
            ¬y≈x : ¬ (y ≈A x)
            ¬y≈x y≈x = ¬x≈y (≈A-sym y≈x)

        ∼-refl : Reflexive _∼†A_
        ∼-refl {[]} = EmptyLeft
        ∼-refl {x ∷ x'} = HeadEqual (≈A-refl {x}) (∼-refl {x'})
         
F₁ : ∀ {A B} → CohL' [ A ,, B ] → CohL' [ F₀ A ,, F₀ B ]
F₁ {A} {B} f@(record { pred = pred-f ; isPoint = isPoint-f ; resp-≈ = resp-≈-f }) = record
  { pred = pred
  ; isPoint = isPoint
  ; resp-≈ = resp-≈
  } 
  where
    |FA⇒ₗFB| = CoherentSpace.TokenSet $ (F₀ A) ⇒ₗ (F₀ B)
    _∼_ = CoherentSpace._∼_ $ (F₀ A) ⇒ₗ (F₀ B)
    _∼|A⇒ₗB|_ = CoherentSpace._∼_ $ A ⇒ₗ B
    _≈|FA⇒ₗFB|_ = CoherentSpace._≈_ $ (F₀ A) ⇒ₗ (F₀ B)

    module ObjectSpaceA = ObjectSpace {A}
    open ObjectSpaceA

    module ObjectSpaceB = ObjectSpace {B}  
    open ObjectSpaceB renaming (
      _≈†A_ to _≈†B_ ; _∼†A_ to _∼†B_ ; |†A| to |†B| ; _≁†A_ to _≁†B_ ;
      _≈A_ to _≈B_ ; _∼A_ to _∼B_ ; _≁A_ to _≁B_ ; ≈A-refl to ≈B-refl ;
      ≈A-decidable to ≈B-decidable)

    ≈†A-decidable = CoherentSpace.≈-decidable (F₀ A)
    ≈†B-decidable = CoherentSpace.≈-decidable (F₀ B)

    pred : Pred |FA⇒ₗFB| c
    pred (as , bs) = Pointwise (λ a b → pred-f (a , b)) as bs

    isPoint : ((as₁ , bs₁) (as₂ , bs₂) : |FA⇒ₗFB|) → (as₁ , bs₁) ∈ pred → (as₂ , bs₂) ∈ pred → (as₁ , bs₁) ∼ (as₂ , bs₂)
    --[[[
    isPoint (.[] , .[]) (.[] , .[]) Pointwise.[] Pointwise.[] = []∼†A[]→[]∼†B[] , []≁†B[]→[]≁†A
      where
        []∼†A[]→[]∼†B[] : [] ∼†A [] → [] ∼†B []
        []∼†A[]→[]∼†B[] []∼†A[] = ObjectSpaceB.EmptyLeft
        
        []≁†B[]→[]≁†A : [] ≁†B [] → [] ≁†A []
        []≁†B[]→[]≁†A []≁†B[] = inj₁ $ IsEquivalence.refl (CoherentSpace.≈-isEquivalence $ F₀ A) {[]}
    isPoint (.[] , .[]) ((a₂ ∷ as₂) , (b₂ ∷ bs₂)) Pointwise.[] (a₂,b₂∈f ∷PW as₂,bs₂∈f) = []-∼†A-as₂→[]∼†B-bs₂ , []-≁†B-bs₂→[]-≁†A-as₂
      where
        []-∼†A-as₂→[]∼†B-bs₂ : [] ∼†A (a₂ ∷ as₂) → [] ∼†B (b₂ ∷ bs₂)
        []-∼†A-as₂→[]∼†B-bs₂ []-∼†A-a₂ = ObjectSpaceB.EmptyLeft

        []-≁†B-bs₂→[]-≁†A-as₂ : [] ≁†B (b₂ ∷ bs₂) → [] ≁†A (a₂ ∷ as₂)
        []-≁†B-bs₂→[]-≁†A-as₂ (inj₂ ¬[]∼†B-b₂∷bs₂) = ⊥-elim $ ¬[]∼†B-b₂∷bs₂ ObjectSpaceB.EmptyLeft
    isPoint (a₁ ∷ as₁ , b₁ ∷ bs₁) ([] , []) (a₁,b₁∈f ∷PW as₁,bs₁∈pred) [],[]∈pred = a₁∷as₁∼[]→b₁∷bs₁∼[] , b₁∷bs₁≁[]→a₁∷as₁≁[]
      where
        a₁∷as₁∼[]→b₁∷bs₁∼[] : ((a₁ ∷ as₁) ∼†A []) → ((b₁ ∷ bs₁) ∼†B [])
        a₁∷as₁∼[]→b₁∷bs₁∼[] a₁∷as₁∼[] = ObjectSpaceB.EmptyRight

        b₁∷bs₁≁[]→a₁∷as₁≁[] : ((b₁ ∷ bs₁) ≁†B []) → ((a₁ ∷ as₁) ≁†A [])
        b₁∷bs₁≁[]→a₁∷as₁≁[] (inj₂ ¬b₁∷bs₁∼[]) = ⊥-elim $ ¬b₁∷bs₁∼[] ObjectSpaceB.EmptyRight
    isPoint (a₁ ∷ as₁ , b₁ ∷ bs₁) (a₂ ∷ as₂ , b₂ ∷ bs₂) (a₁,b₁∈f ∷PW as₁,bs₁∈pred) (a₂,b₂∈f ∷PW as₂,bs₂∈pred) = a₁∷as₁∼a₂∷as₂→b₁∷bs₁∼b₂∷bs₂ , b₁∷bs₁≁b₂∷bs₂→a₁∷as₁≁a₂∷as₂
      where
        as₁,bs₁∼as₂,bs₂ : CoherentSpace._∼_ ((F₀ A) ⇒ₗ (F₀ B)) (as₁ , bs₁) (as₂ , bs₂)
        as₁,bs₁∼as₂,bs₂ = isPoint (as₁ , bs₁) (as₂ , bs₂) as₁,bs₁∈pred as₂,bs₂∈pred

        a₁,b₁∼a₂,b₂ : (a₁ , b₁) ∼|A⇒ₗB| (a₂ , b₂)
        a₁,b₁∼a₂,b₂ = isPoint-f (a₁ , b₁) (a₂ , b₂) a₁,b₁∈f a₂,b₂∈f

        a₁∷as₁∼a₂∷as₂→b₁∷bs₁∼b₂∷bs₂ : ((a₁ ∷ as₁) ∼†A (a₂ ∷ as₂)) → ((b₁ ∷ bs₁) ∼†B (b₂ ∷ bs₂))
        --[[[
        a₁∷as₁∼a₂∷as₂→b₁∷bs₁∼b₂∷bs₂ (ObjectSpaceA.HeadEqual a₁≈a₂ as₁∼as₂) with (CoherentSpace.⇒'-functionalish f a₂,b₁∈f a₂,b₂∈f) | ≈B-decidable b₁ b₂ 
          where
            a₂,b₁∈f : pred-f (a₂ , b₁)
            a₂,b₁∈f = resp-≈-f (a₁≈a₂ , ≈B-refl {b₁}) a₁,b₁∈f
        a₁∷as₁∼a₂∷as₂→b₁∷bs₁∼b₂∷bs₂ (ObjectSpace.HeadEqual a₁≈a₂ as₁∼as₂) | b₁∼b₂ | yes b₁≈b₂ = ObjectSpaceB.HeadEqual b₁≈b₂ (as₁∼as₂→bs₁∼bs₂ as₁∼as₂)
          where
            as₁∼as₂→bs₁∼bs₂ : as₁ ∼†A as₂ → bs₁ ∼†B bs₂
            as₁∼as₂→bs₁∼bs₂ = proj₁ as₁,bs₁∼as₂,bs₂ 
        a₁∷as₁∼a₂∷as₂→b₁∷bs₁∼b₂∷bs₂ (ObjectSpace.HeadEqual a₁≈a₂ as₁∼as₂) | b₁∼b₂ | no ¬b₁≈b₂ = ObjectSpaceB.NotHeadEqual ¬b₁≈b₂ b₁∼b₂
        a₁∷as₁∼a₂∷as₂→b₁∷bs₁∼b₂∷bs₂ (ObjectSpace.NotHeadEqual ¬a₁≈a₂ a₁∼a₂) = ObjectSpaceB.NotHeadEqual ¬b₁≈b₂ b₁∼b₂
          where
            b₁∼b₂ : b₁ ∼B b₂
            b₁∼b₂ = proj₁ a₁,b₁∼a₂,b₂ $ a₁∼a₂

            ¬b₁≈b₂ : ¬ (b₁ ≈B b₂)
            ¬b₁≈b₂ b₁≈b₂ with a₁≁a₂ 
              where
                b₁≁b₂ : b₁ ≁B b₂
                b₁≁b₂ = inj₁ b₁≈b₂

                a₁≁a₂ : a₁ ≁A a₂
                a₁≁a₂ = proj₂ a₁,b₁∼a₂,b₂ $ b₁≁b₂
            ¬b₁≈b₂ b₁≈b₂ | inj₁ a₁≈a₂ = ¬a₁≈a₂ a₁≈a₂
            ¬b₁≈b₂ b₁≈b₂ | inj₂ ¬a₁∼a₂ = ¬a₁∼a₂ a₁∼a₂
        --]]]

        b₁∷bs₁≁b₂∷bs₂→a₁∷as₁≁a₂∷as₂ : ((b₁ ∷ bs₁) ≁†B (b₂ ∷ bs₂)) → ((a₁ ∷ as₁) ≁†A (a₂ ∷ as₂))
        --[[[
        b₁∷bs₁≁b₂∷bs₂→a₁∷as₁≁a₂∷as₂ (inj₁ (b₁≈b₂ ∷PW bs₁≈bs₂)) with a₁≁a₂ | as₁≁as₂ 
          where
            b₁≁b₂ : b₁ ≁B b₂
            b₁≁b₂ = inj₁ b₁≈b₂

            a₁≁a₂ : a₁ ≁A a₂
            a₁≁a₂ = proj₂ a₁,b₁∼a₂,b₂ $ b₁≁b₂

            bs₁≁bs₂ : bs₁ ≁†B bs₂
            bs₁≁bs₂ = inj₁ bs₁≈bs₂
          
            as₁≁as₂ : as₁ ≁†A as₂
            as₁≁as₂ = proj₂ as₁,bs₁∼as₂,bs₂ $ bs₁≁bs₂
        b₁∷bs₁≁b₂∷bs₂→a₁∷as₁≁a₂∷as₂ (inj₁ (b₁≈b₂ ∷PW bs₁≈bs₂)) | inj₁ a₁≈a₂ | inj₁ as₁≈as₂ = inj₁ (a₁≈a₂ ∷PW as₁≈as₂)
        b₁∷bs₁≁b₂∷bs₂→a₁∷as₁≁a₂∷as₂ (inj₁ (b₁≈b₂ ∷PW bs₁≈bs₂)) | inj₂ ¬a₁∼a₂ | as₁≁as₂ = inj₂ ¬a₁∷as₁∼a₂∷as₂
          where
            ¬a₁∷as₁∼a₂∷as₂ : ¬ ((a₁ ∷ as₁) ∼†A (a₂ ∷ as₂))
            ¬a₁∷as₁∼a₂∷as₂ (ObjectSpace.HeadEqual a₁≈a₂ as₁∼as₂) = ¬a₁∼a₂ $ CoherentSpace.≈→∼ A a₁≈a₂
            ¬a₁∷as₁∼a₂∷as₂ (ObjectSpace.NotHeadEqual ¬a₁≈a₂ a₁∼a₂) = ¬a₁∼a₂ a₁∼a₂
        b₁∷bs₁≁b₂∷bs₂→a₁∷as₁≁a₂∷as₂ (inj₁ (b₁≈b₂ ∷PW bs₁≈bs₂)) | inj₁ a₁≈a₂ | inj₂ ¬as₁∼as₂ = inj₂ ¬a₁∷as₁∼a₂∷as₂
          where
            ¬a₁∷as₁∼a₂∷as₂ : ¬ ((a₁ ∷ as₁) ∼†A (a₂ ∷ as₂))
            ¬a₁∷as₁∼a₂∷as₂ (ObjectSpace.HeadEqual a₁≈a₂ as₁∼as₂) = ¬as₁∼as₂ as₁∼as₂
            ¬a₁∷as₁∼a₂∷as₂ (ObjectSpace.NotHeadEqual ¬a₁≈a₂ a₁∼a₂) = ¬a₁≈a₂ a₁≈a₂
        b₁∷bs₁≁b₂∷bs₂→a₁∷as₁≁a₂∷as₂ (inj₂ ¬b₁∷bs₁∼b₂∷bs₂) = inj₂ ¬a₁∷as₁∼a₂∷as₂
          where
            ¬a₁∷as₁∼a₂∷as₂ : ¬ ((a₁ ∷ as₁) ∼†A (a₂ ∷ as₂))
            ¬a₁∷as₁∼a₂∷as₂ a₁∷as₁∼a₂∷as₂ = ¬b₁∷bs₁∼b₂∷bs₂ (a₁∷as₁∼a₂∷as₂→b₁∷bs₁∼b₂∷bs₂ a₁∷as₁∼a₂∷as₂)
        --]]]
    --]]]

    resp-≈ : pred Respects _≈|FA⇒ₗFB|_
    --[[[
    resp-≈ {.[] , .[]} {.[] , .[]} (PW.[] , PW.[]) PW.[] = PW.[]
    resp-≈ {a₁ ∷ as₁ , b₁ ∷ bs₁} {a₂ ∷ as₂ , b₂ ∷ bs₂} (a₁≈a₂ ∷PW as₁≈as₂ , b₁≈b₂ ∷PW bs₁≈bs₂) (a₁,b₁∈f ∷PW as₁,bs₁∈pred) = a₂,b₂∈f ∷PW as₂,bs₂∈pred
      where
        a₂,b₂∈f : (a₂ , b₂) ∈ pred-f
        a₂,b₂∈f = resp-≈-f (a₁≈a₂ , b₁≈b₂) a₁,b₁∈f

        as₂,bs₂∈pred : (as₂ , bs₂) ∈ pred
        as₂,bs₂∈pred = resp-≈ (as₁≈as₂ , bs₁≈bs₂) as₁,bs₁∈pred
    --]]]

identity : {A : CoherentSpace'} → CohL' [ F₁ (id {A}) ≈ id {F₀ A} ]
identity = (λ z → z) , (λ z → z)

homomorphism : ∀ {X Y Z : CoherentSpace'} {f : CohL' [ X ,, Y ]} {g : CohL' [ Y ,, Z ]} → [ F₀ X ⇒ F₀ Z ]⟨  F₁ CohL'[ g ∘ f ] ≈ CohL'[ (F₁ g) ∘ (F₁ f) ] ⟩
homomorphism {X} {Y} {Z} {f} {g} = left⊆right , right⊆left
  where
    open _⇒'_ 

    left : CohL' [ F₀ X ,, F₀ Z ]
    left = F₁ CohL'[ g ∘ f ]

    right : CohL' [ F₀ X ,, F₀ Z ]
    right = CohL'[ (F₁ g) ∘ (F₁ f) ]

    left⊆right : pred left ⊆ pred right
    left⊆right {[] , []} []PW = [] , []PW , []PW 
    left⊆right {(x ∷ xs , z ∷ zs)} (x,z∈g∘f ∷PW rest) with xs,zs∈right 
      where
        xs,zs∈right : (xs , zs) ∈ pred right
        xs,zs∈right = left⊆right rest
    left⊆right {x ∷ xs , z ∷ zs} ((y , (x,y∈f , y,z∈g)) ∷PW rest) | ys , (xs,ys∈†f , ys,zs∈†g) = (y ∷ ys) , (x,y∈f ∷PW xs,ys∈†f) , (y,z∈g ∷PW ys,zs∈†g)

    right⊆left : pred right ⊆ pred left
    right⊆left {[] , []} ([] , []PW , []PW) = []PW
    right⊆left {x ∷ xs , z ∷ zs} (y ∷ ys , x,y∈f ∷PW xs,ys∈†f , y,z∈g ∷PW ys,zs∈†g) = (y , x,y∈f , y,z∈g) ∷PW (right⊆left {xs , zs} (ys , xs,ys∈†f , ys,zs∈†g))

F-resp-≈ : ∀ {A B : CoherentSpace'} {f g : CohL' [ A ,, B ]} → CohL' [ f ≈ g ] → CohL' [ F₁ f ≈ F₁ g ] 
F-resp-≈ {A} {B} {f} {g} (f⊆g , g⊆f) = †f⊆†g , †g⊆†f
  where
    open _⇒'_

    †f⊆†g : pred (F₁ f) ⊆ pred (F₁ g)
    †f⊆†g {.[] , .[]} []PW = []PW
    †f⊆†g {a ∷ as , b ∷ bs} (a,b∈f ∷PW as,bs∈†f) = (f⊆g a,b∈f) ∷PW (†f⊆†g as,bs∈†f)

    †g⊆†f : pred (F₁ g) ⊆ pred (F₁ f)
    †g⊆†f {.[] , .[]} []PW = []PW
    †g⊆†f {a ∷ as , b ∷ bs} (a,b∈g ∷PW as,bs∈†g) = (g⊆f a,b∈g) ∷PW (†g⊆†f as,bs∈†g)


†_ : Functor CohL' CohL'
†_ = record 
  { F₀ = F₀ 
  ; F₁ = F₁
  ; identity = λ {A} → identity {A}
  ; homomorphism = λ {X} {Y} {Z} {f} {g} → homomorphism {X} {Y} {Z} {f} {g}
  ; F-resp-≈ = λ {A} {B} {f} {g} → F-resp-≈ {A} {B} {f} {g}
  }
