{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level

module ObjectFunctor2 {c : Level} where

open import Categories.Category
open import Categories.Functor.Core using (Functor)
open import CoherentSpace using (CohL ; CoherentSpace)

open import Relation.Binary.Core renaming (Rel to BinRel)
open import Relation.Binary.PropositionalEquality.Core as PE using (_≡_)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Binary.Definitions using (tri< ; tri> ; tri≈ ; _Respectsˡ_)
open import Relation.Binary using 
  (Rel ; _Respectsˡ_ ; Symmetric ; Transitive ; Reflexive ; IsEquivalence ; 
   _Respects_)

open import Data.List
open import Data.List.Relation.Binary.Pointwise using (Pointwise) renaming (_∷_ to _∷PW_)
open import Data.List.Relation.Binary.Pointwise.Properties 
  renaming (symmetric to PW-sym ; transitive to PW-trans ; refl to PW-refl)

open import Data.Product using (Σ ; Σ-syntax ; _,_ ; _×_) 
open import Data.Product.Relation.Binary.Pointwise.Dependent renaming (Pointwise to Pointwise-Σ)

private
  CohL' = CohL {c}
  CoherentSpace' = CoherentSpace c
  open Category CohL' using (_⇒_; _∘_; id)


F₀ : CoherentSpace' → CoherentSpace'
F₀ A = †A 
  where
    |A| = CoherentSpace.TokenSet A
    _∼A_ = CoherentSpace._∼_ A
    _≈A_ = CoherentSpace._≈_ A

    ≈A-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence A)
    ≈A-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence A)
    ≈A-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence A)
    ∼A-respˡ-≈A = CoherentSpace.∼-respˡ-≈ A
    ∼A-sym = CoherentSpace.∼-sym A
    ∼A-refl = CoherentSpace.∼-refl A

    †A : CoherentSpace _
    †A = record
      { TokenSet = |†A|
      ; _≈_ = _≈_
      ; _∼_ = _∼_
      ; ≈-isEquivalence = ≈-isEquivalence
      ; ∼-respˡ-≈ = ∼-respˡ-≈
      ; ≈→∼ = ≈→∼
      ; ∼-sym = ∼-sym
      ; ∼-refl = ∼-refl
      }
      where
        |†A| = List |A|
        _≈_ = Pointwise _≈A_

        data _∼_ : |†A| → |†A| → Set c where
          EmptyLeft : ∀ {r} → [] ∼ r
          EmptyRight : ∀ {l} → l ∼ []
          HeadEqual : ∀ {l l' r r'} → (l ≈A r) → (l' ∼ r') → (l ∷ l') ∼ (r ∷ r')
          NotHeadEqual : ∀ {l l' r r'} → ¬ (l ≈A r) → (l ∼A r) → (l ∷ l') ∼ (r ∷ r') 

        ≈→∼ : {a b : |†A|} → Pointwise _≈A_ a b → a ∼ b
        ≈→∼ {.[]} {.[]} Pointwise.[] = EmptyLeft
        ≈→∼ {a ∷ a'} {b ∷ b'} (a≈b ∷PW a'≈b') = HeadEqual a≈b (≈→∼ a'≈b')

        ∼-respˡ-≈ : _∼_ Respectsˡ _≈_
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

        ∼-sym : Symmetric _∼_
        ∼-sym {.[]} {y} EmptyLeft = EmptyRight
        ∼-sym {x} {.[]} EmptyRight = EmptyLeft
        ∼-sym {x ∷ x'} {y ∷ y'} (HeadEqual x≈y x'∼y') = HeadEqual (≈A-sym x≈y) (∼-sym x'∼y')
        ∼-sym {x ∷ x'} {y ∷ y'} (NotHeadEqual ¬x≈y x∼y) = NotHeadEqual ¬y≈x (∼A-sym x∼y)
          where
            ¬y≈x : ¬ (y ≈A x)
            ¬y≈x y≈x = ¬x≈y (≈A-sym y≈x)

        ∼-refl : Reflexive _∼_
        ∼-refl {[]} = EmptyLeft
        ∼-refl {x ∷ x'} = HeadEqual (≈A-refl {x}) (∼-refl {x'})
        
        ≈-isEquivalence : IsEquivalence _≈_
        ≈-isEquivalence = record 
          { sym = PW-sym ≈A-sym 
          ; trans = PW-trans ≈A-trans
          ; refl = PW-refl ≈A-refl
          }
         
