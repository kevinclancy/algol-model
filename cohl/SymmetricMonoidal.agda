{-# OPTIONS --without-K  --allow-unsolved-metas #-}


open import Level

module SymmetricMonoidal {c : Level} where

open import Function using (_$_)
open import Data.Product
open import Data.Sum hiding ([_,_])
open import Data.Empty

open import Relation.Binary using 
  (Rel ; _Respectsˡ_ ; Symmetric ; Transitive ; Reflexive ; IsEquivalence ; 
   _Respects_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Unary using (_⊆_)
open import Relation.Unary.Properties using (⊆-refl)
open import Relation.Nullary

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Structure using (SymmetricMonoidalCategory)
open import Categories.Morphism

open import CoherentSpace using (CohL ; CoherentSpace)

SMCC-CohL : SymmetricMonoidalCategory _ _ _
SMCC-CohL = record
  { U = CohL {c} {c} 
  ; monoidal = monoidal
  ; symmetric = {!!}
  }
  where
    CohL' = CohL {c} {c}
    open Category CohL' using (Obj ; _⇒_ ; _∘_)
    _∣_⇒_⇒_[_∘_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y Z : Category.Obj C) → (g : C [ Y , Z ]) → (f : C [ X , Y ]) → C [ X , Z ]
    C ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ C g f) 
      
    monoidal : Monoidal CohL'
    monoidal = record
      { ⊗ = ⊗
      ; unit = unit
      ; unitorˡ = λ {X} → unitorˡ {X}
      ; unitorʳ = λ {Y} → unitorʳ {Y}
      ; associator = λ {X} {Y} {Z} → associator {X} {Y} {Z}
      ; unitorˡ-commute-from = λ {X} {Y} {f} → unitorˡ-commute-from {X} {Y} {f}
      ; unitorˡ-commute-to = λ {X} {Y} {f} → unitorˡ-commute-to {X} {Y} {f}
      ; unitorʳ-commute-from = λ {X} {Y} {f} → unitorʳ-commute-from {X} {Y} {f}
      ; unitorʳ-commute-to = λ {X} {Y} {f} → unitorʳ-commute-to {X} {Y} {f}
      ; assoc-commute-from = λ {X₁} {Y₁} {f} {X₂} {Y₂} {g} {X₃} {Y₃} {h} → assoc-commute-from {X₁} {Y₁} {f} {X₂} {Y₂} {g} {X₃} {Y₃} {h} 
      ; assoc-commute-to = λ {X₁} {Y₁} {f} {X₂} {Y₂} {g} {X₃} {Y₃} {h} → assoc-commute-to {X₁} {Y₁} {f} {X₂} {Y₂} {g} {X₃} {Y₃} {h}
      ; triangle = λ {X} {Y} → triangle {X} {Y}
      ; pentagon = {!!}
      }
      where
        open import Tensor {c}
        open import Unit {c}
        open import Associator {c} 

        module _ {X Y : Obj} where
          private
    
            _⊗₀_ : Obj → Obj → Obj
            A ⊗₀ B = F₀ (A , B)

            _⊗₁_ : ∀ {X Y Z W} → X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
            _⊗₁_ {X} {Y} {Z} {W} f g = F₁ {X , Z} {Y , W} (f , g)

            open Commutation CohL'

            a-from = _≅_.from (associator {X} {unit} {Y})
            r-X = _≅_.from (unitorʳ {X})              
            l-Y = _≅_.from (unitorˡ {Y})

            id-X = Category.id CohL' {X}
            id-Y = Category.id CohL' {Y}

            idX⊗l : X ⊗₀ (unit ⊗₀ Y) ⇒ X ⊗₀ Y
            idX⊗l = F₁ {X , unit ⊗₀ Y} {X , Y} (id-X , l-Y)

            a⦂[idX⊗l] : (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y
            a⦂[idX⊗l] = CohL' ∣ (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ (unit ⊗₀ Y) ⇒ X ⊗₀ Y [ idX⊗l ∘ a-from ]

            r⊗idY : (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y
            r⊗idY = F₁ {X ⊗₀ unit , Y} {X , Y} (r-X , id-Y) 

          triangle : [ (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨ a⦂[idX⊗l] ≈ r⊗idY ⟩
          triangle = l⊆r , r⊆l
            where
              _≈X_ = CoherentSpace._≈_ X
              _≈Y_ = CoherentSpace._≈_ Y

              ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
              ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y)

              ≈X-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence X)
              ≈Y-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence Y)

              l⊆r : proj₁ a⦂[idX⊗l] ⊆ proj₁ r⊗idY
              l⊆r {((x , ∗) , y) , (x'' , y'')} 
                  ((x' , (∗ , y')) , (x≈x' , ∗≈∗ , y≈y') , (x'≈x'' , y'≈y'')) = (x≈x'' , y≈y'')
                  where
                    x≈x'' : x ≈X x''
                    x≈x'' = ≈X-trans x≈x' x'≈x''
                    
                    y≈y'' : y ≈Y y''
                    y≈y'' = ≈Y-trans y≈y' y'≈y''

              r⊆l : proj₁ r⊗idY ⊆ proj₁ a⦂[idX⊗l]
              r⊆l {((x , ∗) , y) , (x'' , y'')} 
                  (x≈x'' , y≈y'') = (x , (∗ , y)) , (≈X-refl {x} , ∗≈∗ , ≈Y-refl {y}) , (x≈x'' , y≈y'')
              
