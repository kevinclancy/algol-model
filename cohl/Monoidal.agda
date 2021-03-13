{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level

module Monoidal {c : Level} where

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

open import CoherentSpace using (CohL ; CoherentSpace ; _⇒'_)

private
  CohL' = CohL {c}
  open Category CohL' using (Obj ; _⇒_ ; _∘_ ; id)

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
  ; pentagon = λ {X} {Y} {Z} {W} → pentagon {X} {Y} {Z} {W}
  }
  where
    open import Tensor {c}
    open import Unit {c}
    open import Associator {c} 

    module _ {X Y Z W : Obj} where
      private
        open Commutation CohL'
        open _⇒'_

        α⇒ = λ {X} {Y} {Z} → _≅_.from (associator {X} {Y} {Z}) 

        left : ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ (Y ⊗₀ (Z ⊗₀ W))
        left = α⇒ {X} {Y} {Z} ⊗₁ id {W} ⇒⟨ (X ⊗₀ (Y ⊗₀ Z)) ⊗₀ W ⟩
               α⇒ {X} {Y ⊗₀ Z} {W}      ⇒⟨ X ⊗₀ ((Y ⊗₀ Z) ⊗₀ W) ⟩
               id {X} ⊗₁ α⇒ {Y} {Z} {W}

        right : ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ (Y ⊗₀ (Z ⊗₀ W))
        right = α⇒ {X ⊗₀ Y} {Z} {W} ⇒⟨ (X ⊗₀ Y) ⊗₀ (Z ⊗₀ W) ⟩
                α⇒ {X} {Y} {Z ⊗₀ W}

        _≈X_ = CoherentSpace._≈_ X
        _≈Y_ = CoherentSpace._≈_ Y
        _≈Z_ = CoherentSpace._≈_ Z
        _≈W_ = CoherentSpace._≈_ W

        ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X) 
        ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y) 
        ≈Z-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Z) 
        ≈W-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence W)

        ≈X-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence X) 
        ≈Y-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence Y) 
        ≈Z-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence Z) 
        ≈W-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence W)

      pentagon : [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ Y ⊗₀ Z ⊗₀ W ]⟨ left ≈ right ⟩
      pentagon = l⊆r , r⊆l
        where
          l⊆r : pred left ⊆ pred right
          l⊆r {(((x₀ , y₀) , z₀) , w₀) , (x₃ , (y₃ , (z₃ , w₃)))} ₀₃∈ =
            let ((x₂ , ((y₂ , z₂) , w₂)) , ₀₂∈ , (x₂≈x₃ , y₂≈y₃ , z₂≈z₃ , w₂≈w₃)) = ₀₃∈ in
            let (((x₁ , (y₁ , z₁)) , w₁)) , ₀₁∈l , (x₁≈x₂ , (y₁≈y₂ , z₁≈z₂) , w₁≈w₂) = ₀₂∈ in
            let ((x₀≈x₁ , (y₀≈y₁ , z₀≈z₁)) , w₀≈w₁) = ₀₁∈l in 
            let x₀≈x₃ : x₀ ≈X x₃
                x₀≈x₃ = ≈X-trans x₀≈x₁ (≈X-trans x₁≈x₂ x₂≈x₃)     
            in
            let y₀≈y₃ : y₀ ≈Y y₃
                y₀≈y₃ = ≈Y-trans y₀≈y₁ (≈Y-trans y₁≈y₂ y₂≈y₃)     
            in
            let z₀≈z₃ : z₀ ≈Z z₃
                z₀≈z₃ = ≈Z-trans z₀≈z₁ (≈Z-trans z₁≈z₂ z₂≈z₃)     
            in
            let w₀≈w₃ : w₀ ≈W w₃
                w₀≈w₃ = ≈W-trans w₀≈w₁ (≈W-trans w₁≈w₂ w₂≈w₃)     
            in
            ((x₀ , y₀) , (z₀ , w₀)) , 
            ((≈X-refl , ≈Y-refl) , (≈Z-refl , ≈W-refl)) , 
            x₀≈x₃ , y₀≈y₃ , z₀≈z₃ , w₀≈w₃

          r⊆l : pred right ⊆ pred left
          r⊆l {(((x₀ , y₀) , z₀) , w₀) , (x₂ , (y₂ , (z₂ , w₂)))} 
              (((x₁ , y₁) , (z₁ , w₁)) , ₀₁∈ , ₁₂∈) = 
            let ((x₀≈x₁ , y₀≈y₁) , z₀≈z₁ , w₀≈w₁) = ₀₁∈ in
            let (x₁≈x₂ , y₁≈y₂ , z₁≈z₂ , w₁≈w₂) = ₁₂∈ in
            let x₀≈x₂ : x₀ ≈X x₂
                x₀≈x₂ = ≈X-trans x₀≈x₁ x₁≈x₂     
            in
            let y₀≈y₂ : y₀ ≈Y y₂
                y₀≈y₂ = ≈Y-trans y₀≈y₁ y₁≈y₂     
            in
            let z₀≈z₂ : z₀ ≈Z z₂
                z₀≈z₂ = ≈Z-trans z₀≈z₁ z₁≈z₂     
            in
            let w₀≈w₂ : w₀ ≈W w₂
                w₀≈w₂ = ≈W-trans w₀≈w₁ w₁≈w₂     
            in
            let ∈-α∘α⊗id = ((x₀ , (y₀ , z₀)) , w₀) , 
                           ((≈X-refl , ≈Y-refl , ≈Z-refl) , ≈W-refl) ,
                           (≈X-refl , (≈Y-refl , ≈Z-refl) , ≈W-refl)
            in
            (x₀ , (y₀ , z₀) , w₀) , ∈-α∘α⊗id , (x₀≈x₂ , y₀≈y₂ , z₀≈z₂ , w₀≈w₂)

    module _ {X Y : Obj} where
      private
        open Commutation CohL'
        open _⇒'_

        a-from = _≅_.from (associator {X} {unit} {Y})
        r-X = _≅_.from (unitorʳ {X})              
        l-Y = _≅_.from (unitorˡ {Y})

        id-X = Category.id CohL' {X}
        id-Y = Category.id CohL' {Y}

        idX⊗l : X ⊗₀ (unit ⊗₀ Y) ⇒ X ⊗₀ Y
        idX⊗l = F₁ {X , unit ⊗₀ Y} {X , Y} (id-X , l-Y)

        a⦂[idX⊗l] : (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y
        a⦂[idX⊗l] = CohL' [ idX⊗l ∘ a-from ]

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

          l⊆r : pred a⦂[idX⊗l] ⊆ pred r⊗idY
          l⊆r {((x , ∗) , y) , (x'' , y'')} 
              ((x' , (∗ , y')) , (x≈x' , ∗≈∗ , y≈y') , (x'≈x'' , y'≈y'')) = (x≈x'' , y≈y'')
              where
                x≈x'' : x ≈X x''
                x≈x'' = ≈X-trans x≈x' x'≈x''

                y≈y'' : y ≈Y y''
                y≈y'' = ≈Y-trans y≈y' y'≈y''

          r⊆l : pred r⊗idY ⊆ pred a⦂[idX⊗l]
          r⊆l {((x , ∗) , y) , (x'' , y'')} 
              (x≈x'' , y≈y'') = (x , (∗ , y)) , (≈X-refl {x} , ∗≈∗ , ≈Y-refl {y}) , (x≈x'' , y≈y'')


