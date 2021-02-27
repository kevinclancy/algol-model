{-# OPTIONS --without-K  --allow-unsolved-metas #-}

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
open import Categories.Morphism

open import CoherentSpace


SMCC-CohL : ∀ {c} → SymmetricMonoidalCategory _ _ _
SMCC-CohL {c} = record
  { U = CohL {c} {c} 
  ; monoidal = monoidal
  ; symmetric = {!!}
  }
  where
    CohL' = CohL {c} {c}
    open Category CohL' using (Obj)
    _∣_⇒_⇒_[_∘_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y Z : Category.Obj C) → (g : C [ Y , Z ]) → (f : C [ X , Y ]) → C [ X , Z ]
    C ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ C g f) 

    _∣_⇒_[_≈_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y : Category.Obj C) → (g : C [ X , Y ]) → (f : C [ X , Y ]) → Set _
    C ∣ X ⇒ Y [ g ≈ f ] = (Category._≈_ C g f) 
      
    monoidal : Monoidal CohL'
    monoidal = record
      { ⊗ = ⊗
      ; unit = unit
      ; unitorˡ = λ {X} → unitorˡ {X}
      ; unitorʳ = λ {Y} → unitorʳ {Y}
      ; associator = λ {X} {Y} {Z} → associator {X} {Y} {Z}
      ; unitorˡ-commute-from = {!λ {X} {Y} {f} → unitorˡ-commute-from {X} {Y} {f}!}
      ; unitorˡ-commute-to = {!!}
      ; unitorʳ-commute-from = {!!}
      ; unitorʳ-commute-to = {!!}
      ; assoc-commute-from = {!!}
      ; assoc-commute-to = {!!}
      ; triangle = {!!}
      ; pentagon = {!!}
      }
      where
        open import Tensor {c}
        open import Unit {c}
        open import Associator {c}

