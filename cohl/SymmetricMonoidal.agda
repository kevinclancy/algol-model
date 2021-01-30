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
      
    monoidal : Monoidal CohL'
    monoidal = record
      { ⊗ = ⊗
      ; unit = unit
      ; unitorˡ = unitorˡ
      ; unitorʳ = unitorʳ
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
        open import Tensor {c}
        open import Unit {c}
