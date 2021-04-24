{-# OPTIONS --without-K  --allow-unsolved-metas #-}

open import Level

module SymmetricMonoidal {c : Level} where

open import Categories.Category.Monoidal.Structure using (SymmetricMonoidalCategory)
open import CoherentSpace using (CohL)

open import Monoidal {c}
open import Symmetric {c}

SMCC-CohL : SymmetricMonoidalCategory _ _ _
SMCC-CohL = record
  { U = CohL {c} 
  ; monoidal = monoidal
  ; symmetric = symmetric
  }
