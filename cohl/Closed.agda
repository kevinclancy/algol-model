{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

module Closed {c : Level} where


open import Categories.Category
open import Categories.Category.Product
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Functor.Bifunctor using (appˡ ; Bifunctor)
open import CoherentSpace using (CohL ; CoherentSpace ; _⇒'_ ; _⇒ₗ_)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Adjoint using (_⊣_)
open import Lolli using (⊸ ; _⊸₀_ ; _⊸₁_)
open import Tensor using (⊗ ; _⊗₀_ ; _⊗₁_)
open import Monoidal {c} using (monoidal)

private
  CohL' = CohL {c}
  CoherentSpace' = Category.Obj CohL'
  open Category CohL' using (Obj ; _⇒_ )
  open Category (Product CohL' CohL') renaming (Obj to Obj² ; _⇒_ to _⇒²_)
  open Monoidal monoidal using (-⊗_)

module _ {X : Obj} where

  _⊗X⊣X⊸_ : (-⊗ X) ⊣ (appˡ ⊸ X)
  _⊗X⊣X⊸_ = record { unit = unit ; counit = counit ; zig = λ {A} → zig {A} ; zag = λ {A} → zag {A} }
    where
      unit : NaturalTransformation Categories.Functor.id (appˡ ⊸ X ∘F (-⊗ X)) 
      unit = record { η = {!!} ; commute = {!!} ; sym-commute = {!!} }

      counit : NaturalTransformation ((-⊗ X) ∘F appˡ ⊸ X) Categories.Functor.id
      counit = record { η = ? ; commute = ? ; sym-commute = ? }

      zig : {A : Obj} → CohL' [ CohL' [ NaturalTransformation.η counit (A ⊗₀ X) ∘ Functor.F₁ (-⊗ X) (NaturalTransformation.η unit A) ] ≈ Category.id CohL' {A ⊗₀ X} ]
      zig {A} = {!!}

      zag : {A : Obj} → CohL' [ CohL' [ Functor.F₁ (appˡ ⊸ X) (NaturalTransformation.η counit A) ∘ NaturalTransformation.η unit (Functor.F₀ (appˡ ⊸ X) A) ] ≈ Category.id CohL' {X ⊸₀ A} ]
      zag {A} = {!!}

closed : Closed monoidal
closed = record
  { [-,-]   = ⊸
  ; adjoint = λ {X} → _⊗X⊣X⊸_ {X}
  ; mate = {!!}
  }
    
