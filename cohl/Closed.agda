{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

module Closed {c : Level} where

open import Function using (_$_)

open import Data.Product
open import Relation.Unary using (Pred ; _⊆_ ; _∈_)
open import Relation.Binary using (IsEquivalence)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal.Closed
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor using (flip-bifunctor ; Bifunctor)
open import Categories.Morphism
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (associator)

open import CoherentSpace using (CohL ; CoherentSpace ; _⇒'_ ; _⇒ₗ_)
open import Monoidal {c}

private
  CohL' = CohL {c}
  open Category CohL' using (Obj ; _⇒_)
  open Category (Product CohL' CohL') renaming (Obj to Obj² ; _⇒_ to _⇒²_)

  _⊸₀_ : Obj -> Obj -> Obj
  X ⊸₀ Y = X ⇒ₗ Y

  _⊸₁_ : {(W , X) : Obj²} → {(Y , Z) : Obj²} → ((f , g) : (X ⇒ W) × (Y ⇒ Z)) → (W ⊸₀ Y) ⇒ (X ⊸₀ Z) 
  _⊸₁_ {W , X} {Y , Z} (f , g) = {!!}
  
  [-,-] : Bifunctor (Category.op CohL') CohL' CohL'
  [-,-] = record 
    { F₀ = λ (X , Y) → (X ⊸₀ Y)
    ; F₁ = _⊸₁_ 
    ; identity = {!!}
    ; homomorphism = {!!}
    ; F-resp-≈ = {!!} 
    }
  
closed : Closed monoidal
closed = record
  { [-,-]   = {!!} 
  ; adjoint = {!!}
  ; mate = {!!}
  }
    
