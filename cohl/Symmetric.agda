open import Level

module Symmetric {c : Level} where

open import Data.Product
open import Relation.Unary using (Pred ; _⊆_ ; _∈_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor
open import Categories.Functor.Bifunctor using (flip-bifunctor)
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism

open import CoherentSpace using (CohL ; CoherentSpace ; _⇒'_ ; _⇒ₗ_)
open import Monoidal {c}
open import Tensor {c}

private
  CohL' = CohL {c}
  CohL'×CohL' = Product CohL' CohL'

  open Category CohL' using (Obj ; _⇒_ ; _∘_ ; id)
  open Category CohL'×CohL' renaming (Obj to Obj² ; _⇒_ to _⇒²_ ; _∘_ to _∘²_ ; id to id²)

symmetric : Symmetric monoidal
symmetric = symmetricHelper monoidal (record { braiding = braiding ; commutative = {!!} ; hexagon = {!!} })
  where
    η⇒ : ((X , Y) : Obj²) → (X ⊗₀ Y ⇒ Y ⊗₀ X)
    η⇒ (X , Y) = record
      { pred = pred
      ; isPoint = isPoint
      ; resp-≈ = {!!}
      }
      where
        _≈X_ = CoherentSpace._≈_ X
        _≈Y_ = CoherentSpace._≈_ Y

        |X⊗Y⇒Y⊗X| = CoherentSpace.TokenSet (X ⊗₀ Y ⇒ₗ Y ⊗₀ X)

        pred : Pred |X⊗Y⇒Y⊗X| _
        pred ((x , y) , (y' , x')) = (x ≈X x') × (y ≈Y y')

        isPoint : CoherentSpace.isPoint (X ⊗₀ Y ⇒ₗ Y ⊗₀ X) pred 
        isPoint ((x₀ , y₀) , (y₁ , x₁)) ((x₂ , y₃) , (y₄ , x₄))  = {!!}

    F⇒G : NaturalTransformation ⊗ (flip-bifunctor ⊗)
    F⇒G = record 
      { η = η⇒
      ; commute = {!!}
      ; sym-commute = {!!}
      }

    braiding : NaturalIsomorphism ⊗ (flip-bifunctor ⊗)
    braiding = record 
      { F⇒G = {!!}
      ; F⇐G = {!!}
      ; iso = {!!}
      }
 
    -- symm′ : Categories.Category.Monoidal.Symmetric.Symmetric′ monoidal
    -- symm′ = ?
