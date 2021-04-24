{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

module Symmetric {c : Level} where

open import Function using (_$_)

open import Data.Product
open import Data.Sum
open import Relation.Unary using (Pred ; _⊆_ ; _∈_)
open import Relation.Binary using (IsEquivalence ; _Respects_)
open import Relation.Nullary using (¬_)

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor using (flip-bifunctor)
open import Categories.Morphism
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (associator)

open import CoherentSpace using (CohL ; CoherentSpace ; _⇒'_ ; _⇒ₗ_)
open import Monoidal {c}
open import Tensor {c}
open import Braiding {c}


private
  CohL' = CohL {c}
  CohL'×CohL' = Product CohL' CohL'

  open Category CohL' using (Obj ; _⇒_ ; _∘_ ; id)
  open Category CohL'×CohL' renaming (Obj to Obj² ; _⇒_ to _⇒²_ ; _∘_ to _∘²_ ; id to id²)

  η⇒ = NaturalTransformation.η (NaturalIsomorphism.F⇒G braiding)

  module _ {X Y : Obj} where
    private
      open _⇒'_
      open Commutation CohL'

      ≈X-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence X)
      ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
      ≈Y-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence Y)
      ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y)

    commutative : [ (X ⊗₀ Y) ⇒ (X ⊗₀ Y) ]⟨ (η⇒ $ Y , X) ∘ (η⇒ $ X , Y) ≈ id {X ⊗₀ Y} ⟩
    commutative = l⊆r , r⊆l
      where
        l⊆r : pred ((η⇒ $ Y , X) ∘ (η⇒ $ X , Y)) ⊆ pred (id {X ⊗₀ Y})
        l⊆r {(x , y) , (x'' , y'')} ((y' , x') , (x≈x' , y≈y') , (y'≈y'' , x'≈x'')) 
            = ≈X-trans x≈x' x'≈x'' , ≈Y-trans y≈y' y'≈y''
        
        r⊆l : pred (id {X ⊗₀ Y}) ⊆ pred ((η⇒ $ Y , X) ∘ (η⇒ $ X , Y))
        r⊆l {(x , y) , (x' , y')} (x≈x' , y≈y') = (y , x) , (≈X-refl , ≈Y-refl) , (y≈y' , x≈x') 
        
  module _ {X Y Z : Obj} where
    private
      open _⇒'_
      open Commutation CohL'
      open import Categories.Category.Monoidal
      open Monoidal monoidal hiding (_⊗₀_ ; _⊗₁_)

      _≈X_ = CoherentSpace._≈_ X
      _≈Y_ = CoherentSpace._≈_ Y
      _≈Z_ = CoherentSpace._≈_ Z

      ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
      ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y)
      ≈Z-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Z)      

    a : ((X ⊗₀ Y) ⊗₀ Z) ⇒ (Y ⊗₀ (Z ⊗₀ X))
    a = (η⇒ $ X , Y) ⊗₁ (id {Z})     ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
        associator.from {Y} {X} {Z}  ⇒⟨ Y ⊗₀ (X ⊗₀ Z) ⟩
        (id {Y}) ⊗₁ (η⇒ $ X , Z)

    b : ((X ⊗₀ Y) ⊗₀ Z) ⇒ (Y ⊗₀ (Z ⊗₀ X))
    b = associator.from {X} {Y} {Z}  ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⟩
        (η⇒ $ X , Y ⊗₀ Z)            ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
        associator.from {Y} {Z} {X}

    hexagon : CohL' [ a ≈ b ]
    hexagon = a⊆b , b⊆a          
      where
        a⊆b : pred a ⊆ pred b
        --[[[
        a⊆b {((x₀ , y₀) , z₀) , (y₃ , (z₃ , x₃))} 
            ((y₂ , (x₂ , z₂)) , (((y₁ , x₁) , z₁) , ((x₀≈x₁ , y₀≈y₁) , z₀≈z₁) , (y₁≈y₂ , (x₁≈x₂ , z₁≈z₂))) , (y₂≈y₃ , x₂≈x₃ , z₂≈z₃)) 
            = ((y₀ , z₀) , x₀) , ((x₀ , (y₀ , z₀)) , (≈X-refl , (≈Y-refl , ≈Z-refl)) , (≈X-refl , (≈Y-refl , ≈Z-refl))) , (y₀≈y₃ , (z₀≈z₃ , x₀≈x₃))
          where
            z₀≈z₃ : z₀ ≈Z z₃
            z₀≈z₃ = begin 
                z₀ ≈⟨ z₀≈z₁ ⟩
                z₁ ≈⟨ z₁≈z₂ ⟩
                z₂ ≈⟨ z₂≈z₃ ⟩
                z₃
              ∎
              where
                import Relation.Binary.Reasoning.Setoid as SetR
                open SetR (CoherentSpace.setoid Z)

            y₀≈y₃ : y₀ ≈Y y₃
            y₀≈y₃ = begin 
                y₀ ≈⟨ y₀≈y₁ ⟩
                y₁ ≈⟨ y₁≈y₂ ⟩
                y₂ ≈⟨ y₂≈y₃ ⟩
                y₃
              ∎
              where
                import Relation.Binary.Reasoning.Setoid as SetR
                open SetR (CoherentSpace.setoid Y)

            x₀≈x₃ : x₀ ≈X x₃
            x₀≈x₃ = begin 
                x₀ ≈⟨ x₀≈x₁ ⟩
                x₁ ≈⟨ x₁≈x₂ ⟩
                x₂ ≈⟨ x₂≈x₃ ⟩
                x₃
              ∎
              where
                import Relation.Binary.Reasoning.Setoid as SetR
                open SetR (CoherentSpace.setoid X)
        --]]]

        b⊆a : pred b ⊆ pred a
        --[[[
        b⊆a {((x₀ , y₀) , z₀) , (y₃ , (z₃ , x₃))} 
            (((y₂ , z₂) , x₂) , ((x₁ , (y₁ , z₁)) , (x₀≈x₁ , (y₀≈y₁ , z₀≈z₁)) , (x₁≈x₂ , y₁≈y₂ , z₁≈z₂)) , (y₂≈y₃ , (z₂≈z₃ , x₂≈x₃))) 
            = (y₀ , (x₀ , z₀)) , (((y₀ , x₀) , z₀) , ((≈X-refl , ≈Y-refl) , ≈Z-refl) , (≈Y-refl , (≈X-refl , ≈Z-refl))) , (y₀≈y₃ , (x₀≈x₃ , z₀≈z₃))
            where
              z₀≈z₃ : z₀ ≈Z z₃
              z₀≈z₃ = begin 
                  z₀ ≈⟨ z₀≈z₁ ⟩
                  z₁ ≈⟨ z₁≈z₂ ⟩
                  z₂ ≈⟨ z₂≈z₃ ⟩
                  z₃
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid Z)

              y₀≈y₃ : y₀ ≈Y y₃
              y₀≈y₃ = begin 
                  y₀ ≈⟨ y₀≈y₁ ⟩
                  y₁ ≈⟨ y₁≈y₂ ⟩
                  y₂ ≈⟨ y₂≈y₃ ⟩
                  y₃
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid Y)

              x₀≈x₃ : x₀ ≈X x₃
              x₀≈x₃ = begin 
                  x₀ ≈⟨ x₀≈x₁ ⟩
                  x₁ ≈⟨ x₁≈x₂ ⟩
                  x₂ ≈⟨ x₂≈x₃ ⟩
                  x₃
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid X)
        --]]]

symmetric : Symmetric monoidal
symmetric = symmetricHelper monoidal (record { braiding = braiding
                                               ; commutative = λ {X} {Y} → commutative {Y} {X} 
                                               ; hexagon = λ {X} {Y} {Z} → hexagon {X} {Y} {Z} })
