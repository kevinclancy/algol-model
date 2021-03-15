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
      ; resp-≈ = resp-≈
      }
      where
        _≈X_ = CoherentSpace._≈_ X
        _≈Y_ = CoherentSpace._≈_ Y

        |X⊗Y⇒Y⊗X| = CoherentSpace.TokenSet (X ⊗₀ Y ⇒ₗ Y ⊗₀ X)
        
        pred : Pred |X⊗Y⇒Y⊗X| _
        pred ((x , y) , (y' , x')) = (x ≈X x') × (y ≈Y y')

        isPoint : CoherentSpace.isPoint (X ⊗₀ Y ⇒ₗ Y ⊗₀ X) pred 
        --[[[
        isPoint ((x₀ , y₀) , (y₁ , x₁)) ((x₂ , y₂) , (y₃ , x₃))  
                (x₀≈x₁ , y₀≈y₁) (x₂≈x₃ , y₂≈y₃) = x₀y₀∼x₂y₂→y₁x₁∼y₃x₃ , y₁x₁≁y₃x₃→x₀y₀≁x₂y₂
          where
            _∼X⊗Y_ = CoherentSpace._∼_ (X ⊗₀ Y)
            _∼Y⊗X_ = CoherentSpace._∼_ (Y ⊗₀ X)
            _≁X⊗Y_ = CoherentSpace._≁_ (X ⊗₀ Y)
            _≁Y⊗X_ = CoherentSpace._≁_ (Y ⊗₀ X)
            _∼X_   = CoherentSpace._∼_ X
            _∼Y_   = CoherentSpace._∼_ Y

            ≈X-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence X)
            
            ∼X-respˡ-≈X = CoherentSpace.∼-respˡ-≈ X
            ∼X-respʳ-≈X = CoherentSpace.∼-respʳ-≈ X 

            ∼Y-respˡ-≈Y = CoherentSpace.∼-respˡ-≈ Y 
            ∼Y-respʳ-≈Y = CoherentSpace.∼-respʳ-≈ Y 

            x₀y₀∼x₂y₂→y₁x₁∼y₃x₃ : (x₀ , y₀) ∼X⊗Y (x₂ , y₂) → (y₁ , x₁) ∼Y⊗X (y₃ , x₃)
            x₀y₀∼x₂y₂→y₁x₁∼y₃x₃ (x₀∼x₂ , y₀∼y₂) = y₁∼y₃ , x₁∼x₃
              where
                y₁∼y₂ : y₁ ∼Y y₂
                y₁∼y₂ = ∼Y-respˡ-≈Y y₀≈y₁ y₀∼y₂

                y₁∼y₃ : y₁ ∼Y y₃
                y₁∼y₃ = ∼Y-respʳ-≈Y y₂≈y₃ y₁∼y₂

                x₁∼x₂ : x₁ ∼X x₂
                x₁∼x₂ = ∼X-respˡ-≈X x₀≈x₁ x₀∼x₂
      
                x₁∼x₃ : x₁ ∼X x₃
                x₁∼x₃ = ∼X-respʳ-≈X x₂≈x₃ x₁∼x₂

            y₁x₁≁y₃x₃→x₀y₀≁x₂y₂ : (y₁ , x₁) ≁Y⊗X (y₃ , x₃) → (x₀ , y₀) ≁X⊗Y (x₂ , y₂)
            y₁x₁≁y₃x₃→x₀y₀≁x₂y₂ (inj₁ (y₁≈y₃ , x₁≈x₃)) = inj₁ (x₀≈x₂ , y₀≈y₂)
              where
                x₀≈x₂ : x₀ ≈X x₂
                x₀≈x₂ = begin
                    x₀  ≈⟨ x₀≈x₁ ⟩
                    x₁  ≈⟨ x₁≈x₃ ⟩
                    x₃ ≈˘⟨ x₂≈x₃ ⟩
                    x₂
                  ∎ 
                  where
                    import Relation.Binary.Reasoning.Setoid as SetR
                    open SetR (CoherentSpace.setoid X)

                y₀≈y₂ : y₀ ≈Y y₂
                y₀≈y₂ = begin
                    y₀  ≈⟨ y₀≈y₁ ⟩
                    y₁  ≈⟨ y₁≈y₃ ⟩
                    y₃ ≈˘⟨ y₂≈y₃ ⟩
                    y₂
                  ∎ 
                  where
                    import Relation.Binary.Reasoning.Setoid as SetR
                    open SetR (CoherentSpace.setoid Y)
            y₁x₁≁y₃x₃→x₀y₀≁x₂y₂ (inj₂ ¬y₁x₁∼y₃x₃) = inj₂ ¬x₀y₀∼x₂y₂
              where
                ¬x₀y₀∼x₂y₂ : ¬ (x₀ , y₀) ∼X⊗Y (x₂ , y₂)
                ¬x₀y₀∼x₂y₂ (x₀∼x₂ , y₀∼y₂) = ¬y₁x₁∼y₃x₃ (y₁∼y₃ , x₁∼x₃)
                  where
                    y₁∼y₂ : y₁ ∼Y y₂
                    y₁∼y₂ = ∼Y-respˡ-≈Y y₀≈y₁ y₀∼y₂
      
                    y₁∼y₃ : y₁ ∼Y y₃
                    y₁∼y₃ = ∼Y-respʳ-≈Y y₂≈y₃ y₁∼y₂

                    x₁∼x₂ : x₁ ∼X x₂
                    x₁∼x₂ = ∼X-respˡ-≈X x₀≈x₁ x₀∼x₂
      
                    x₁∼x₃ : x₁ ∼X x₃
                    x₁∼x₃ = ∼X-respʳ-≈X x₂≈x₃ x₁∼x₂
          --]]]

        resp-≈ : pred Respects (CoherentSpace._≈_ $ X ⊗₀ Y ⇒ₗ Y ⊗₀ X) 
        --[[[
        resp-≈ {(x₀ , y₀) , (y₁ , x₁)} {(x₂ , y₂) , (y₃ , x₃)} 
               ((x₀≈x₂ , y₀≈y₂) , (y₁≈y₃ , x₁≈x₃)) (x₀≈x₁ , y₀≈y₁) = x₂≈x₃ , y₂≈y₃
          where
            x₂≈x₃ : x₂ ≈X x₃
            x₂≈x₃ = begin 
                x₂ ≈˘⟨ x₀≈x₂ ⟩
                x₀  ≈⟨ x₀≈x₁ ⟩
                x₁  ≈⟨ x₁≈x₃ ⟩
                x₃
              ∎ 
              where
                import Relation.Binary.Reasoning.Setoid as SetR
                open SetR (CoherentSpace.setoid X)

            y₂≈y₃ : y₂ ≈Y y₃
            y₂≈y₃ = begin 
                y₂ ≈˘⟨ y₀≈y₂ ⟩
                y₀  ≈⟨ y₀≈y₁ ⟩
                y₁  ≈⟨ y₁≈y₃ ⟩
                y₃
              ∎ 
              where
                import Relation.Binary.Reasoning.Setoid as SetR
                open SetR (CoherentSpace.setoid Y)
        --]]]

    F⇒G : NaturalTransformation ⊗ (flip-bifunctor ⊗)
    F⇒G = record 
      { η = η⇒
      ; commute = {!!}
      ; sym-commute = {!!}
      }

    braiding : NaturalIsomorphism ⊗ (flip-bifunctor ⊗)
    braiding = record 
      { F⇒G = F⇒G
      ; F⇐G = {!!}
      ; iso = {!!}
      }
 
    -- symm′ : Categories.Category.Monoidal.Symmetric.Symmetric′ monoidal
    -- symm′ = ?
