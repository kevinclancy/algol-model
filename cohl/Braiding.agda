{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

module Braiding {c : Level} where

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

private
  CohL' = CohL {c}
  CohL'×CohL' = Product CohL' CohL'

  open Category CohL' using (Obj ; _⇒_ ; _∘_ ; id)
  open Category CohL'×CohL' renaming (Obj to Obj² ; _⇒_ to _⇒²_ ; _∘_ to _∘²_ ; id to id²)

  η⇒ : ((X , Y) : Obj²) → (X ⊗₀ Y ⇒ Y ⊗₀ X)
  --[[[
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
    --]]]

  η⇐ : ((X , Y) : Obj²) → (Y ⊗₀ X ⇒ X ⊗₀ Y)
  η⇐ (X , Y) = η⇒ (Y , X)

  module _ {X Y Z W : Obj} where
    private
      open _⇒'_
      open Commutation CohL'
      F₁' = Functor.F₁ (flip-bifunctor ⊗)  
      ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
      ≈X-sym  = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X)
      ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y)
      ≈Y-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence Y)
      ≈Z-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence Z)
      ≈Z-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Z)
      ≈W-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence W)
      ≈W-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence W)
      _≈ZW_ = CoherentSpace._≈_ (Z ⊗₀ W)

    commute⇒ : (f : (X , Y) ⇒² (Z , W)) → [ X ⊗₀ Y ⇒ W ⊗₀ Z ]⟨  η⇒ (Z , W) ∘ F₁ f ≈ F₁' f ∘ η⇒ (X , Y) ⟩ 
    commute⇒ f = l⊆r , r⊆l
      where
        l⊆r : pred (η⇒ (Z , W) ∘ F₁ f) ⊆ pred (F₁' f ∘ η⇒ (X , Y))
        l⊆r {(x , y) , (w , z)} ((z' , w') , [xy][z'w']∈f , (z'≈z , w'≈w)) = (y , x) , (≈X-refl , ≈Y-refl) , (yw∈f₂ , xz∈f₁)
          where
            xz∈f₁ : (x , z) ∈ pred (proj₁ f)
            xz∈f₁ = resp-≈ (proj₁ f) (≈X-refl , z'≈z) (proj₁ [xy][z'w']∈f)

            yw∈f₂ : (y , w) ∈ pred (proj₂ f)
            yw∈f₂ = resp-≈ (proj₂ f) (≈Y-refl , w'≈w) (proj₂ [xy][z'w']∈f)

        r⊆l : pred (F₁' f ∘ η⇒ (X , Y)) ⊆ pred (η⇒ (Z , W) ∘ F₁ f)
        r⊆l {((x , y) , (w , z))} ((y' , x') , (x≈x' , y≈y') , [x'y'][wz]∈f) = (z , w) , (xz∈f₁ , yw∈f₂) , (≈Z-refl , ≈W-refl)
          where
            xz∈f₁ : (x , z) ∈ pred (proj₁ f)
            xz∈f₁ = resp-≈ (proj₁ f) (≈X-sym x≈x' , ≈Z-refl) (proj₂ [x'y'][wz]∈f)

            yw∈f₂ : (y , w) ∈ pred (proj₂ f)
            yw∈f₂ = resp-≈ (proj₂ f) (≈Y-sym y≈y' , ≈W-refl) (proj₁ [x'y'][wz]∈f)

    commute⇐ : (f : (X , Y) ⇒² (Z , W)) → [ Y ⊗₀ X ⇒ Z ⊗₀ W ]⟨  η⇐ (Z , W) ∘ F₁' f ≈ F₁ f ∘ η⇐ (X , Y) ⟩ 
    commute⇐ f = l⊆r , r⊆l
      where
        l⊆r : pred (η⇐ (Z , W) ∘ F₁' f) ⊆ pred (F₁ f ∘ η⇐ (X , Y))
        l⊆r {(y , x) , (z , w)} ((w' , z') , [yx][w'z']∈f , (z'≈z , w'≈w)) = (x , y) , (≈Y-refl , ≈X-refl) , (xz∈f₁ , yw∈f₂)
          where
            xz∈f₁ : (x , z) ∈ pred (proj₁ f)
            xz∈f₁ = resp-≈ (proj₁ f) (≈X-refl , w'≈w) (proj₂ [yx][w'z']∈f)

            yw∈f₂ : (y , w) ∈ pred (proj₂ f)
            yw∈f₂ = resp-≈ (proj₂ f) (≈Y-refl , z'≈z) (proj₁ [yx][w'z']∈f)

        r⊆l : pred (F₁ f ∘ η⇐ (X , Y)) ⊆ pred (η⇐ (Z , W) ∘ F₁' f)
        r⊆l {((y , x) , (z , w))} ((x' , y') , (y≈z' , x≈x') , [x'y'][wz]∈f) = (w , z) , (yw∈f₂ , xz∈f₁) , (≈W-refl , ≈Z-refl)
          where
            xz∈f₁ : (x , z) ∈ pred (proj₁ f)
            xz∈f₁ = resp-≈ (proj₁ f) (≈X-sym x≈x' , ≈Z-refl) (proj₁ [x'y'][wz]∈f)

            yw∈f₂ : (y , w) ∈ pred (proj₂ f)
            yw∈f₂ = resp-≈ (proj₂ f) (≈Y-sym y≈z' , ≈W-refl) (proj₂ [x'y'][wz]∈f)

  F⇒G : NaturalTransformation ⊗ (flip-bifunctor ⊗)
  F⇒G = record 
    { η = η⇒
    ; commute = commute⇒ 
    ; sym-commute = λ f → (proj₂ $ commute⇒ f) , (proj₁ $ commute⇒ f) 
    }

  F⇐G : NaturalTransformation (flip-bifunctor ⊗) ⊗
  F⇐G = record 
    { η = η⇐
    ; commute = commute⇐
    ; sym-commute = λ f → (proj₂ $ commute⇐ f) , (proj₁ $ commute⇐ f) 
    }

  iso : ((X , Y) : Obj²) → Iso CohL' (η⇒ $ X , Y) (η⇐ $ X , Y)
  iso (X , Y) = record 
    { isoˡ = p , q
    ; isoʳ = r , s
    }
    where
      open _⇒'_

      ≈X-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence X)
      ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
      ≈Y-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence Y)
      ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y)

      p : pred ((η⇐ $ X , Y) ∘ (η⇒ $ X , Y)) ⊆ pred (Category.id CohL' {X ⊗₀ Y})
      p {(x , y) , (x'' , y'')} ((y' , x') , (x≈x' , y≈y') , (y'≈y'' , x'≈x'')) 
        = (≈X-trans x≈x' x'≈x'' , ≈Y-trans y≈y' y'≈y'')

      q : pred (Category.id CohL' {X ⊗₀ Y}) ⊆ pred ((η⇐ $ X , Y) ∘ (η⇒ $ X , Y))
      q {(x , y) , (x' , y')} (x≈x' , y≈y') = (y , x) , (≈X-refl , ≈Y-refl) , (y≈y' , x≈x')

      r : pred ((η⇒ $ X , Y) ∘ (η⇐ $ X , Y)) ⊆ pred (Category.id CohL' {Y ⊗₀ X})
      r {(y , x) , (y'' , x'')} ((x' , y') , (y≈y' , x≈x') , (x'≈x'' , y'≈y'')) 
        = ≈Y-trans y≈y' y'≈y'' , ≈X-trans x≈x' x'≈x''

      s : pred (Category.id CohL' {Y ⊗₀ X}) ⊆ pred ((η⇐ $ Y , X) ∘ (η⇒ $ Y , X))
      s {(y , x) , (y' , x')} (y≈y' , x≈x') = (x , y) , (≈Y-refl , ≈X-refl) , (x≈x' , y≈y')

braiding : NaturalIsomorphism ⊗ (flip-bifunctor ⊗)
braiding = record 
  { F⇒G = F⇒G
  ; F⇐G = F⇐G
  ; iso = iso
  }
