{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

module Lolli {c : Level} where

open import Function using (_$_)

open import Data.Product
open import Data.Sum
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Unary using (Pred ; _⊆_ ; _∈_)
open import Relation.Binary using (IsEquivalence ; _Respects_)
open import Relation.Nullary using (yes ; no ; ¬_)

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
  CoherentSpace' = Category.Obj CohL'
  open Category CohL' using (Obj ; _⇒_)
  open Category (Product CohL' CohL') renaming (Obj to Obj² ; _⇒_ to _⇒²_)

  -- open Category (Category.op CohL') renaming (Obj to CoherentSpace'-op)

_⊸₀_ : Obj -> Obj -> Obj
X ⊸₀ Y = X ⇒ₗ Y

_⊸₁_ : {(W , X) : Obj²} → {(Y , Z) : Obj²} → (X ⇒ W) → (Y ⇒ Z) → (W ⊸₀ Y) ⇒ (X ⊸₀ Z)
_⊸₁_ {W , X} {Y , Z} f g = record { pred = p ; isPoint = q ; resp-≈ = r }
  where
    --[[[
    open _⇒'_

    _≁W_ = CoherentSpace._≁_ W
    _≁X_ = CoherentSpace._≁_ X
    _≁Y_ = CoherentSpace._≁_ Y
    _≁Z_ = CoherentSpace._≁_ Z

    _∼W_ = CoherentSpace._∼_ W
    _∼X_ = CoherentSpace._∼_ X
    _∼Y_ = CoherentSpace._∼_ Y
    _∼Z_ = CoherentSpace._∼_ Z

    _≈W_ = CoherentSpace._≈_ W
    _≈X_ = CoherentSpace._≈_ X
    _≈Y_ = CoherentSpace._≈_ Y
    _≈Z_ = CoherentSpace._≈_ Z

    _≁W⊸Y_ = CoherentSpace._≁_ (W ⊸₀ Y)
    _≁X⊸Z_ = CoherentSpace._≁_ (X ⊸₀ Z)

    _∼W⊸Y_ = CoherentSpace._∼_ (W ⊸₀ Y)
    _∼X⊸Z_ = CoherentSpace._∼_ (X ⊸₀ Z)

    p : Pred (CoherentSpace.TokenSet $ (W ⊸₀ Y) ⇒ₗ (X ⊸₀ Z)) c
    p ((w , y) , (x , z)) = ((x , w) ∈ pred f) × ((y , z) ∈ pred g)

    q : CoherentSpace.isPoint ((W ⊸₀ Y) ⇒ₗ (X ⊸₀ Z)) p
    q ((w₀ , y₀) , (x₀ , z₀)) ((w₁ , y₁) , (x₁ , z₁)) (x₀w₀∈f , y₀z₀∈g) (x₁w₁∈f , y₁z₁∈g)
      = w₀y₀∼w₁y₁→x₀z₀∼x₁z₁ , x₀z₀≁x₁z₁→w₀y₀≁w₁y₁
      where
        --[[[
        x₀∼x₁→w₀∼w₁ = proj₁ (isPoint f (x₀ , w₀) (x₁ , w₁) x₀w₀∈f x₁w₁∈f)
        w₀≁w₁→x₀≁x₁ = proj₂ (isPoint f (x₀ , w₀) (x₁ , w₁) x₀w₀∈f x₁w₁∈f)

        y₀∼y₁→z₀∼z₁ = proj₁ (isPoint g (y₀ , z₀) (y₁ , z₁) y₀z₀∈g y₁z₁∈g)
        z₀≁z₁→y₀≁y₁ = proj₂ (isPoint g (y₀ , z₀) (y₁ , z₁) y₀z₀∈g y₁z₁∈g)

        w₀y₀∼w₁y₁→x₀z₀∼x₁z₁ : (w₀ , y₀) ∼W⊸Y (w₁ , y₁) → (x₀ , z₀) ∼X⊸Z (x₁ , z₁)
        --[[[
        w₀y₀∼w₁y₁→x₀z₀∼x₁z₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) = x₀∼x₁→z₀∼z₁ , z₀≁z₁→x₀≁x₁
          where
            x₀∼x₁→z₀∼z₁ : x₀ ∼X x₁ → z₀ ∼Z z₁
            x₀∼x₁→z₀∼z₁ x₀∼x₁ = z₀∼z₁
              where
                w₀∼w₁ : w₀ ∼W w₁
                w₀∼w₁ = x₀∼x₁→w₀∼w₁ x₀∼x₁

                y₀∼y₁ : y₀ ∼Y y₁
                y₀∼y₁ = w₀∼w₁→y₀∼y₁ w₀∼w₁

                z₀∼z₁ : z₀ ∼Z z₁
                z₀∼z₁ = y₀∼y₁→z₀∼z₁ y₀∼y₁

            z₀≁z₁→x₀≁x₁ : z₀ ≁Z z₁ → x₀ ≁X x₁
            z₀≁z₁→x₀≁x₁ z₀≁z₁ = x₀≁x₁
              where
                y₀≁y₁ : y₀ ≁Y y₁
                y₀≁y₁ = z₀≁z₁→y₀≁y₁ z₀≁z₁

                w₀≁w₁ : w₀ ≁W w₁
                w₀≁w₁ = y₀≁y₁→w₀≁w₁ y₀≁y₁

                x₀≁x₁ : x₀ ≁X x₁
                x₀≁x₁ = w₀≁w₁→x₀≁x₁ w₀≁w₁
        --]]]

        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ : (x₀ , z₀) ≁X⊸Z (x₁ , z₁) → (w₀ , y₀) ≁W⊸Y (w₁ , y₁)
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₁ (x₀≈x₁ , z₀≈z₁)) with y₀≁y₁
          where
            y₀≁y₁ : y₀ ≁Y y₁
            y₀≁y₁ = z₀≁z₁→y₀≁y₁ (inj₁ z₀≈z₁)
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₁ (x₀≈x₁ , z₀≈z₁)) | inj₁ y₀≈y₁ with CoherentSpace.≈-decidable W w₀ w₁
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₁ (x₀≈x₁ , z₀≈z₁)) | inj₁ y₀≈y₁ | yes w₀≈w₁ = inj₁ (w₀≈w₁ , y₀≈y₁)
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₁ (x₀≈x₁ , z₀≈z₁)) | inj₁ y₀≈y₁ | no ¬w₀≈w₁ = inj₂ ¬w₀y₀∼w₁y₁ -- I need ⊥-elim here
          where
            --[[[
            ≈X→∼X = CoherentSpace.≈→∼ X

            w₀∼w₁ : w₀ ∼W w₁
            w₀∼w₁ = x₀∼x₁→w₀∼w₁ (≈X→∼X x₀≈x₁)

            ¬w₀y₀∼w₁y₁ : ¬ (w₀ , y₀) ∼W⊸Y (w₁ , y₁)
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) with w₀≁w₁
              where
                w₀≁w₁ : w₀ ≁W w₁
                w₀≁w₁ = y₀≁y₁→w₀≁w₁ (inj₁ y₀≈y₁)
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) | inj₁ w₀≈w₁ = ¬w₀≈w₁ w₀≈w₁
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) | inj₂ ¬w₀∼w₁ = ¬w₀∼w₁ w₀∼w₁
            --]]]
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₁ (x₀≈x₁ , z₀≈z₁)) | inj₂ ¬y₀∼y₁ with CoherentSpace.≈-decidable W w₀ w₁
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₁ (x₀≈x₁ , z₀≈z₁)) | inj₂ ¬y₀∼y₁ | yes w₀≈w₁ = inj₂ ¬w₀y₀∼w₁y₁
          where
            --[[[
            ≈W→∼W = CoherentSpace.≈→∼ W

            ¬w₀y₀∼w₁y₁ : ¬ (w₀ , y₀) ∼W⊸Y (w₁ , y₁)
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) = ¬y₀∼y₁ y₀∼y₁
              where
                y₀∼y₁ : y₀ ∼Y y₁
                y₀∼y₁ = w₀∼w₁→y₀∼y₁ (≈W→∼W w₀≈w₁)
            --]]]
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₁ (x₀≈x₁ , z₀≈z₁)) | inj₂ ¬y₀∼y₁ | no ¬w₀≈w₁ = inj₂ ¬w₀y₀∼w₁y₁
          where
            --[[[
            ≈X→∼X = CoherentSpace.≈→∼ X

            w₀∼w₁ : w₀ ∼W w₁
            w₀∼w₁ = x₀∼x₁→w₀∼w₁ (≈X→∼X x₀≈x₁)

            y₀≁y₁ : y₀ ≁Y y₁
            y₀≁y₁ = inj₂ ¬y₀∼y₁

            ¬w₀y₀∼w₁y₁ : ¬ (w₀ , y₀) ∼W⊸Y (w₁ , y₁)
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) with w₀≁w₁
              where
                w₀≁w₁ = y₀≁y₁→w₀≁w₁ y₀≁y₁
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) | inj₁ w₀≈w₁ = ¬w₀≈w₁ w₀≈w₁
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) | inj₂ ¬w₀∼w₁ = ¬w₀∼w₁ w₀∼w₁
            --]]]
        x₀z₀≁x₁z₁→w₀y₀≁w₁y₁ (inj₂ ¬x₀z₀∼x₁z₁) = inj₂ ¬w₀y₀∼w₁y₁
          where
            --[[[
            ¬w₀y₀∼w₁y₁ : ¬ (w₀ , y₀) ∼W⊸Y (w₁ , y₁)
            ¬w₀y₀∼w₁y₁ (w₀∼w₁→y₀∼y₁ , y₀≁y₁→w₀≁w₁) = ⊥-elim $ ¬x₀z₀∼x₁z₁ x₀z₀∼x₁z₁
              where
                x₀∼x₁→z₀∼z₁ : (x₀ ∼X x₁) → (z₀ ∼Z z₁)
                x₀∼x₁→z₀∼z₁ x₀∼x₁ = y₀∼y₁→z₀∼z₁ (w₀∼w₁→y₀∼y₁ (x₀∼x₁→w₀∼w₁ x₀∼x₁))

                z₀≁z₁→x₀≁x₁ : (z₀ ≁Z z₁) → (x₀ ≁X x₁)
                z₀≁z₁→x₀≁x₁ z₀≁z₁ = w₀≁w₁→x₀≁x₁ (y₀≁y₁→w₀≁w₁ (z₀≁z₁→y₀≁y₁ z₀≁z₁))

                x₀z₀∼x₁z₁ : (x₀ , z₀) ∼X⊸Z (x₁ , z₁)
                x₀z₀∼x₁z₁ = x₀∼x₁→z₀∼z₁ , z₀≁z₁→x₀≁x₁
            --]]]
        --]]]

    r : p Respects (CoherentSpace._≈_ $ (W ⊸₀ Y) ⇒ₗ (X ⊸₀ Z))
    r {(w₀ , y₀) , (x₀ , z₀)} {(w₁ , y₁) , (x₁ , z₁)} ((w₀≈w₁ , y₀≈y₁) , x₀≈x₁ , z₀≈z₁)
      (x₀w₀∈f , y₀z₀∈f)
      = (resp-≈ f (x₀≈x₁ , w₀≈w₁) x₀w₀∈f) , (resp-≈ g (y₀≈y₁ , z₀≈z₁) y₀z₀∈f)
    --]]]

module _ {X Y : Obj} where
  private
    id_⟨X⟩⊸id_⟨Y⟩ = Category.id CohL' {X} ⊸₁ Category.id CohL' {Y}
    id_⟨X⊸Y⟩ = Category.id CohL' {X ⊸₀ Y}

    _≈X_ = CoherentSpace._≈_ X
    _≈Y_ = CoherentSpace._≈_ Y

    ≈X-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X)

    open _⇒'_

  identity : CohL' [ id_⟨X⟩⊸id_⟨Y⟩ ≈ id_⟨X⊸Y⟩ ]
  identity = id_⟨X⟩⊸id_⟨Y⟩⊆id_⟨X⊸Y⟩ , id_⟨X⊸Y⟩⊆id_⟨X⟩⊸id_⟨Y⟩
    --[[[
    where
      id_⟨X⟩⊸id_⟨Y⟩⊆id_⟨X⊸Y⟩ : pred id_⟨X⟩⊸id_⟨Y⟩ ⊆ pred id_⟨X⊸Y⟩
      id_⟨X⟩⊸id_⟨Y⟩⊆id_⟨X⊸Y⟩ {(x₀ , y₀) , (x₁ , y₁)} (x₁x₀∈id_⟨X⊸X⟩ , y₀y₁∈id_⟨Y⊸Y⟩) = x₀≈x₁ , y₀≈y₁
        where
          x₀≈x₁ : x₀ ≈X x₁
          x₀≈x₁ = ≈X-sym x₁x₀∈id_⟨X⊸X⟩

          y₀≈y₁ : y₀ ≈Y y₁
          y₀≈y₁ = y₀y₁∈id_⟨Y⊸Y⟩

      id_⟨X⊸Y⟩⊆id_⟨X⟩⊸id_⟨Y⟩ : pred id_⟨X⊸Y⟩ ⊆ pred id_⟨X⟩⊸id_⟨Y⟩
      id_⟨X⊸Y⟩⊆id_⟨X⟩⊸id_⟨Y⟩ {(x₀ , y₀) , (x₁ , y₁)} (x₀x₁∈id_⟨X⊸X⟩ , y₀y₁∈id_⟨Y⊸Y⟩)= x₁≈x₀ , y₀≈y₁
        where
          x₁≈x₀ : x₁ ≈X x₀
          x₁≈x₀ = ≈X-sym x₀x₁∈id_⟨X⊸X⟩

          y₀≈y₁ : y₀ ≈Y y₁
          y₀≈y₁ = y₀y₁∈id_⟨Y⊸Y⟩
    --]]]

-- (((x₀ , w₀) ∈ (pred f)) , ((y₀ , z₀) ∈ (pred g))) = {!!}
[-,-] : Bifunctor (Category.op CohL') CohL' CohL'
[-,-] = record
    { F₀ = λ (X , Y) → (X ⊸₀ Y)
    ; F₁ = λ (f , g) → (f ⊸₁ g)
    ; identity = λ {X,Y} → identity {proj₁ X,Y} {proj₂ X,Y}
    ; homomorphism = {!!}
    ; F-resp-≈ = {!!}
    }
