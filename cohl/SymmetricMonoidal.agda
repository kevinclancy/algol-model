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
      
    monoidal : Monoidal CohL'
    monoidal = record
      { ⊗ = ⊗
      ; unit = unit
      ; unitorˡ = unitorˡ
      ; unitorʳ = unitorʳ
      ; associator = associator
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

        module _ {X Y Z : Obj} where 
          [X⊗Y]⊗Z = (F₀ (F₀ (X , Y) , Z))
          X⊗[Y⊗Z] = (F₀ (X , F₀ (Y , Z)))

          _≈X_ = CoherentSpace._≈_ X
          _∼X_ = CoherentSpace._∼_ X
          ∼X-respˡ-≈X = CoherentSpace.∼-respˡ-≈ X
          ∼X-respʳ-≈X = CoherentSpace.∼-respʳ-≈ X
          _≈Y_ = CoherentSpace._≈_ Y
          _∼Y_ = CoherentSpace._∼_ Y
          ∼Y-respˡ-≈Y = CoherentSpace.∼-respˡ-≈ Y
          ∼Y-respʳ-≈Y = CoherentSpace.∼-respʳ-≈ Y
          _≈Z_ = CoherentSpace._≈_ Z
          _∼Z_ = CoherentSpace._∼_ Z
          ∼Z-respˡ-≈Z = CoherentSpace.∼-respˡ-≈ Z
          ∼Z-respʳ-≈Z = CoherentSpace.∼-respʳ-≈ Z

          from : CoherentSpace.Point ([X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z]) 
          from = f , f-isPoint , {!!}
            where
              f : Pred (CoherentSpace.TokenSet $ [X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z]) c
              f (((x , y) , z) , (x' , (y' , z'))) = (x ≈X x') × (y ≈Y y') × (z ≈Z z')

              f-isPoint : CoherentSpace.isPoint ([X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z]) f
              f-isPoint (((x , y) , z) , (x' , (y' , z'))) (((a , b) , c) , (a' , (b' , c')))
                        (x≈x' , y≈y' , z≈z') (a≈a' , b≈b' , c≈c') = sim
                where
                  _∼_ = CoherentSpace._∼_ ([X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z])
                  _∼[XY]Z_ = CoherentSpace._∼_ [X⊗Y]⊗Z
                  _≁[XY]Z_ = CoherentSpace._≁_ [X⊗Y]⊗Z
                  _∼X[YZ]_ = CoherentSpace._∼_ X⊗[Y⊗Z]
                  _≁X[YZ]_ = CoherentSpace._≁_ X⊗[Y⊗Z]
                              
                  [xy]z∼[ab]c→x'[y'z']∼a'[b'c'] : ((x , y) , z) ∼[XY]Z ((a , b) , c) → 
                                                  (x' , (y' , z')) ∼X[YZ] (a' , (b' , c'))
                  [xy]z∼[ab]c→x'[y'z']∼a'[b'c'] ((x∼a , y∼b) , z∼c) = x'∼a' , (y'∼b' , z'∼c')
                    where
                      x'∼a' : x' ∼X a'
                      x'∼a' = ∼X-respʳ-≈X a≈a' x'∼a
                        where
                          x'∼a : x' ∼X a
                          x'∼a = ∼X-respˡ-≈X x≈x' x∼a

                      y'∼b' : y' ∼Y b'
                      y'∼b' = ∼Y-respʳ-≈Y b≈b' y'∼b
                        where
                          y'∼b : y' ∼Y b
                          y'∼b = ∼Y-respˡ-≈Y y≈y' y∼b

                      z'∼c' : z' ∼Z c'
                      z'∼c' = ∼Z-respʳ-≈Z c≈c' z'∼c
                        where
                          z'∼c : z' ∼Z c
                          z'∼c = ∼Z-respˡ-≈Z z≈z' z∼c

                  x'[y'z']≁a'[b'c']→[xy]z≁[ab]c : (x' , (y' , z')) ≁X[YZ] (a' , (b' , c')) → 
                                                  ((x , y) , z) ≁[XY]Z ((a , b) , c)
                  x'[y'z']≁a'[b'c']→[xy]z≁[ab]c (inj₁ (x'≈a' , (y'≈b' , z'≈c'))) = inj₁ ((x≈a , y≈b) , z≈c)
                    where
                      x≈a : x ≈X a
                      x≈a = begin
                          x   ≈⟨ x≈x' ⟩
                          x'  ≈⟨ x'≈a'  ⟩
                          a'  ≈˘⟨ a≈a' ⟩
                          a
                        ∎
                        where
                          import Relation.Binary.Reasoning.Setoid as SetR
                          open SetR (CoherentSpace.setoid X)

                      y≈b : y ≈Y b
                      y≈b = begin
                          y   ≈⟨ y≈y'  ⟩
                          y'  ≈⟨ y'≈b' ⟩
                          b' ≈˘⟨ b≈b'  ⟩
                          b
                        ∎
                        where
                          import Relation.Binary.Reasoning.Setoid as SetR
                          open SetR (CoherentSpace.setoid Y)                      

                      z≈c : z ≈Z c
                      z≈c = begin
                          z   ≈⟨ z≈z'  ⟩
                          z'  ≈⟨ z'≈c' ⟩
                          c' ≈˘⟨ c≈c'  ⟩
                          c
                        ∎
                        where
                          import Relation.Binary.Reasoning.Setoid as SetR
                          open SetR (CoherentSpace.setoid Z)    

                  x'[y'z']≁a'[b'c']→[xy]z≁[ab]c (inj₂ y) = {!!}

                  sim : (((x , y) , z) , (x' , (y' , z'))) ∼ (((a , b) , c) , (a' , (b' , c')))
                  sim = [xy]z∼[ab]c→x'[y'z']∼a'[b'c'] , {!x'[y'z']≁a'[b'c']→[xy]z≁[ab]c!}
                  
                  
          to : CoherentSpace.Point (X⊗[Y⊗Z] ⇒ₗ [X⊗Y]⊗Z)
          to = {!!}

          [X⊗Y]⊗Z≅X⊗[Y⊗Z] = Categories.Morphism.Iso CohL' {[X⊗Y]⊗Z} {X⊗[Y⊗Z]}  
          

          associator : {!!} -- [X⊗Y]⊗Z≅X⊗[Y⊗Z]
          associator = {!!}

        
