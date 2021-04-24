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
    open _⇒'_
    open Commutation CohL'
    open import Categories.Category.Monoidal
    open Monoidal monoidal hiding (_⊗₀_ ; _⊗₁_)

    hexagon : [ ((X ⊗₀ Y) ⊗₀ Z) ⇒ (Y ⊗₀ (Z ⊗₀ X)) ]⟨ 
                (η⇒ $ X , Y) ⊗₁ (id {Z})     ⇒⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
                associator.from {Y} {X} {Z}  ⇒⟨ Y ⊗₀ (X ⊗₀ Z) ⟩
                (id {Y}) ⊗₁ (η⇒ $ X , Z)
              ≈ associator.from {X} {Y} {Z}  ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⟩
                (η⇒ $ X , Y ⊗₀ Z)            ⇒⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
                associator.from {Y} {Z} {X}
              ⟩
    hexagon = {!!}          

symmetric : Symmetric monoidal
symmetric = symmetricHelper monoidal (record { braiding = braiding
                                               ; commutative = λ {X} {Y} → commutative {Y} {X} 
                                               ; hexagon = λ {X} {Y} {Z} → hexagon {X} {Y} {Z} })
