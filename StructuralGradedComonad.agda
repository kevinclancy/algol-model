

module StructuralGradedComonad where

open import Level

open import Function using (_$_)

open import CoeffectScalarStructure

open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal
open import Categories.Functor using (Endofunctor ; Functor ; _∘F_ ; id)
open import Categories.NaturalTransformation using (NaturalTransformation)

open Functor using (F₀ ; F₁)

record StructuralGradedComonad (ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level) (Q : CoeffectScalarStructure ℓ₀ ℓ₁ ℓ₂) (C : Category ℓ₃ ℓ₄ ℓ₅) (monoidal : Monoidal C) : Set _ where

  private
    |Q| = CoeffectScalarStructure.Carrier Q
    open CoeffectScalarStructure.CoeffectScalarStructure Q using (_≤_ ; use ; _∗_ ; _+_)
    open Category C using (Obj ; _∘_ ; _≈_)
    open Categories.Category.Commutation C
    

  field
    D : |Q| → Endofunctor C
    ⟦≤⟧ : ∀ {q r : |Q|} → q ≤ r → NaturalTransformation (D q) (D r)
    δ : (q r : |Q|) → NaturalTransformation (D $ q ∗ r) (D q ∘F D r) 
    ε : NaturalTransformation (D use) id
    
  η = NaturalTransformation.η

  field
{--
    assoc : ∀ {X : Obj} {r s t : |Q|} → [ F₀ (D (r ∗ (s ∗ t))) X ⇒ F₀ (D r ∘F D s ∘F D t) X ]⟨ 
                                          {!F₁ (D r) ?  !} ⇒⟨ F₀ (D r ∘F D (s ∗ t)) X ⟩ {!!} ≈ {!!} 
                                        ⟩
--}
    -- the ∗ operator should be *strictly* monoidal; otherwise, this won't type check 
    -- it will probably be easier just to use propositional equality for scalars instead of setoid equality
    assoc : ∀ { X : Obj } {r s t : |Q|} → 
              (Functor.F₁ (D r) $ (η $ δ s t) X) ∘ (η $ δ r (s ∗ t)) X 
              ≈
              ((η $ δ r s) (F₀ (D t) X) ∘ {!(η $ δ (r ∗ s) t) X!})  
    
