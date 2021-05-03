module CoeffectScalarStructure where

open import Level

open import Data.Maybe
open import Data.Sum
open import Data.Product

open import Relation.Binary using (Rel ; Decidable)
open import Algebra.Structures using (IsMonoid)
open import Relation.Binary.PropositionalEquality

record CoeffectScalarStructure (c ℓ s : Level) : Set (suc (c ⊔ ℓ ⊔ s)) where
  
  field 
    Carrier : Set c
    -- Setoid equality
    _≈_ : Rel Carrier s
    -- Composition
    _∗_ : Carrier → Carrier → Carrier 
    -- Contraction
    _+_ : Carrier → Carrier → Maybe Carrier

    -- unit of composition
    use : Carrier
    -- unit of contraction
    ign : Carrier

    _≤_ : Rel Carrier ℓ    
    _≤?_ : Decidable _≤_

    isMonoid : IsMonoid _≈_ _∗_ use

    ignUnitˡ : ∀ {x : Carrier} → Σ[ y ∈ Carrier ] (ign + x ≡ just y) × (x ≈ y)
    ignUnitʳ : ∀ {x : Carrier} → Σ[ y ∈ Carrier ] (x + ign ≡ just y) × (x ≈ y)
