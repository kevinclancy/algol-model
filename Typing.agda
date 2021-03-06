module Typing where

open import Syntax
open import Data.Vec
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_)


-- TODO: I should make some of these arguments implicit, but make sure that inference works.
data _∣_⊢_∣_ : {n m : ℕ} → (Vec θ n) → (Vec θ m) → P → θ → Set where
  TyId : {n m : ℕ} {k : Fin m} → (Π : Vec θ n) → (Γ : Vec θ m) → (θ₁ : θ) → 
       (lookup Γ k ≡ θ₁) → (Π ∣ Γ ⊢ (Id (toℕ k)) ∣ θ₁)  

  TyFunI : {n m : ℕ} {k : Fin m} → (Π : Vec θ n) → (Γ : Vec θ m) → (θ₁ θ₂ : θ) → (lookup Γ k ≡ θ₁) → 
           (P₁ : P) → (Π ∣ (θ₁ ∷ Γ) ⊢ P₁ ∣ θ₂) → (Π ∣ Γ ⊢ (Abs P₁) ∣ (θ₁ θ→ θ₂)) 

  TyFunE : {n₁ m₁ n₂ m₂ : ℕ} → (Π₁ : Vec θ n₁) → (Π₂ : Vec θ n₂) → (Γ₁ : Vec θ m₁) → (Γ₂ : Vec θ m₂) → 
           (θ₁ θ₂ : θ) → (P₁ P₂ : P) → (Π₁ ∣ Γ₁ ⊢ P₁ ∣ (θ₁ θ→ θ₂)) → (Π₂ ∣ Γ₂ ⊢ P₂ ∣ θ₁) → 
           ((Π₁ ++ Π₂) ∣ (Γ₁ ++ Γ₂) ⊢ (App P₁ P₂) ∣ θ₂)

  TyProdI : {n m : ℕ} → (Π : Vec θ n) → (Γ : Vec θ m) → (θ₁ θ₂ : θ) → (P₁ P₂ : P) → (Π ∣ Γ ⊢ P₁ ∣ θ₁) → 
            (Π ∣ Γ ⊢ P₂ ∣ θ₂) → (Π ∣ Γ ⊢ (Pair P₁ P₂) ∣ (θ₁ θ× θ₂))

  TyProdE1 : {n m : ℕ} → (Π : Vec θ n) → (Γ : Vec θ m) → (θ₁ θ₂ : θ) → (P₀ : P) → 
             (Π ∣ Γ ⊢ P₀ ∣ (θ₁ θ× θ₂)) → (Π ∣ Γ ⊢ (Fst P₀) ∣ (θ₁ θ× θ₂))

  TyProdE2 : {n m : ℕ} → (Π : Vec θ n) → (Γ : Vec θ m) → (θ₁ θ₂ : θ) → (P₀ : P) → 
             (Π ∣ Γ ⊢ P₀ ∣ (θ₁ θ× θ₂)) → (Π ∣ Γ ⊢ (Snd P₀) ∣ θ₂)
