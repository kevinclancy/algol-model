module Typing where

open import Syntax
open import Data.Vec
open import Data.Nat using (ℕ)
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_)


variable 
  n m : ℕ 
  n₁ n₂ m₁ m₂ : ℕ
  k : Fin m
  Π₁ : Vec θ n₁
  Π₂ : Vec θ n₂
  Γ₁ : Vec θ m₁
  Γ₂ : Vec θ m₂
  Γ : Vec θ m
  Π : Vec θ n 
  θ₁ θ₂ : θ
  P₀ P₁ P₂ : P

data _∣_⊢_∣_ : (Vec θ n) → (Vec θ m) → P → θ → Set where

  TyId : (lookup Γ k ≡ θ₁) 
       → (m ≡ toℕ k)
         --------------------------  
       → (Π ∣ Γ ⊢ (Id m) ∣ θ₁)  

  TyFunI : (lookup Γ k ≡ θ₁) 
         → (Π ∣ (θ₁ ∷ Γ) ⊢ P₁ ∣ θ₂) 
           -------------------------------
         → (Π ∣ Γ ⊢ (Abs P₁) ∣ (θ₁ θ→ θ₂)) 

  TyFunE : (Π₁ ∣ Γ₁ ⊢ P₁ ∣ (θ₁ θ→ θ₂)) 
         → (Π₂ ∣ Γ₂ ⊢ P₂ ∣ θ₁) 
           ---------------------------------------------
         → ((Π₁ ++ Π₂) ∣ (Γ₁ ++ Γ₂) ⊢ (App P₁ P₂) ∣ θ₂)

  TyProdI : (Π ∣ Γ ⊢ P₁ ∣ θ₁) 
          → (Π ∣ Γ ⊢ P₂ ∣ θ₂)
            -----------------------------------------
          → (Π ∣ Γ ⊢ (Pair P₁ P₂) ∣ (θ₁ θ× θ₂))

  TyProdE1 : (Π ∣ Γ ⊢ P₀ ∣ (θ₁ θ× θ₂))
             ----------------------------------------
           → (Π ∣ Γ ⊢ (Fst P₀) ∣ θ₁)

  TyProdE2 : (Π ∣ Γ ⊢ P₀ ∣ (θ₁ θ× θ₂)) 
             ----------------------------------------
           → (Π ∣ Γ ⊢ (Snd P₀) ∣ θ₂)

  --TyContr : {Π : Vec θ n} → {θ₀ θ₁ : θ} → {Γ : Vec θ m} → {P₀ : P} → 
  --          (θ₁ ∷ θ₁ ∷ Π ∣ Γ ⊢ P₀ : θ₀) → (θ₁ ∷ Π ∣ Γ ⊢ (contract P₀) : θ₀)  

