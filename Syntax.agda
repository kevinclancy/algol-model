module Syntax where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat

data δ : Set where
  δInt : δ
  δBool : δ
  
data θ : Set where
  θVar : δ → θ
  θExp : δ → θ
  θComm : θ
  _θ×_ : (θ₁ θ₂ : θ) → θ
  _θ→_ : (θ₁ θ₂ : θ) → θ
  _θ→ₚ_ : (θ₁ θ₂ : θ) → θ 

data IsPassive : (θ → Set) where
  IsPassiveExp : (δ₁ : δ) → IsPassive (θExp δ₁)
  IsPassiveProd : (θ₁ θ₂ : θ) → (IsPassive θ₁) → (IsPassive θ₂) → (IsPassive (θ₁ θ× θ₂))
  IsPassiveFun1 : (θ₁ θ₂ : θ) → (IsPassive θ₂) → (IsPassive (θ₁ θ→ θ₂))
  IsPassiveFun2 : (θ₁ θ₂ : θ) → (IsPassive (θ₁ θ→ₚ θ₂))

data P : Set where
  -- An identifier occurence
  Id : ℕ → P
  -- The abstraction "λ.P₁"
  Abs : (P₁ : P) → P
  -- The application "P₁ P₂"
  App : (P₁ P₂ : P) → P
  -- The pair "(P₁ , P₂)" 
  Pair : (P₁ P₂ : P) → P
  -- the projection (Fst P₁)
  Fst : (P₁ : P) → P
  -- the projection (Snd P₁)
  Snd : (P₁ : P) → P
  --constants
  --coming soon






 
