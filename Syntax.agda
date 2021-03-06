module Syntax where

open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary
open import Data.Nat renaming (_<?_ to _ℕ<?_)
open import Data.Bool
open import Agda.Builtin.Nat

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
  -- An identifier occurrence
  Id : ℕ → P
  -- The abstraction "λ.P₁"
  Abs : (P₁ : P) → P
  -- The application "P₁ P₂"
  App : (P₁ P₂ : P) → P
  -- The pair "(P₁ , P₂)" 
  Pair : (P₁ P₂ : P) → P
  -- the projection "Fst P₁"
  Fst : (P₁ : P) → P
  -- the projection "Snd P₁"
  Snd : (P₁ : P) → P
  --constants
  --coming soon

-- (shift n) decrements any identifier strictly greater than n 
shift : ℕ → P → P
shift n (Id m) with n ℕ<? m
shift n (Id m) | yes n<m with m
shift n (Id m) | yes n<m | suc m' = Id m'
shift n (Id m) | no ¬n<m = Id m
shift n (Abs p) = Abs $ shift (suc n) p
shift n (App p₁ p₂) = App (shift n p₁) (shift n p₂)
shift n (Pair p₁ p₂) = Pair (shift n p₁) (shift n p₂)
shift n (Fst p) = Fst (shift n p)
shift n (Snd p) = Snd (shift n p)

contract : P → P
contract = shift 0
