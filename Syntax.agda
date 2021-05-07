module Syntax where

open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary
open import Data.Nat renaming (_<?_ to _ℕ<?_)
open import Data.Nat.Properties using (<-cmp)
open import Relation.Binary.Definitions using (tri< ; tri> ; tri≈)
open import Data.Bool
--open import Agda.Builtin.Nat

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
  -- the phrase "if P-cond then P₁ else P₂"
  IfThenElse : (P-cond : P) → (P₁ : P) → (P₂ : P) → P   
  -- the phrase "rec P₁"
  Rec : (P₁ : P) → P
  -- the phrase "P₁ := P₂"
  Assign : (P₁ : P) → (P₂ : P) → P

--constants
  --coming soon

-- (shift n) decrements any identifier strictly greater than n 
{--
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
--}

-- substitute P₁ for deBruijn index n in P₂
sub : (P₁ : P) → (n : ℕ) → (P₂ : P) → P
sub P₁ n (Id m) with (<-cmp n m) 
sub P₁ n (Id m) | tri< _ _ _  with m
sub P₁ n (Id m) | tri< _ _ _ | suc m' = Id m' 
sub P₁ n (Id m) | tri> _ _ _ = Id m 
sub P₁ n (Id .n) | tri≈ _ PE.refl _ = P₁
sub P₁ n (Abs P₂) = Abs (sub P₁ (suc n) P₂)
sub P₁ n (App P₂ P₃) = App (sub P₁ n P₂) (sub P₁ n P₃)
sub P₁ n (Pair P₂ P₃) = Pair (sub P₁ n P₂) (sub P₁ n P₃)
sub P₁ n (Fst P₂) = Fst (sub P₁ n P₂)
sub P₁ n (Snd P₂) = Snd (sub P₁ n P₂)
sub P₁ n (IfThenElse P-cond P₂ P₃) = IfThenElse (sub P₁ n P-cond) (sub P₁ n P₂) (sub P₁ n P₃)
sub P₁ n (Rec P₂) = Rec (sub P₁ n P₂)
sub P₁ n (Assign P₂ P₃) = Assign (sub P₁ n P₂) (sub P₁ n P₃)


