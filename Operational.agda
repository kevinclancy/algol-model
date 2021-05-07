module Operational where

open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Syntax

variable
  P₁ P₂ P₃ P₄ : P

data _⟶_ : P → P → Set where
  
  ⟶-Fst : Fst (Pair P₁ P₂) ⟶ P₁

  ⟶-Snd : Snd (Pair P₁ P₂) ⟶ P₂

  ⟶-Elim : (P₃ ≡ sub P₂ 0 P₁)
            -----------------------
          → (App (Abs P₁) P₂) ⟶ P₃

  ⟶-Rec : Rec P₁ ⟶ App P₁ (Rec P₁)

  ⟶-PropFst : Fst (IfThenElse P₁ P₂ P₃) ⟶ IfThenElse P₁ (Fst P₂) (Fst P₃)

  ⟶-PropSnd : Snd (IfThenElse P₁ P₂ P₃) ⟶ IfThenElse P₁ (Snd P₂) (Snd P₃)

  ⟶-PropApp : (App (IfThenElse P₁ P₂ P₃) P₄) ⟶ IfThenElse P₁ (App P₂ P₄) (App P₃ P₄)

  ⟶-PropAssign : (Assign (IfThenElse P₁ P₂ P₃) P₄) ⟶ IfThenElse P₁ (Assign P₂ P₄) (Assign P₃ P₄)
     

