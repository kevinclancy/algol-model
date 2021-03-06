{-# OPTIONS --without-K --safe #-}

open import Level

module TestModule {c : Level} where

open import Categories.Category

open import CoherentSpace using (CohL ; CoherentSpace)

private
  CohL' = CohL {c} {c}
  open Category CohL' using (Obj)

module _ {X : CoherentSpace c c} where
  private
    open Commutation CohL' using ([_⇒_]⟨_≈_⟩ ; connect)
    id-X = Category.id CohL' {X}


  test : [ X ⇒ X ]⟨ id-X ⇒⟨ X ⟩ id-X ≈ id-X ⟩
  test = Category.identityˡ CohL' {X} {X} {id-X}
