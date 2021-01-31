module Utils where

open import Categories.Category

_∣_⇒_⇒_[_∘_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y Z : Category.Obj C) → (g : C [ Y , Z ]) → (f : C [ X , Y ]) → C [ X , Z ]
C ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ C g f) 

_∣_⇒_[_≈_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y : Category.Obj C) → (g : C [ X , Y ]) → (f : C [ X , Y ]) → Set _
C ∣ X ⇒ Y [ g ≈ f ] = (Category._≈_ C g f) 

