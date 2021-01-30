{-# OPTIONS --without-K --allow-unsolved-metas #-}
module Unit {c} where

open import Tensor {c}

open import Data.Product
open import Data.Sum hiding ([_,_])
open import Function using (_$_)
open import Relation.Unary
open import Relation.Binary using 
  (IsEquivalence; _Respects_)
open import Relation.Nullary using (¬_)

open import Categories.Category

open import CoherentSpace

private
  CohL' = CohL {c} {c}
  open Category CohL' using (Obj)

  _∣_⇒_⇒_[_∘_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y Z : Category.Obj C) → (g : C [ Y , Z ]) → (f : C [ X , Y ]) → C [ X , Z ]
  C ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ C g f) 

  _∣_⇒_[_≈_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y : Category.Obj C) → (g : C [ X , Y ]) → (f : C [ X , Y ]) → Set _
  C ∣ X ⇒ Y [ g ≈ f ] = (Category._≈_ C g f) 

data |1| : Set c where
  ∗ : |1|

data _≈1_ : |1| → |1| → Set c where
  ∗≈∗ : ∗ ≈1 ∗

≈-trans : ∀ {x y z : |1|} → x ≈1 y → y ≈1 z → x ≈1 z
≈-trans {∗} {∗} {∗} refl₁ refl₂  = ∗≈∗

≈-sym : ∀ {x y : |1|} → x ≈1 y → y ≈1 x
≈-sym {∗} {∗} ∗≈∗ = ∗≈∗

≈-refl : ∀ {x : |1|} → x ≈1 x
≈-refl {∗} = ∗≈∗ 

unit : Obj
unit = record 
  { TokenSet = |1| 
  ; _≈_ = _≈1_
  ; _∼_ = _≈1_
  ; ∼-respˡ-≈ = λ {x} {y} {y'} y≈y' x≈y → ≈-trans (≈-sym y≈y') x≈y
  ; ≈→∼ = λ a≈b → a≈b
  ; ∼-sym = ≈-sym
  ; ∼-refl = ≈-refl
  ; ≈-isEquivalence = record 
    { refl = ≈-refl 
    ; sym = ≈-sym
    ; trans = ≈-trans 
    } 
  }

module _ {X : Obj} where
  open import Categories.Morphism using (_≅_)
  _≅CohL_ = _≅_ CohL'
  _≈X_ = CoherentSpace._≈_ X
  ≈X-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X)

  _∼X_ = CoherentSpace._∼_ X
  _≁X_ = CoherentSpace._≁_ X
  ∼X-respˡ-≈X = CoherentSpace.∼-respˡ-≈ X
  ∼X-respʳ-≈X = CoherentSpace.∼-respʳ-≈ X

  unitorˡ : F₀ (unit , X) ≅CohL X
  unitorˡ = record
    { from = from , from-isPoint , from-resp-≈
    ; to = to , to-isPoint , to-resp-≈
    ; iso = iso
    }
    where
      unit⊗X⇒X = F₀ (unit , X) ⇒ₗ X
      X⇒unit⊗X = X ⇒ₗ F₀ (unit , X)

      _∼1⊗X_ = CoherentSpace._∼_ $ F₀ (unit , X)  
      _≁1⊗X_ = CoherentSpace._≁_ $ F₀ (unit , X) 

      from : Pred (CoherentSpace.TokenSet unit⊗X⇒X) c
      from ((_ , x) , x') = x ≈X x'

      from-isPoint : CoherentSpace.isPoint unit⊗X⇒X from
      --[[[
      from-isPoint ((∗ , a) , a') ((∗ , b) , b') a≈a' b≈b' = p , q
        where
          p : (∗ , a) ∼1⊗X (∗ , b) → a' ∼X b'
          p (_ , a∼b) = ∼X-respˡ-≈X a≈a' (∼X-respʳ-≈X b≈b' a∼b)

          q : (a' ≁X b') → (∗ , a) ≁1⊗X (∗ , b)
          q (inj₁ a'≈b') = inj₁ (∗≈∗  , a≈b)
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)
              a≈b : a ≈X b
              a≈b = begin 
                  a   ≈⟨ a≈a' ⟩
                  a'  ≈⟨ a'≈b' ⟩
                  b' ≈˘⟨ b≈b' ⟩
                  b
                ∎
          q (inj₂ ¬a'∼b') = inj₂ ¬∗a∼∗b
            where
              ¬∗a∼∗b : ¬ (∗ , a) ∼1⊗X (∗ , b)
              ¬∗a∼∗b (_ , a∼b) = ¬a'∼b' (∼X-respʳ-≈X b≈b' a'∼b)
                where
                  a'∼b : a' ∼X b
                  a'∼b = ∼X-respˡ-≈X a≈a' a∼b

      --]]]

      from-resp-≈ : from Respects (CoherentSpace._≈_ unit⊗X⇒X) 
      --[[[
      from-resp-≈ {(∗ , a) , a' } {(∗ , b) , b'} ((_ , a≈b) , a'≈b') a≈a' = begin
          b ≈˘⟨ a≈b ⟩
          a  ≈⟨ a≈a' ⟩
          a' ≈⟨ a'≈b' ⟩
          b'
        ∎
        where
          import Relation.Binary.Reasoning.Setoid as SetR
          open SetR (CoherentSpace.setoid X)               
      --]]]

      to : Pred (CoherentSpace.TokenSet X⇒unit⊗X) c
      to (x , (_ , x')) = x ≈X x'

      to-isPoint : CoherentSpace.isPoint X⇒unit⊗X to
      --[[[
      to-isPoint (a , (∗ , a')) (b , (∗ , b')) a≈a' b≈b' = p , q
        where
          p : a ∼X b → (∗ , a') ∼1⊗X (∗ , b')
          p a∼b = ∗≈∗ , ∼X-respʳ-≈X b≈b' a'∼b 
            where
              a'∼b : a' ∼X b
              a'∼b = ∼X-respˡ-≈X a≈a' a∼b

          q : (∗ , a') ≁1⊗X (∗ , b') → a ≁X b
          q (inj₁ (∗≈∗ , a'≈b')) = inj₁ r
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)

              r : a ≈X b
              r = begin
                  a   ≈⟨ a≈a' ⟩
                  a'  ≈⟨ a'≈b' ⟩
                  b' ≈˘⟨ b≈b' ⟩
                  b
                ∎ 
          q (inj₂ ¬∗a'∼∗b') = inj₂ ¬a∼b
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)

              ¬a∼b : ¬ (a ∼X b)
              ¬a∼b a∼b = ¬∗a'∼∗b' (∗≈∗ , a'∼b')
                where
                  a'∼b : a' ∼X b
                  a'∼b = ∼X-respˡ-≈X a≈a' a∼b

                  a'∼b' : a' ∼X b'
                  a'∼b' = ∼X-respʳ-≈X b≈b' a'∼b
      --]]]

      to-resp-≈ : to Respects (CoherentSpace._≈_ X⇒unit⊗X) 
      --[[[
      to-resp-≈ {(a , (∗ , a'))} {(b , (∗ , b'))} (a≈b , (∗≈∗ , a'≈b')) a≈a' = b≈b'
        where
          import Relation.Binary.Reasoning.Setoid as SetR
          open SetR (CoherentSpace.setoid X)

          b≈b' : b ≈X b'
          b≈b' = begin
              b ≈˘⟨ a≈b ⟩
              a  ≈⟨ a≈a' ⟩ 
              a' ≈⟨ a'≈b' ⟩
              b'
            ∎
      --]]]

      unit⊗X≅X = Categories.Morphism.Iso CohL' {F₀ (unit , X)} {X} 

      to-⇒ : CohL' [ X , F₀ (unit , X) ]
      to-⇒ = to , to-isPoint , to-resp-≈

      from-⇒ : CohL' [ F₀ (unit , X) , X ]             
      from-⇒ = from , from-isPoint , from-resp-≈

      iso : unit⊗X≅X from-⇒ to-⇒
      --[[[
      iso = record 
        { isoˡ = isoˡ 
        ; isoʳ = isoʳ
        }
        where
          _≈1⊗X⇒1⊗X_ = Category._≈_ CohL' {F₀ (unit , X)} {F₀ (unit , X)}
          _≈X⇒X_ = Category._≈_ CohL' {X} {X}

          _∘₁_ = CohL' ∣ X ⇒ F₀ (unit , X) ⇒ X [_∘_]
          _∘₂_ = CohL' ∣ F₀ (unit , X) ⇒ X ⇒ F₀ (unit , X) [_∘_]

          f-⇒ = from-⇒ ∘₁ to-⇒
          g-⇒ = to-⇒ ∘₂ from-⇒
          idX-⇒ = Category.id CohL' {X}
          id1⊗X-⇒ = Category.id CohL' {F₀ (unit , X)}

          isoˡ : g-⇒ ≈1⊗X⇒1⊗X id1⊗X-⇒
          isoˡ = g⊆id , id⊆g
            where
              g = proj₁ g-⇒
              id = proj₁ id1⊗X-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)

              g⊆id : g ⊆ id
              g⊆id {(∗ , x) , (∗ , x')} (y , x≈y , y≈x') = ∗≈∗ , trans x≈y y≈x'

              id⊆g : id ⊆ g
              id⊆g {(∗ , x) , (∗ , x')} (∗≈∗ , x≈x') = x , refl , x≈x'

          isoʳ : f-⇒ ≈X⇒X idX-⇒
          isoʳ = f⊆id , id⊆f
            where
              f = proj₁ f-⇒
              id = proj₁ idX-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)

              f⊆id : f ⊆ id
              f⊆id {x , x'} ((∗ , y) , x≈y , y≈x') = trans x≈y y≈x'

              id⊆f : id ⊆ f
              id⊆f {x , x'} x≈x' = (∗ , x) , refl , x≈x'
      --]]]

  unitorʳ : F₀ (X , unit) ≅CohL X
  unitorʳ = record
    { from = from , from-isPoint , from-resp-≈
    ; to = to , to-isPoint , to-resp-≈
    ; iso = iso
    }
    where
      X⊗unit⇒X = F₀ (X , unit) ⇒ₗ X
      X⇒X⊗unit = X ⇒ₗ F₀ (X , unit)

      _∼X⊗1_ = CoherentSpace._∼_ $ F₀ (X , unit)  
      _≁X⊗1_ = CoherentSpace._≁_ $ F₀ (X , unit) 
      
      from : Pred (CoherentSpace.TokenSet X⊗unit⇒X) c
      from ((x , _) , x') = x ≈X x'
 
      from-isPoint : CoherentSpace.isPoint X⊗unit⇒X from
      --[[[
      from-isPoint ((a , ∗) , a') ((b , ∗) , b') a≈a' b≈b' = p , q
        where
          p : (a , ∗) ∼X⊗1 (b , ∗) → a' ∼X b'
          p (a∼b , _) = ∼X-respˡ-≈X a≈a' (∼X-respʳ-≈X b≈b' a∼b)

          q : (a' ≁X b') → (a , ∗) ≁X⊗1 (b , ∗)
          q (inj₁ a'≈b') = inj₁ (a≈b , ∗≈∗)
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)
              a≈b : a ≈X b
              a≈b = begin
                  a   ≈⟨ a≈a'  ⟩
                  a'  ≈⟨ a'≈b' ⟩
                  b' ≈˘⟨ b≈b'  ⟩
                  b
                ∎ 
          q (inj₂ ¬a'∼b') = inj₂ ¬a∗∼b∗
            where
              ¬a∗∼b∗ : ¬ (a , ∗) ∼X⊗1 (b , ∗)
              ¬a∗∼b∗ (a∼b , _) = ¬a'∼b' (∼X-respʳ-≈X b≈b' a'∼b)
                where
                  a'∼b : a' ∼X b
                  a'∼b = ∼X-respˡ-≈X a≈a' a∼b
      --]]]

      from-resp-≈ : from Respects (CoherentSpace._≈_ X⊗unit⇒X)
      --[[[
      from-resp-≈ {(a , ∗) , a'} {(b , ∗) , b'} ((a≈b , _) , a'≈b') a≈a' = begin
          b ≈˘⟨ a≈b   ⟩ 
          a  ≈⟨ a≈a'  ⟩
          a' ≈⟨ a'≈b' ⟩
          b'
        ∎ 
        where
          import Relation.Binary.Reasoning.Setoid as SetR
          open SetR (CoherentSpace.setoid X)           
      --]]]

      to : Pred (CoherentSpace.TokenSet X⇒X⊗unit) c
      to (x , (x' , _)) = x ≈X x'

      to-isPoint : CoherentSpace.isPoint X⇒X⊗unit to
      --[[[
      to-isPoint (a , (a' , ∗)) (b , (b' , ∗)) a≈a' b≈b' = p , q
        where
          p : a ∼X b → (a' , ∗) ∼X⊗1 (b' , ∗)
          p a∼b = ∼X-respʳ-≈X b≈b' a'∼b , ∗≈∗
            where
              a'∼b : a' ∼X b
              a'∼b = ∼X-respˡ-≈X a≈a' a∼b

          q : (a' , ∗) ≁X⊗1 (b' , ∗) → a ≁X b
          q (inj₁ (a'≈b' , ∗≈∗)) = inj₁ r
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)

              r : a ≈X b
              r = begin
                  a   ≈⟨ a≈a' ⟩
                  a'  ≈⟨ a'≈b' ⟩
                  b' ≈˘⟨ b≈b' ⟩
                  b
                ∎
          q (inj₂ ¬a'∗∼b'∗) = inj₂ ¬a∼b
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)

              ¬a∼b : ¬ (a ∼X b)
              ¬a∼b a∼b = ¬a'∗∼b'∗ (a'∼b' , ∗≈∗)
                where
                  a'∼b : a' ∼X b
                  a'∼b = ∼X-respˡ-≈X a≈a' a∼b

                  a'∼b' : a' ∼X b'
                  a'∼b' = ∼X-respʳ-≈X b≈b' a'∼b
      --]]]

      to-resp-≈ : to Respects (CoherentSpace._≈_ X⇒X⊗unit)
      --[[[
      to-resp-≈ {a , (a' , ∗)} {b , (b' , ∗)} (a≈b , (a'≈b' , ∗≈∗)) a≈a' = b≈b'
        where
          import Relation.Binary.Reasoning.Setoid as SetR
          open SetR (CoherentSpace.setoid X)

          b≈b' : b ≈X b'
          b≈b' = begin
              b ≈˘⟨ a≈b ⟩
              a  ≈⟨ a≈a' ⟩ 
              a' ≈⟨ a'≈b' ⟩
              b'
            ∎  
      --]]]

      X⊗unit≅X = Categories.Morphism.Iso CohL' {F₀ (X , unit)} {X} 

      to-⇒ : CohL' [ X , F₀ (X , unit) ]
      to-⇒ = to , to-isPoint , to-resp-≈

      from-⇒ : CohL' [ F₀ (X , unit) , X ]             
      from-⇒ = from , from-isPoint , from-resp-≈

      iso : X⊗unit≅X from-⇒ to-⇒ 
      iso = record
        { isoˡ = isoˡ
        ; isoʳ = isoʳ
        }
        where
          _≈X⊗1⇒X⊗1_ = Category._≈_ CohL' {F₀ (X , unit)} {F₀ (X , unit)}
          _≈X⇒X_ = Category._≈_ CohL' {X} {X}

          _∘₁_ = CohL' ∣ X ⇒ F₀ (X , unit) ⇒ X [_∘_]
          _∘₂_ = CohL' ∣ F₀ (X , unit) ⇒ X ⇒ F₀ (X , unit) [_∘_]

          f-⇒ = from-⇒ ∘₁ to-⇒
          g-⇒ = to-⇒ ∘₂ from-⇒
          idX-⇒ = Category.id CohL' {X}
          idX⊗1-⇒ = Category.id CohL' {F₀ (X , unit)}

          isoˡ : g-⇒ ≈X⊗1⇒X⊗1 idX⊗1-⇒
          isoˡ = g⊆id , id⊆g
            where
              g = proj₁ g-⇒
              id = proj₁ idX⊗1-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)
        
              g⊆id : g ⊆ id
              g⊆id {(x , ∗) , (x' , ∗)} (y , x≈y , y≈x') = trans x≈y y≈x' , ∗≈∗
  
              id⊆g : id ⊆ g
              id⊆g {(x , ∗) , (x' , ∗)} (x≈x' , ∗≈∗) = x , refl , x≈x'

          isoʳ : f-⇒ ≈X⇒X idX-⇒
          isoʳ = f⊆id , id⊆f
            where
              f = proj₁ f-⇒
              id = proj₁ idX-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)

              f⊆id : f ⊆ id
              f⊆id {x , x'} ((y , ∗) , x≈y , y≈x') = trans x≈y y≈x'

              id⊆f : id ⊆ f
              id⊆f {x , x'} x≈x' = (x , ∗) , refl , x≈x'
