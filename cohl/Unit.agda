{-# OPTIONS --without-K --allow-unsolved-metas #-}
module Unit {c} where

open import Tensor {c}

open import Data.Product
open import Data.Sum hiding ([_,_])
open import Function using (_$_)
open import Relation.Unary using (Pred ; _⊆_ ; _∈_)
open import Relation.Binary using 
  (IsEquivalence; _Respects_)
open import Relation.Nullary using (¬_)

open import Categories.Category

open import CoherentSpace
open import Level

private
  open import Categories.Morphism using (_≅_)

  CohL' = CohL {c} {c}
  open Category CohL' using (Obj ; _⇒_ ; id)

  ∣_⇒_⇒_[_∘_] : (X Y Z : Category.Obj CohL') → (g : CohL' [ Y , Z ]) → (f : CohL' [ X , Y ]) → CohL' [ X , Z ]
  ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ CohL' {X} {Y} {Z} g f) 

  ∣_⇒_[_≈_] : (X Y : Category.Obj CohL') → (g : CohL' [ X , Y ]) → (f : CohL' [ X , Y ]) → Set _
  ∣ X ⇒ Y [ g ≈ f ] = (Category._≈_ CohL' {X} {Y} g f) 

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
  

  private
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

          _∘₁_ = ∣ X ⇒ F₀ (unit , X) ⇒ X [_∘_]
          _∘₂_ = ∣ F₀ (unit , X) ⇒ X ⇒ F₀ (unit , X) [_∘_]

          f-⇒ = from-⇒ ∘₁ to-⇒
          g-⇒ = to-⇒ ∘₂ from-⇒
          idX-⇒ = Category.id CohL' {X}
          id1⊗X-⇒ = Category.id CohL' {F₀ (unit , X)}

          isoˡ : g-⇒ ≈1⊗X⇒1⊗X id1⊗X-⇒
          isoˡ = g⊆id , id⊆g
            where
              g₁ = proj₁ g-⇒
              id₁ = proj₁ id1⊗X-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)

              g⊆id : g₁ ⊆ id₁
              g⊆id {(∗ , x) , (∗ , x')} (y , x≈y , y≈x') = ∗≈∗ , trans x≈y y≈x'

              id⊆g : id₁ ⊆ g₁
              id⊆g {(∗ , x) , (∗ , x')} (∗≈∗ , x≈x') = x , refl , x≈x'

          isoʳ : f-⇒ ≈X⇒X idX-⇒
          isoʳ = f⊆id , id⊆f
            where
              f₁ = proj₁ f-⇒
              id₁ = proj₁ idX-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)

              f⊆id : f₁ ⊆ id₁
              f⊆id {x , x'} ((∗ , y) , x≈y , y≈x') = trans x≈y y≈x'

              id⊆f : id₁ ⊆ f₁
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

          _∘₁_ = ∣ X ⇒ F₀ (X , unit) ⇒ X [_∘_]
          _∘₂_ = ∣ F₀ (X , unit) ⇒ X ⇒ F₀ (X , unit) [_∘_]

          f-⇒ = from-⇒ ∘₁ to-⇒
          g-⇒ = to-⇒ ∘₂ from-⇒
          idX-⇒ = id {X}
          idX⊗1-⇒ = id {F₀ (X , unit)}

          isoˡ : g-⇒ ≈X⊗1⇒X⊗1 idX⊗1-⇒
          isoˡ = g⊆id , id⊆g
            where
              g₁ = proj₁ g-⇒
              id₁ = proj₁ idX⊗1-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)
        
              g⊆id : g₁ ⊆ id₁
              g⊆id {(x , ∗) , (x' , ∗)} (y , x≈y , y≈x') = trans x≈y y≈x' , ∗≈∗
  
              id⊆g : id₁ ⊆ g₁
              id⊆g {(x , ∗) , (x' , ∗)} (x≈x' , ∗≈∗) = x , refl , x≈x'

          isoʳ : f-⇒ ≈X⇒X idX-⇒
          isoʳ = f⊆id , id⊆f
            where
              f₁ = proj₁ f-⇒
              id₁ = proj₁ idX-⇒

              open IsEquivalence (CoherentSpace.≈-isEquivalence X)

              f⊆id : f₁ ⊆ id₁
              f⊆id {x , x'} ((y , ∗) , x≈y , y≈x') = trans x≈y y≈x'

              id⊆f : id₁ ⊆ f₁
              id⊆f {x , x'} x≈x' = (x , ∗) , refl , x≈x'

module _ {X : Obj} {Y : Obj} {f : X ⇒ Y} where
  private
    _≈X⇒Y_ = CoherentSpace._≈_ (X ⇒ₗ Y)
    ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
    ≈X-sym  = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X)
    ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y)

    f-resp-≈X⇒Y : (proj₁ f) Respects _≈X⇒Y_
    f-resp-≈X⇒Y = proj₂ $ proj₂ f
 
    1⊗X≅X = unitorˡ {X} 
    1⊗Y≅Y = unitorˡ {Y}

  module _ where
    private
      1⊗X⇒X = _≅_.from 1⊗X≅X 
      1⊗Y⇒Y = _≅_.from 1⊗Y≅Y
  
      bottomLeft : F₀ (unit , X) ⇒ Y
      bottomLeft = ∣ F₀ (unit , X) ⇒ F₀ (unit , Y) ⇒ Y [ 1⊗Y⇒Y ∘ (F₁ {unit , X} {unit , Y} (id {unit} , f)) ]
    
      topRight : F₀ (unit , X) ⇒ Y
      topRight = ∣ F₀ (unit , X) ⇒ X ⇒ Y [ f ∘ 1⊗X⇒X  ]

    unitorˡ-commute-from : ∣ F₀ (unit , X) ⇒ Y [ bottomLeft ≈ topRight ] 
    unitorˡ-commute-from = bl⊆tr , tr⊆bl
      where
        bl⊆tr : proj₁ bottomLeft ⊆ proj₁ topRight
        bl⊆tr {(∗ , x) , y} ((∗ , y') , (∗≈∗ , xy'∈f) , y'≈y) = x , ≈X-refl , f-resp-≈X⇒Y xy'≈xy xy'∈f 
          where
            xy'≈xy : (x , y') ≈X⇒Y (x , y)
            xy'≈xy = ≈X-refl , y'≈y

        tr⊆bl : proj₁ topRight ⊆ proj₁ bottomLeft
        tr⊆bl {(∗ , x) , y} (x' , x≈x' , x'y∈f) = (∗ , y) , (∗≈∗ , xy∈f) , ≈Y-refl
          where 
            x'y≈xy : (x' , y) ≈X⇒Y (x , y) 
            x'y≈xy = (≈X-sym x≈x' , ≈Y-refl)

            xy∈f : (x , y) ∈ (proj₁ f)
            xy∈f = f-resp-≈X⇒Y x'y≈xy x'y∈f

  module _ where
    private
      X⇒1⊗X = _≅_.to 1⊗X≅X 
      Y⇒1⊗Y = _≅_.to 1⊗Y≅Y

      bottomLeft : X ⇒ F₀ (unit , Y)
      bottomLeft = ∣ X ⇒ Y ⇒ F₀ (unit , Y) [ Y⇒1⊗Y ∘ f ]

      topRight : X ⇒ F₀ (unit , Y)
      topRight = ∣ X ⇒ F₀ (unit , X) ⇒ F₀ (unit , Y) [ F₁ {unit , X} {unit , Y} (id {unit} , f) ∘ X⇒1⊗X ] 

    unitorˡ-commute-to : ∣ X ⇒ F₀ (unit , Y) [ bottomLeft ≈ topRight ]
    unitorˡ-commute-to = bl⊆tr , tr⊆bl
      where
        bl⊆tr : proj₁ bottomLeft ⊆ proj₁ topRight
        bl⊆tr {x , (∗ , y)} (y' , xy'∈f , y'≈y) = (∗ , x) , ≈X-refl , (∗≈∗ , xy∈f)
          where
            xy∈f : (x , y) ∈ proj₁ f
            xy∈f = f-resp-≈X⇒Y (≈X-refl , y'≈y) xy'∈f

        tr⊆bl : proj₁ topRight ⊆ proj₁ bottomLeft
        tr⊆bl {x , (∗ , y)} ((∗ , x') , x≈x' , (∗≈∗ , x'y∈f)) = y , xy∈f , ≈Y-refl
          where
            xy∈f : (x , y) ∈ proj₁ f
            xy∈f = f-resp-≈X⇒Y (≈X-sym x≈x' , ≈Y-refl) x'y∈f
          
