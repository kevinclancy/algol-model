{-# OPTIONS --without-K  --allow-unsolved-metas #-}
module Associator {c} where

open import Data.Product
open import Data.Sum hiding ([_,_])

open import Relation.Binary using 
  (Rel ; _Respectsˡ_ ; Symmetric ; Transitive ; Reflexive ; IsEquivalence ; 
   _Respects_)

open import Relation.Unary using (Pred ; _⊆_ ; _∈_)
open import Relation.Nullary using (¬_)
open import Function using (_$_)

open import Categories.Category
open import CoherentSpace

open import Tensor {c} using (F₀ ; F₁)

open import Categories.Morphism using (_≅_)

private 
  CohL' = CohL {c} {c}
  open Category CohL' using (Obj ; _⇒_)
  _∣_⇒_⇒_[_∘_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y Z : Category.Obj C) → (g : C [ Y , Z ]) → (f : C [ X , Y ]) → C [ X , Z ]
  C ∣ X ⇒ Y ⇒ Z [ g ∘ f ] = (Category._∘_ C g f) 

  _∣_⇒_[_≈_] : ∀ {o ℓ e} (C : Category o ℓ e) → (X Y : Category.Obj C) → (g : C [ X , Y ]) → (f : C [ X , Y ]) → Set _
  C ∣ X ⇒ Y [ g ≈ f ] = (Category._≈_ C g f) 

module _ {X Y Z : Obj} where
  private
    _≅CohL_ = _≅_ CohL'

    [X⊗Y]⊗Z = (F₀ (F₀ (X , Y) , Z))
    X⊗[Y⊗Z] = (F₀ (X , F₀ (Y , Z)))

    _≈X_ = CoherentSpace._≈_ X
    ≈X-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence X)
    ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
    _∼X_ = CoherentSpace._∼_ X
    ∼X-respˡ-≈X = CoherentSpace.∼-respˡ-≈ X
    ∼X-respʳ-≈X = CoherentSpace.∼-respʳ-≈ X
    _≈Y_ = CoherentSpace._≈_ Y
    ≈Y-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence Y)
    ≈Y-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y)
    _∼Y_ = CoherentSpace._∼_ Y
    ∼Y-respˡ-≈Y = CoherentSpace.∼-respˡ-≈ Y
    ∼Y-respʳ-≈Y = CoherentSpace.∼-respʳ-≈ Y
    _≈Z_ = CoherentSpace._≈_ Z
    ≈Z-trans = IsEquivalence.trans (CoherentSpace.≈-isEquivalence Z)
    ≈Z-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Z)
    _∼Z_ = CoherentSpace._∼_ Z
    ∼Z-respˡ-≈Z = CoherentSpace.∼-respˡ-≈ Z
    ∼Z-respʳ-≈Z = CoherentSpace.∼-respʳ-≈ Z

  from-⇒ : CoherentSpace.Point ([X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z]) 
  from-⇒ = f , f-isPoint , f-Resp-≈
    where
      f : Pred (CoherentSpace.TokenSet $ [X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z]) c
      f (((x , y) , z) , (x' , (y' , z'))) = (x ≈X x') × (y ≈Y y') × (z ≈Z z')

      f-isPoint : CoherentSpace.isPoint ([X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z]) f
      --[[[
      f-isPoint (((x , y) , z) , (x' , (y' , z'))) (((a , b) , c) , (a' , (b' , c')))
                (x≈x' , y≈y' , z≈z') (a≈a' , b≈b' , c≈c') = sim
        where
          _∼_ = CoherentSpace._∼_ ([X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z])
          _∼[XY]Z_ = CoherentSpace._∼_ [X⊗Y]⊗Z
          _≁[XY]Z_ = CoherentSpace._≁_ [X⊗Y]⊗Z
          _∼X[YZ]_ = CoherentSpace._∼_ X⊗[Y⊗Z]
          _≁X[YZ]_ = CoherentSpace._≁_ X⊗[Y⊗Z]

          [xy]z∼[ab]c→x'[y'z']∼a'[b'c'] : ((x , y) , z) ∼[XY]Z ((a , b) , c) → 
                                          (x' , (y' , z')) ∼X[YZ] (a' , (b' , c'))
          [xy]z∼[ab]c→x'[y'z']∼a'[b'c'] ((x∼a , y∼b) , z∼c) = x'∼a' , (y'∼b' , z'∼c')
            where
              x'∼a' : x' ∼X a'
              x'∼a' = ∼X-respʳ-≈X a≈a' x'∼a
                where
                  x'∼a : x' ∼X a
                  x'∼a = ∼X-respˡ-≈X x≈x' x∼a

              y'∼b' : y' ∼Y b'
              y'∼b' = ∼Y-respʳ-≈Y b≈b' y'∼b
                where
                  y'∼b : y' ∼Y b
                  y'∼b = ∼Y-respˡ-≈Y y≈y' y∼b

              z'∼c' : z' ∼Z c'
              z'∼c' = ∼Z-respʳ-≈Z c≈c' z'∼c
                where
                  z'∼c : z' ∼Z c
                  z'∼c = ∼Z-respˡ-≈Z z≈z' z∼c

          x'[y'z']≁a'[b'c']→[xy]z≁[ab]c : (x' , (y' , z')) ≁X[YZ] (a' , (b' , c')) → 
                                          ((x , y) , z) ≁[XY]Z ((a , b) , c)
          x'[y'z']≁a'[b'c']→[xy]z≁[ab]c (inj₁ (x'≈a' , (y'≈b' , z'≈c'))) = inj₁ ((x≈a , y≈b) , z≈c)
            where
              x≈a : x ≈X a
              x≈a = begin
                  x   ≈⟨ x≈x' ⟩
                  x'  ≈⟨ x'≈a'  ⟩
                  a'  ≈˘⟨ a≈a' ⟩
                  a
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid X)

              y≈b : y ≈Y b
              y≈b = begin
                  y   ≈⟨ y≈y'  ⟩
                  y'  ≈⟨ y'≈b' ⟩
                  b' ≈˘⟨ b≈b'  ⟩
                  b
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid Y)                      

              z≈c : z ≈Z c
              z≈c = begin
                  z   ≈⟨ z≈z'  ⟩
                  z'  ≈⟨ z'≈c' ⟩
                  c' ≈˘⟨ c≈c'  ⟩
                  c
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid Z)    

          x'[y'z']≁a'[b'c']→[xy]z≁[ab]c (inj₂ ¬x'[y'z']∼a'[b'c']) = inj₂ ¬[xy]z∼[ab]c
            where
              ¬[xy]z∼[ab]c : ¬ ((x , y) , z) ∼[XY]Z ((a , b) , c)
              ¬[xy]z∼[ab]c ((x∼a , y∼b) , z∼c) = ¬x'[y'z']∼a'[b'c'] ((x'∼a' , (y'∼b' , z'∼c')))
                where
                  x'∼a' : x' ∼X a'
                  x'∼a' = ∼X-respʳ-≈X a≈a' x'∼a
                    where
                      x'∼a : x' ∼X a
                      x'∼a = ∼X-respˡ-≈X x≈x' x∼a

                  y'∼b' : y' ∼Y b'
                  y'∼b' = ∼Y-respʳ-≈Y b≈b' y'∼b
                    where
                      y'∼b : y' ∼Y b
                      y'∼b = ∼Y-respˡ-≈Y y≈y' y∼b

                  z'∼c' : z' ∼Z c'
                  z'∼c' = ∼Z-respʳ-≈Z c≈c' z'∼c
                    where
                      z'∼c : z' ∼Z c
                      z'∼c = ∼Z-respˡ-≈Z z≈z' z∼c

          sim : (((x , y) , z) , (x' , (y' , z'))) ∼ (((a , b) , c) , (a' , (b' , c')))
          sim = [xy]z∼[ab]c→x'[y'z']∼a'[b'c'] , x'[y'z']≁a'[b'c']→[xy]z≁[ab]c
      --]]] 

      f-Resp-≈ : f Respects (CoherentSpace._≈_ $ [X⊗Y]⊗Z ⇒ₗ X⊗[Y⊗Z])
      --[[[
      f-Resp-≈ {((x , y) , z) , (x' , (y' , z'))} {((a , b) , c) , (a' , (b' , c'))} 
               (((x≈a , y≈b) , z≈c) , (x'≈a' , (y'≈b' , z'≈c'))) 
               (x≈x' , y≈y' , z≈z') = a≈a' , b≈b' , c≈c'
        where
          a≈a' : a ≈X a'
          a≈a' = begin 
              a ≈˘⟨ x≈a   ⟩
              x  ≈⟨ x≈x'  ⟩
              x' ≈⟨ x'≈a' ⟩
              a'
            ∎
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)

          b≈b' : b ≈Y b'
          b≈b' = begin 
              b ≈˘⟨ y≈b   ⟩
              y  ≈⟨ y≈y'  ⟩
              y' ≈⟨ y'≈b' ⟩
              b'
            ∎
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid Y)

          c≈c' : c ≈Z c'
          c≈c' = begin 
              c ≈˘⟨ z≈c   ⟩
              z  ≈⟨ z≈z'  ⟩
              z' ≈⟨ z'≈c' ⟩
              c'
            ∎
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid Z)
      --]]]     

  to-⇒ : CoherentSpace.Point (X⊗[Y⊗Z] ⇒ₗ [X⊗Y]⊗Z)
  to-⇒ = f , f-isPoint , f-Resp-≈
    where
      f : Pred (CoherentSpace.TokenSet $ X⊗[Y⊗Z] ⇒ₗ [X⊗Y]⊗Z) c
      f ((x , (y , z)) , ((x' , y') , z')) = (x ≈X x') × (y ≈Y y') × (z ≈Z z')

      f-isPoint : CoherentSpace.isPoint (X⊗[Y⊗Z] ⇒ₗ [X⊗Y]⊗Z) f
      --[[[
      f-isPoint ((x , (y , z)) , ((x' , y') , z')) ((a , (b , c)) , ((a' , b') , c'))
                (x≈x' , y≈y' , z≈z') (a≈a' , b≈b' , c≈c') = sim
        where
          _∼_ = CoherentSpace._∼_ (X⊗[Y⊗Z] ⇒ₗ [X⊗Y]⊗Z)
          _∼[XY]Z_ = CoherentSpace._∼_ [X⊗Y]⊗Z
          _≁[XY]Z_ = CoherentSpace._≁_ [X⊗Y]⊗Z
          _∼X[YZ]_ = CoherentSpace._∼_ X⊗[Y⊗Z]
          _≁X[YZ]_ = CoherentSpace._≁_ X⊗[Y⊗Z]

          x[yz]∼a[bc]→[x'y']z'∼[a'b']c' : (x , (y , z)) ∼X[YZ] (a , (b , c)) → 
                                          ((x' , y') , z') ∼[XY]Z ((a' , b') , c')
          x[yz]∼a[bc]→[x'y']z'∼[a'b']c' (x∼a , (y∼b , z∼c)) = (x'∼a' , y'∼b') , z'∼c'
            where
              x'∼a' : x' ∼X a'
              x'∼a' = ∼X-respʳ-≈X a≈a' x'∼a
                where
                  x'∼a : x' ∼X a
                  x'∼a = ∼X-respˡ-≈X x≈x' x∼a

              y'∼b' : y' ∼Y b'
              y'∼b' = ∼Y-respʳ-≈Y b≈b' y'∼b
                where
                  y'∼b : y' ∼Y b
                  y'∼b = ∼Y-respˡ-≈Y y≈y' y∼b

              z'∼c' : z' ∼Z c'
              z'∼c' = ∼Z-respʳ-≈Z c≈c' z'∼c
                where
                  z'∼c : z' ∼Z c
                  z'∼c = ∼Z-respˡ-≈Z z≈z' z∼c

          [x'y']z'≁[a'b']c'→x[yz]≁a[bc] : ((x' , y') , z') ≁[XY]Z ((a' , b') , c') → 
                                          (x , (y , z)) ≁X[YZ] (a , (b , c))
          [x'y']z'≁[a'b']c'→x[yz]≁a[bc] (inj₁ ((x'≈a' , y'≈b') , z'≈c')) = inj₁ (x≈a , (y≈b , z≈c))
            where
              x≈a : x ≈X a
              x≈a = begin
                  x   ≈⟨ x≈x' ⟩
                  x'  ≈⟨ x'≈a'  ⟩
                  a'  ≈˘⟨ a≈a' ⟩
                  a
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid X)

              y≈b : y ≈Y b
              y≈b = begin
                  y   ≈⟨ y≈y'  ⟩
                  y'  ≈⟨ y'≈b' ⟩
                  b' ≈˘⟨ b≈b'  ⟩
                  b
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid Y)                      

              z≈c : z ≈Z c
              z≈c = begin
                  z   ≈⟨ z≈z'  ⟩
                  z'  ≈⟨ z'≈c' ⟩
                  c' ≈˘⟨ c≈c'  ⟩
                  c
                ∎
                where
                  import Relation.Binary.Reasoning.Setoid as SetR
                  open SetR (CoherentSpace.setoid Z)    

          [x'y']z'≁[a'b']c'→x[yz]≁a[bc] (inj₂ ¬[x'y']z'∼[a'b']c') = inj₂ ¬x[yz]∼a[bc]
            where
              ¬x[yz]∼a[bc] : ¬ (x , (y , z)) ∼X[YZ] (a , (b , c))
              ¬x[yz]∼a[bc] (x∼a , (y∼b , z∼c)) = ¬[x'y']z'∼[a'b']c' ((x'∼a' , y'∼b') , z'∼c')
                where
                  x'∼a' : x' ∼X a'
                  x'∼a' = ∼X-respʳ-≈X a≈a' x'∼a
                    where
                      x'∼a : x' ∼X a
                      x'∼a = ∼X-respˡ-≈X x≈x' x∼a

                  y'∼b' : y' ∼Y b'
                  y'∼b' = ∼Y-respʳ-≈Y b≈b' y'∼b
                    where
                      y'∼b : y' ∼Y b
                      y'∼b = ∼Y-respˡ-≈Y y≈y' y∼b

                  z'∼c' : z' ∼Z c'
                  z'∼c' = ∼Z-respʳ-≈Z c≈c' z'∼c
                    where
                      z'∼c : z' ∼Z c
                      z'∼c = ∼Z-respˡ-≈Z z≈z' z∼c

          sim : ((x , (y , z)) , ((x' , y') , z')) ∼ ((a , (b , c)) , ((a' , b') , c'))
          sim = x[yz]∼a[bc]→[x'y']z'∼[a'b']c' , [x'y']z'≁[a'b']c'→x[yz]≁a[bc]
      --]]] 

      f-Resp-≈ : f Respects (CoherentSpace._≈_ $ X⊗[Y⊗Z] ⇒ₗ [X⊗Y]⊗Z)
      --[[[
      f-Resp-≈ {(x , (y , z)) , ((x' , y') , z')} {(a , (b , c)) , ((a' , b') , c')} 
               ((x≈a , (y≈b , z≈c)) , ((x'≈a' , y'≈b') , z'≈c')) 
               (x≈x' , y≈y' , z≈z') = a≈a' , b≈b' , c≈c'
        where
          a≈a' : a ≈X a'
          a≈a' = begin 
              a ≈˘⟨ x≈a   ⟩
              x  ≈⟨ x≈x'  ⟩
              x' ≈⟨ x'≈a' ⟩
              a'
            ∎
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid X)

          b≈b' : b ≈Y b'
          b≈b' = begin 
              b ≈˘⟨ y≈b   ⟩
              y  ≈⟨ y≈y'  ⟩
              y' ≈⟨ y'≈b' ⟩
              b'
            ∎
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid Y)

          c≈c' : c ≈Z c'
          c≈c' = begin 
              c ≈˘⟨ z≈c   ⟩
              z  ≈⟨ z≈z'  ⟩
              z' ≈⟨ z'≈c' ⟩
              c'
            ∎
            where
              import Relation.Binary.Reasoning.Setoid as SetR
              open SetR (CoherentSpace.setoid Z)
      --]]]     

  [X⊗Y]⊗Z≅X⊗[Y⊗Z] = Categories.Morphism.Iso CohL' {[X⊗Y]⊗Z} {X⊗[Y⊗Z]} 

  iso : [X⊗Y]⊗Z≅X⊗[Y⊗Z] from-⇒ to-⇒
  iso = record 
    { isoˡ = isoˡ
    ; isoʳ = isoʳ 
    }
    where
      _≈[X⊗Y]⊗Z⇒[X⊗Y]⊗Z_ = Category._≈_ CohL' {[X⊗Y]⊗Z} {[X⊗Y]⊗Z}
      _≈X⊗[Y⊗Z]⇒X⊗[Y⊗Z]_ = Category._≈_ CohL' {X⊗[Y⊗Z]} {X⊗[Y⊗Z]}

      _∘₁_ = CohL' ∣ [X⊗Y]⊗Z ⇒ X⊗[Y⊗Z] ⇒ [X⊗Y]⊗Z [_∘_]
      _∘₂_ = CohL' ∣ X⊗[Y⊗Z] ⇒ [X⊗Y]⊗Z ⇒ X⊗[Y⊗Z] [_∘_] 

      f-⇒ = to-⇒ ∘₁ from-⇒
      g-⇒ = from-⇒ ∘₂ to-⇒

      isoˡ : f-⇒ ≈[X⊗Y]⊗Z⇒[X⊗Y]⊗Z (Category.id CohL' {[X⊗Y]⊗Z})
      isoˡ = f⊆id , id⊆f
        where
          f = proj₁ f-⇒
          id = proj₁ $ Category.id CohL' {[X⊗Y]⊗Z}

          f⊆id : f ⊆ id
          f⊆id {((x , y) , z) , ((x'' , y'') , z'')} 
               ((x' , (y' , z')) , (x≈x' , (y≈y' , z≈z')) , (x'≈x'' , (y'≈y'' , z'≈z''))) = 
               (≈X-trans x≈x' x'≈x'' , ≈Y-trans y≈y' y'≈y'') , ≈Z-trans z≈z' z'≈z''

          id⊆f : id ⊆ f
          id⊆f {((x , y) , z) , ((x' , y') , z')}
               ((x≈x' , y≈y') , z≈z') =
               (x , (y , z)) , ((≈X-refl {x} , ≈Y-refl {y} , ≈Z-refl {z})) , (x≈x' , y≈y' , z≈z')

      isoʳ : g-⇒ ≈X⊗[Y⊗Z]⇒X⊗[Y⊗Z] (Category.id CohL' {X⊗[Y⊗Z]}) 
      isoʳ = g⊆id , id⊆g
        where
          g = proj₁ g-⇒
          id = proj₁ $ Category.id CohL' {X⊗[Y⊗Z]}

          g⊆id : g ⊆ id
          g⊆id {((x , (y , z)) , (x'' , (y'' , z'')))} 
               (((x' , y') , z') , (x≈x' , y≈y' , z≈z') , (x'≈x'' , y'≈y'' , z'≈z'')) = 
               ≈X-trans x≈x' x'≈x'' , ≈Y-trans y≈y' y'≈y'' , ≈Z-trans z≈z' z'≈z''

          id⊆g : id ⊆ g
          id⊆g {(x , (y , z)) , (x' , (y' , z'))} (x≈x' , (y≈y' , z≈z')) 
               = (((x , y) , z)) , (≈X-refl {x} , ≈Y-refl {y} , ≈Z-refl {z}) , (x≈x' , y≈y' , z≈z')

  associator : [X⊗Y]⊗Z ≅CohL X⊗[Y⊗Z]
  associator = record
    { from = from-⇒ 
    ; to = to-⇒
    ; iso = iso
    }

module _ {X₁ Y₁ : Obj} 
         {f : X₁ ⇒ Y₁} 
         {X₂ Y₂ : Obj} 
         {g : X₂ ⇒ Y₂} 
         {X₃ Y₃ : Obj} 
         {h : X₃ ⇒ Y₃}
  where
    private
      _≈X₁⇒Y₁_ = CoherentSpace._≈_ (X₁ ⇒ₗ Y₁)
      _≈X₂⇒Y₂_ = CoherentSpace._≈_ (X₂ ⇒ₗ Y₂)
      _≈X₃⇒Y₃_ = CoherentSpace._≈_ (X₃ ⇒ₗ Y₃)

      f-resp-≈X₁⇒Y₁ : (proj₁ f) Respects _≈X₁⇒Y₁_
      f-resp-≈X₁⇒Y₁ = proj₂ $ proj₂ f

      g-resp-≈X₂⇒Y₂ : (proj₁ g) Respects _≈X₂⇒Y₂_
      g-resp-≈X₂⇒Y₂ = proj₂ $ proj₂ g

      h-resp-≈X₃⇒Y₃ : (proj₁ h) Respects _≈X₃⇒Y₃_
      h-resp-≈X₃⇒Y₃ = proj₂ $ proj₂ h

      X₁⊗X₂ : Obj
      X₁⊗X₂ = F₀ (X₁ , X₂)

      [X₁⊗X₂]⊗X₃ : Obj
      [X₁⊗X₂]⊗X₃ = F₀ (X₁⊗X₂ , X₃)

      Y₁⊗Y₂ : Obj
      Y₁⊗Y₂ = F₀ (Y₁ , Y₂)

      [Y₁⊗Y₂]⊗Y₃ : Obj
      [Y₁⊗Y₂]⊗Y₃ = F₀ (Y₁⊗Y₂ , Y₃)

      X₂⊗X₃ : Obj
      X₂⊗X₃ = F₀ (X₂ , X₃) 

      X₁⊗[X₂⊗X₃] : Obj
      X₁⊗[X₂⊗X₃] = F₀ (X₁ , X₂⊗X₃)

      Y₂⊗Y₃ : Obj
      Y₂⊗Y₃ = F₀ (Y₂ , Y₃)

      Y₁⊗[Y₂⊗Y₃] : Obj
      Y₁⊗[Y₂⊗Y₃] = F₀ (Y₁ , Y₂⊗Y₃)

      f⊗g : X₁⊗X₂ ⇒ Y₁⊗Y₂
      f⊗g = F₁ {X₁ , X₂} {Y₁ , Y₂} (f , g)

      g⊗h : X₂⊗X₃ ⇒ Y₂⊗Y₃
      g⊗h = F₁ {X₂ , X₃} {Y₂ , Y₃} (g , h)

      [f⊗g]⊗h : [X₁⊗X₂]⊗X₃ ⇒ [Y₁⊗Y₂]⊗Y₃
      [f⊗g]⊗h = F₁ {X₁⊗X₂ , X₃} {Y₁⊗Y₂ , Y₃} (f⊗g , h) 

      f⊗[g⊗h] : X₁⊗[X₂⊗X₃] ⇒ Y₁⊗[Y₂⊗Y₃]
      f⊗[g⊗h] = F₁ {X₁ , X₂⊗X₃} {Y₁ , Y₂⊗Y₃} (f , g⊗h)

    module _ where
      private
        fromX : [X₁⊗X₂]⊗X₃ ⇒ X₁⊗[X₂⊗X₃]
        fromX = _≅_.from (associator {X₁} {X₂} {X₃})

        fromY : [Y₁⊗Y₂]⊗Y₃ ⇒ Y₁⊗[Y₂⊗Y₃]
        fromY = _≅_.from (associator {Y₁} {Y₂} {Y₃})
        
        bottomLeft : [X₁⊗X₂]⊗X₃ ⇒ Y₁⊗[Y₂⊗Y₃]
        bottomLeft = CohL' ∣ [X₁⊗X₂]⊗X₃ ⇒ [Y₁⊗Y₂]⊗Y₃ ⇒ Y₁⊗[Y₂⊗Y₃] [ fromY ∘ [f⊗g]⊗h ]
  
        topRight : [X₁⊗X₂]⊗X₃ ⇒ Y₁⊗[Y₂⊗Y₃]
        topRight = CohL' ∣ [X₁⊗X₂]⊗X₃ ⇒ X₁⊗[X₂⊗X₃] ⇒ Y₁⊗[Y₂⊗Y₃] [ f⊗[g⊗h] ∘ fromX ]

      assoc-commute-from : CohL' ∣ [X₁⊗X₂]⊗X₃ ⇒ Y₁⊗[Y₂⊗Y₃] [ bottomLeft ≈ topRight ]
      assoc-commute-from = bl⊆tr , tr⊆bl
        where
          bl⊆tr : proj₁ bottomLeft ⊆ proj₁ topRight
          bl⊆tr {((x₁ , x₂) , x₃) , (y₁ , (y₂ , y₃))} 
                (((y₁' , y₂'), y₃') , ((x₁y₁'∈f , x₂y₂'∈g) , x₃y₃'∈h) , (y₁'≈y₁ , y₂'≈y₂ , y₃'≈y₃)) = 
                ((x₁ , (x₂ , x₃)) , (≈X₁-refl , ≈X₂-refl , ≈X₃-refl) , (x₁y₁∈f , x₂y₂∈g , x₃y₃∈h))
            where
              ≈X₁-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X₁)
              ≈X₂-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X₂)
              ≈X₃-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X₃)

              x₁y₁∈f : (x₁ , y₁) ∈ (proj₁ f)
              x₁y₁∈f = f-resp-≈X₁⇒Y₁ (≈X₁-refl , y₁'≈y₁) x₁y₁'∈f

              x₂y₂∈g : (x₂ , y₂) ∈ (proj₁ g)
              x₂y₂∈g = g-resp-≈X₂⇒Y₂ (≈X₂-refl , y₂'≈y₂) x₂y₂'∈g

              x₃y₃∈h : (x₃ , y₃) ∈ (proj₁ h)
              x₃y₃∈h = h-resp-≈X₃⇒Y₃ (≈X₃-refl , y₃'≈y₃) x₃y₃'∈h

          tr⊆bl : proj₁ topRight ⊆ proj₁ bottomLeft
          tr⊆bl {((x₁ , x₂) , x₃) , (y₁ , (y₂ , y₃))} 
                ((x₁' , (x₂' , x₃')) , (x₁≈x₁' , x₂≈x₂' , x₃≈x₃') , (x₁'y₁∈f , x₂'y₂∈g , x₃'y₃∈h)) = 
                (((y₁ , y₂) , y₃) , ((x₁y₁∈f , x₂y₂∈g) , x₃y₃∈h) , (≈Y₁-refl , ≈Y₂-refl , ≈Y₃-refl))
            where
              ≈Y₁-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y₁)
              ≈Y₂-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y₂)
              ≈Y₃-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y₃)

              ≈X₁-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X₁)
              ≈X₂-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X₂)
              ≈X₃-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X₃)

              x₁y₁∈f : (x₁ , y₁) ∈ (proj₁ f)
              x₁y₁∈f = f-resp-≈X₁⇒Y₁ (≈X₁-sym x₁≈x₁' , ≈Y₁-refl) x₁'y₁∈f

              x₂y₂∈g : (x₂ , y₂) ∈ (proj₁ g)
              x₂y₂∈g = g-resp-≈X₂⇒Y₂ (≈X₂-sym x₂≈x₂' , ≈Y₂-refl) x₂'y₂∈g

              x₃y₃∈h : (x₃ , y₃) ∈ (proj₁ h)
              x₃y₃∈h = h-resp-≈X₃⇒Y₃ (≈X₃-sym x₃≈x₃' , ≈Y₃-refl) x₃'y₃∈h

    module _ where
      private
        toX : X₁⊗[X₂⊗X₃] ⇒ [X₁⊗X₂]⊗X₃
        toX = _≅_.to (associator {X₁} {X₂} {X₃})

        toY : Y₁⊗[Y₂⊗Y₃] ⇒ [Y₁⊗Y₂]⊗Y₃
        toY = _≅_.to (associator {Y₁} {Y₂} {Y₃})

        bottomLeft : X₁⊗[X₂⊗X₃] ⇒ [Y₁⊗Y₂]⊗Y₃
        bottomLeft = CohL' ∣ X₁⊗[X₂⊗X₃] ⇒ Y₁⊗[Y₂⊗Y₃] ⇒ [Y₁⊗Y₂]⊗Y₃ [ toY ∘ f⊗[g⊗h] ]

        topRight : X₁⊗[X₂⊗X₃] ⇒ [Y₁⊗Y₂]⊗Y₃
        topRight = CohL' ∣ X₁⊗[X₂⊗X₃] ⇒ [X₁⊗X₂]⊗X₃ ⇒ [Y₁⊗Y₂]⊗Y₃ [ [f⊗g]⊗h ∘ toX ]

      assoc-commute-to : CohL' ∣ X₁⊗[X₂⊗X₃] ⇒ [Y₁⊗Y₂]⊗Y₃ [ bottomLeft ≈ topRight ]
      assoc-commute-to = bl⊆tr , tr⊆bl
        where
          bl⊆tr : proj₁ bottomLeft ⊆ proj₁ topRight
          bl⊆tr {(x₁ , (x₂ , x₃)) , ((y₁ , y₂) , y₃)} 
                ((y₁' , (y₂' , y₃')) , (x₁y₁'∈f , (x₂y₂'∈g , x₃y₃'∈h)) , (y₁'≈y₁ , y₂'≈y₂ , y₃'≈y₃)) = 
                (((x₁ , x₂) , x₃) , (≈X₁-refl , ≈X₂-refl , ≈X₃-refl) , ((x₁y₁∈f , x₂y₂∈g) , x₃y₃∈h))
            where
              ≈X₁-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X₁)
              ≈X₂-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X₂)
              ≈X₃-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X₃)

              x₁y₁∈f : (x₁ , y₁) ∈ (proj₁ f)
              x₁y₁∈f = f-resp-≈X₁⇒Y₁ (≈X₁-refl , y₁'≈y₁) x₁y₁'∈f

              x₂y₂∈g : (x₂ , y₂) ∈ (proj₁ g)
              x₂y₂∈g = g-resp-≈X₂⇒Y₂ (≈X₂-refl , y₂'≈y₂) x₂y₂'∈g

              x₃y₃∈h : (x₃ , y₃) ∈ (proj₁ h)
              x₃y₃∈h = h-resp-≈X₃⇒Y₃ (≈X₃-refl , y₃'≈y₃) x₃y₃'∈h

          tr⊆bl : proj₁ topRight ⊆ proj₁ bottomLeft
          tr⊆bl {(x₁ , (x₂ , x₃)) , ((y₁ , y₂) , y₃)} 
                (((x₁' , x₂') , x₃') , (x₁≈x₁' , x₂≈x₂' , x₃≈x₃') , ((x₁'y₁∈f , x₂'y₂∈g) , x₃'y₃∈h)) = 
                ((y₁ , (y₂ , y₃)) , (x₁y₁∈f , (x₂y₂∈g , x₃y₃∈h)) , (≈Y₁-refl , ≈Y₂-refl , ≈Y₃-refl))
            where
              ≈Y₁-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y₁)
              ≈Y₂-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y₂)
              ≈Y₃-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence Y₃)

              ≈X₁-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X₁)
              ≈X₂-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X₂)
              ≈X₃-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence X₃)

              x₁y₁∈f : (x₁ , y₁) ∈ (proj₁ f)
              x₁y₁∈f = f-resp-≈X₁⇒Y₁ (≈X₁-sym x₁≈x₁' , ≈Y₁-refl) x₁'y₁∈f

              x₂y₂∈g : (x₂ , y₂) ∈ (proj₁ g)
              x₂y₂∈g = g-resp-≈X₂⇒Y₂ (≈X₂-sym x₂≈x₂' , ≈Y₂-refl) x₂'y₂∈g

              x₃y₃∈h : (x₃ , y₃) ∈ (proj₁ h)
              x₃y₃∈h = h-resp-≈X₃⇒Y₃ (≈X₃-sym x₃≈x₃' , ≈Y₃-refl) x₃'y₃∈h
