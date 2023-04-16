{-# OPTIONS --without-K  --allow-unsolved-metas #-}
open import Level

module Closed {c : Level} where

open import Function using (_$_)
open import Categories.Category
open import Categories.Category.Product
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Categories.Functor
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Functor.Bifunctor using (appˡ ; Bifunctor)
open import CoherentSpace using (CohL ; CoherentSpace ; _⇒'_ ; _⇒ₗ_)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Adjoint using (_⊣_)

open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred ; _⊆_ ; _∈_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary using (_Respects_ ; IsEquivalence ; Setoid)

open import Data.Product
open import Data.Sum using (inj₁ ; inj₂)

open import Lolli using (⊸ ; _⊸₀_ ; _⊸₁_)
open import Tensor using (⊗ ; _⊗₀_ ; _⊗₁_)
open import Monoidal {c} using (monoidal)

private
  CohL' = CohL {c}
  CoherentSpace' = Category.Obj CohL'
  open Category CohL' using (Obj ; _⇒_ )
  open Category (Product CohL' CohL') renaming (Obj to Obj² ; _⇒_ to _⇒²_) hiding (_≈_ ; _∘_) 
  open Monoidal monoidal using (-⊗_)

module _ {X : CoherentSpace'} where

  _⊗X⊣X⊸_ : (-⊗ X) ⊣ (appˡ ⊸ X)
  _⊗X⊣X⊸_ = record { unit = unit ; counit = counit ; zig = λ {A} → zig {A} ; zag = λ {A} → zag {A} }
    where
      _≈X_ = CoherentSpace._≈_ X
      _∼X_ = CoherentSpace._∼_ X
      _≁X_ = CoherentSpace._≁_ X
      ∼X-respˡ-≈X = CoherentSpace.∼-respˡ-≈ X
      ∼X-respʳ-≈X = CoherentSpace.∼-respʳ-≈ X

      unit : NaturalTransformation Categories.Functor.id (appˡ ⊸ X ∘F (-⊗ X)) 
      unit = record { η = η ; commute = commute ; sym-commute = sym-commute }
        where
          η : (A : CoherentSpace') → CohL' [ A , X ⊸₀ (A ⊗₀ X) ]
          --[[[
          η A = record { pred = pred ; isPoint = isPoint ; resp-≈ = resp-≈ }
            where
              _∼_ = CoherentSpace._∼_ $ A ⇒ₗ (X ⊸₀ (A ⊗₀ X))
              |A⇒⟨X⊸⟨A⊗X⟩⟩| = CoherentSpace.TokenSet $ A ⇒ₗ (X ⊸₀ (A ⊗₀ X))

              _≁⟨X⊸⟨A⊗X⟩⟩_ = CoherentSpace._≁_ (X ⊸₀ (A ⊗₀ X))
              _∼⟨X⊸⟨A⊗X⟩⟩_ = CoherentSpace._∼_ (X ⊸₀ (A ⊗₀ X))

              _∼A⊗X_ = CoherentSpace._∼_ (A ⊗₀ X)
              _≁A⊗X_ = CoherentSpace._≁_ (A ⊗₀ X)

              _≈A_ = CoherentSpace._≈_ A
              _≁A_ = CoherentSpace._≁_ A 
              _∼A_ = CoherentSpace._∼_ A
              ∼A-respˡ-≈A = CoherentSpace.∼-respˡ-≈ A
              ∼A-respʳ-≈A = CoherentSpace.∼-respʳ-≈ A

              pred : Pred (CoherentSpace.TokenSet $ A ⇒ₗ (X ⊸₀ (A ⊗₀ X))) _
              pred (a₀ , (x₀ , (a₁ , x₁))) = (a₀ ≈A a₁) × (x₀ ≈X x₁)
              
              isPoint : (p₀ p₁ : |A⇒⟨X⊸⟨A⊗X⟩⟩|) → pred p₀ → pred p₁ → p₀ ∼ p₁
              --[[[
              isPoint (a₀ , (x₀ , (a₁ , x₁))) (a₀' , (x₀' , (a₁' , x₁'))) (a₀≈a₁ , x₀≈x₁) (a₀'≈a₁' , x₀'≈x₁') 
                      = a₀∼a₀'→x₀a₁x₁∼x₀'a₁'x₁' , x₀a₁x₁≁x₀'a₁'x₁'→a₀≁a₀'
                where
                  a₀∼a₀'→x₀a₁x₁∼x₀'a₁'x₁' : a₀ ∼A a₀' → (x₀ , (a₁ , x₁)) ∼⟨X⊸⟨A⊗X⟩⟩ (x₀' , (a₁' , x₁'))
                  a₀∼a₀'→x₀a₁x₁∼x₀'a₁'x₁' a₀∼a₀' = x₀∼x₀'→a₁x₁∼x₁'x₁' , a₁x₁≁a₁'x₁'→x₀≁x₀'
                    where
                      a₁∼a₀' : a₁ ∼A a₀'
                      a₁∼a₀' = ∼A-respˡ-≈A a₀≈a₁ a₀∼a₀'

                      a₁∼a₁' : a₁ ∼A a₁'
                      a₁∼a₁' = ∼A-respʳ-≈A a₀'≈a₁' a₁∼a₀'

                      x₀∼x₀'→a₁x₁∼x₁'x₁' : x₀ ∼X x₀' → (a₁ , x₁) ∼A⊗X (a₁' , x₁')
                      x₀∼x₀'→a₁x₁∼x₁'x₁' x₀∼x₀' = a₁∼a₁' , x₁∼x₁'
                        where
                          x₁∼x₀' : x₁ ∼X x₀'
                          x₁∼x₀' = ∼X-respˡ-≈X x₀≈x₁ x₀∼x₀'

                          x₁∼x₁' : x₁ ∼X x₁'
                          x₁∼x₁' = ∼X-respʳ-≈X x₀'≈x₁' x₁∼x₀'

                      a₁x₁≁a₁'x₁'→x₀≁x₀' : (a₁ , x₁) ≁A⊗X (a₁' , x₁') → x₀ ≁X x₀'
                      a₁x₁≁a₁'x₁'→x₀≁x₀' (inj₁ (a₁≈a₁' , x₁≈x₁')) = inj₁ x₀≈x₀'
                        where
                          x₀≈x₀' : x₀ ≈X x₀'
                          x₀≈x₀' = begin
                              x₀ ≈⟨ x₀≈x₁ ⟩
                              x₁ ≈⟨ x₁≈x₁' ⟩
                              x₁' ≈˘⟨ x₀'≈x₁' ⟩
                              x₀' 
                            ∎
                            where
                              open SetoidReasoning (CoherentSpace.setoid X)
                      a₁x₁≁a₁'x₁'→x₀≁x₀' (inj₂ ¬a₁x₁∼a₁'x₁') = inj₂ ¬x₀∼x₀'
                        where
                          ¬x₀∼x₀' : ¬ (x₀ ∼X x₀')
                          ¬x₀∼x₀' x₀∼x₀' = ¬a₁x₁∼a₁'x₁' (a₁∼a₁' , x₁∼x₁')
                            where
                              x₁∼x₀' : x₁ ∼X x₀'
                              x₁∼x₀' = ∼X-respˡ-≈X x₀≈x₁ x₀∼x₀'

                              x₁∼x₁' : x₁ ∼X x₁'
                              x₁∼x₁' = ∼X-respʳ-≈X x₀'≈x₁' x₁∼x₀'
                  x₀a₁x₁≁x₀'a₁'x₁'→a₀≁a₀' : (x₀ , (a₁ , x₁)) ≁⟨X⊸⟨A⊗X⟩⟩ (x₀' , (a₁' , x₁')) → a₀ ≁A a₀'
                  x₀a₁x₁≁x₀'a₁'x₁'→a₀≁a₀' (inj₁ (x₀≈x₀' , (a₁≈a₁' , x₁≈x₁'))) = inj₁ a₀≈a₀' 
                    where
                      a₀≈a₀' : a₀ ≈A a₀'
                      a₀≈a₀' = begin
                          a₀ ≈⟨ a₀≈a₁ ⟩ 
                          a₁ ≈⟨ a₁≈a₁' ⟩ 
                          a₁' ≈˘⟨ a₀'≈a₁' ⟩
                          a₀'
                        ∎
                        where
                          open SetoidReasoning (CoherentSpace.setoid A)
                  x₀a₁x₁≁x₀'a₁'x₁'→a₀≁a₀' (inj₂ ¬x₀a₁x₁∼x₀'a₁'x₁') = inj₂ ¬a₀∼a₀'  
                    where
                      ¬a₀∼a₀' : ¬ (a₀ ∼A a₀')
                      ¬a₀∼a₀' a₀∼a₀' = ¬x₀a₁x₁∼x₀'a₁'x₁' (x₀∼x₀'→a₁x₁∼a₁'x₁' , a₁x₁≁a₁'x₁'→x₀≁x₀')
                        where
                          a₁∼a₁' : a₁ ∼A a₁'
                          a₁∼a₁' = ∼A-respˡ-≈A a₀≈a₁ (∼A-respʳ-≈A a₀'≈a₁' a₀∼a₀')

                          x₀∼x₀'→a₁x₁∼a₁'x₁' : x₀ ∼X x₀' → (a₁ , x₁) ∼A⊗X (a₁' , x₁')
                          x₀∼x₀'→a₁x₁∼a₁'x₁' x₀∼x₀' = a₁∼a₁' , x₁∼x₁'
                            where
                              x₁∼x₁' : x₁ ∼X x₁'
                              x₁∼x₁' = ∼X-respˡ-≈X x₀≈x₁ (∼X-respʳ-≈X x₀'≈x₁' x₀∼x₀')
                          a₁x₁≁a₁'x₁'→x₀≁x₀' : (a₁ , x₁) ≁A⊗X (a₁' , x₁') → x₀ ≁X x₀' 
                          a₁x₁≁a₁'x₁'→x₀≁x₀' (inj₁ (a₁≈a₁' , x₁≈x₁')) = inj₁ x₀≈x₀'
                            where
                              x₀≈x₀' : x₀ ≈X x₀'
                              x₀≈x₀' = begin
                                  x₀ ≈⟨ x₀≈x₁ ⟩
                                  x₁ ≈⟨ x₁≈x₁' ⟩
                                  x₁' ≈˘⟨ x₀'≈x₁' ⟩
                                  x₀'
                                ∎
                                where
                                  open SetoidReasoning (CoherentSpace.setoid X)
                          a₁x₁≁a₁'x₁'→x₀≁x₀' (inj₂ ¬a₁x₁∼a₁'x₁') = inj₂ ¬x₀∼x₀'
                            where
                              ¬x₀∼x₀' : ¬ x₀ ∼X x₀'
                              ¬x₀∼x₀' x₀∼x₀' = ¬a₁x₁∼a₁'x₁' (a₁∼a₁' , x₁∼x₁')
                                where
                                  x₁∼x₁' : x₁ ∼X x₁'
                                  x₁∼x₁' = ∼X-respˡ-≈X x₀≈x₁ (∼X-respʳ-≈X x₀'≈x₁' x₀∼x₀')
              --]]]

              resp-≈ : pred Respects (CoherentSpace._≈_ $ A ⇒ₗ (X ⊸₀ (A ⊗₀ X)))
              --[[[
              resp-≈ {(a₀ , (x₀ , (a₁ , x₁)))} 
                     {(a₀' , (x₀' , (a₁' , x₁')))} 
                     (a₀≈a₀' , (x₀≈x₀' , (a₁≈a₁' , x₁≈x₁'))) 
                     (a₀≈a₁ , x₀≈x₁) 
                     = a₀'≈a₁' , x₀'≈x₁'
                where
                  a₀'≈a₁' : a₀' ≈A a₁'
                  a₀'≈a₁' = begin
                      a₀' ≈˘⟨ a₀≈a₀' ⟩
                      a₀ ≈⟨ a₀≈a₁ ⟩
                      a₁ ≈⟨ a₁≈a₁' ⟩
                      a₁'
                    ∎
                    where
                      open SetoidReasoning (CoherentSpace.setoid A)
                  
                  x₀'≈x₁' : x₀' ≈X x₁'
                  x₀'≈x₁' = begin
                      x₀' ≈˘⟨ x₀≈x₀' ⟩
                      x₀ ≈⟨ x₀≈x₁ ⟩
                      x₁ ≈⟨ x₁≈x₁' ⟩
                      x₁'
                    ∎
                    where
                      open SetoidReasoning (CoherentSpace.setoid X)
              --]]]
          --]]]

          _∘_ = _[_∘_] CohL'
          
          module _ {A B : CoherentSpace'} (f : CohL' [ A , B ]) where
            private
              _≈A⊗B_ = CoherentSpace._≈_ (A ⊗₀ B)
              X⊸⟨f⊗X⟩ = Functor.F₁ (appˡ ⊸ X ∘F (-⊗ X)) f
              ≈A-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence A)
              ≈A-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence A)
              ≈B-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence B)
              ≈B-sym = IsEquivalence.sym (CoherentSpace.≈-isEquivalence B)
              ≈X-refl = IsEquivalence.refl (CoherentSpace.≈-isEquivalence X)
              open _⇒'_

            commute : CohL' [ (η B ∘ f) ≈ (X⊸⟨f⊗X⟩ ∘ η A) ]
            --[[[
            commute = η∘f⊆⟨X⊸⟨f⊗X⟩⟩∘η , ⟨X⊸⟨f⊗X⟩⟩∘η⊆η∘f
              where
                η∘f⊆⟨X⊸⟨f⊗X⟩⟩∘η : pred (η B ∘ f) ⊆ pred (X⊸⟨f⊗X⟩ ∘ η A)
                η∘f⊆⟨X⊸⟨f⊗X⟩⟩∘η {a , (x₀ , (b , x₁))} (b' , (ab'∈f , (b'≈b , x₀≈x₁))) 
                                 = (x₀ , (a , x₁)) , (≈A-refl {a} , x₀≈x₁) , (≈X-refl {x₀} , (ab∈f , ≈X-refl {x₁}))
                  where
                    ab≈ab' : (a , b') ≈A⊗B (a , b)
                    ab≈ab' = ≈A-refl {a} , b'≈b

                    ab∈f : (a , b) ∈ pred f
                    ab∈f = resp-≈ f ab≈ab' ab'∈f

                ⟨X⊸⟨f⊗X⟩⟩∘η⊆η∘f : pred (X⊸⟨f⊗X⟩ ∘ η A) ⊆ pred (η B ∘ f)
                ⟨X⊸⟨f⊗X⟩⟩∘η⊆η∘f {a , (x₀ , (b , x₁))} 
                                ((x₀' , (a' , x₁')) , (a≈a' , x₀'≈x₁') , (x₀≈x₀' , a'b∈f , x₁'≈x₁)) 
                                = b , ab∈f , (≈B-refl {b} , x₀≈x₁)
                  where
                    a'b≈ab : (a' , b) ≈A⊗B (a , b)
                    a'b≈ab = ≈A-sym a≈a' , ≈B-refl {b}

                    ab∈f : (a , b) ∈ pred f
                    ab∈f = resp-≈ f a'b≈ab a'b∈f

                    x₀≈x₁ : x₀ ≈X x₁
                    x₀≈x₁ = begin
                        x₀ ≈⟨ x₀≈x₀' ⟩
                        x₀' ≈⟨ x₀'≈x₁' ⟩
                        x₁' ≈⟨ x₁'≈x₁ ⟩
                        x₁ 
                      ∎
                      where
                        open SetoidReasoning (CoherentSpace.setoid X)
            --]]]

            sym-commute : CohL' [ (X⊸⟨f⊗X⟩ ∘ η A) ≈ (η B ∘ f) ]
            sym-commute = sym {η B ∘ f} {X⊸⟨f⊗X⟩ ∘ η A} commute
              where 
                open IsEquivalence (Category.equiv CohL' {A} {X ⊸₀ (B ⊗₀ X)})

      counit : NaturalTransformation ((-⊗ X) ∘F appˡ ⊸ X) Categories.Functor.id
      counit = record { η = η ; commute = {!!} ; sym-commute = {!!} }
        where
          η : (A : CoherentSpace') → CohL' [ (X ⊸₀ A) ⊗₀ X , A ]
          η A = {!!}

      zig : {A : CoherentSpace'} → CohL' [ CohL' [ NaturalTransformation.η counit (A ⊗₀ X) ∘ Functor.F₁ (-⊗ X) (NaturalTransformation.η unit A) ] ≈ Category.id CohL' {A ⊗₀ X} ]
      zig {A} = {!!}

      zag : {A : CoherentSpace'} → CohL' [ CohL' [ Functor.F₁ (appˡ ⊸ X) (NaturalTransformation.η counit A) ∘ NaturalTransformation.η unit (Functor.F₀ (appˡ ⊸ X) A) ] ≈ Category.id CohL' {X ⊸₀ A} ]
      zag {A} = {!!}

closed : Closed monoidal
closed = record
  { [-,-]   = ⊸
  ; adjoint = λ {X} → _⊗X⊣X⊸_ {X}
  ; mate = {!!}
  }
    
