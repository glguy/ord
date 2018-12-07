module Ord.Alt a where

open import Level using (lift)
open import Ord.Base a
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality


fold-ord : Ord → (Ord → Ord) → Ord → Ord
fold-ord z s (limit f) = z ⊔ (⨆ λ i → s (fold-ord z s (f i)))

add : Ord → Ord → Ord
add α = fold-ord α suc

+-same-≤ : ∀ α β → α + β ≤ add α β
+-same-≤ (limit {A} f) (limit {B} g) (inj₁ i) = inj₁ i , ord-le-refl _
+-same-≤ (limit {A} f) (limit {B} g) (inj₂ i) = inj₂ (i , _) , +-same-≤ (limit f) (g i)

+-same-≥ : ∀ α β → α + β ≥ add α β
+-same-≥ (limit {A} f) (limit {B} g) (inj₁ i) = inj₁ i , ord-le-refl _
+-same-≥ (limit {A} f) (limit {B} g) (inj₂ (i , _)) = inj₂ i , +-same-≥ (limit f) (g i)

mul : Ord → Ord → Ord
mul α = fold-ord zero (add α)

∙-same-≤ : ∀ α β → α ∙ β ≤ mul α β
∙-same-≤ (α@(limit {A} f)) (limit {B} g) (i , j) with g j | inspect g j
... | limit z | [ gj-def ] = (inj₂ (j , helper (g j))) , result gj-def
  where
    helper : ∀ γ → ord-index (add α (mul α γ))
    helper γ@(limit g) = inj₁ i

    result :
       ∀ {γ} → 
       γ ≡ limit z →
       (α ∙ limit z) + f i ≤
       subord (add (limit f) (mul α γ)) (helper γ)
    result refl = {!!}


∙-same-≥ : ∀ α β → α ∙ β ≥ mul α β
∙-same-≥ (limit {A} f) (limit {B} g) (inj₁ (lift ()))
∙-same-≥ α@(limit {A} f) (limit {B} g) (inj₂ (i , j)) = (index (g i) j , i) , {!!}
  where
    index : ∀ γ → ord-index (add α (mul α γ)) → A
    index (limit _) (inj₁ i) = i
    index (limit _) (inj₂ (inj₁ () , _))
    index (limit x) (inj₂ (inj₂ (i , j) , _)) = index (x i) j
