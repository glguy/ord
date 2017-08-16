module Ord.Alt a where

open import Ord.Base a
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

mul : Ord → Ord → Ord
mul α β@(limit f) = ⨆ λ i → mul α (f i) + α

≤-same : ∀ α β → α ∙ β ≤ mul α β
≤-same (limit {A} f) (limit {B} g) (i , j) with g j | inspect g j
... | limit h | [ gj ] = (j , help) , next
  where
    help : ord-index (mul (limit f) (g j) ⊔ limit (λ i → mul (limit f) (g j) + f i))
    help rewrite gj = inj₂ i

    next :  limit (λ { (i₁ , j₁) → (( limit f ∙ h j₁)) + (f i₁)}) + f i
      ≤ subord (mul (limit f) (g j) ⊔ limit (λ i₁ → mul (limit f) (g j) + f i₁)) help
    next with g j
    ... | z = {!!}

