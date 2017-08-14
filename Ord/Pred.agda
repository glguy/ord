module Ord.Pred a where

open import Ord.Base a
open import Ord.RelProp a

open import Data.Product

has-maximum-sub = λ (o : Ord) → ∃ λ i → ∀ j → subord o i ≥ subord o j
accending-subs  = λ (o : Ord) → ∀ i → ∃ λ j → subord o i < subord o j

pred : Ord → Ord
pred o = limit λ { (i , j) → subord (subord o i) j }

pred-most : ∀ x y → x < y → x ≤ pred y
pred-most (limit f) (limit g) (j , limf<gj) i with limf<gj i
... | ab rewrite ord-lt-unfold (f i) (g j) = (j , proj₁ ab) , proj₂ ab

subord-smaller : ∀ x y → subord x y < x
subord-smaller (limit f) i = i , ord-le-refl (f i)

pred-smaller : (o : Ord) → has-maximum-sub o → pred o < o
pred-smaller (limit f) (i , max) =
  i , λ { (j , o) → <-≤-trans (subord-smaller (f j) o) (max j) }

pred-≤ : (o : Ord) → pred o ≤ o
pred-≤ (limit f) (i , j) = i , ord-lt-le (subord-smaller (f i) j)

pred-≥ : (o : Ord) → accending-subs o → pred o ≥ o
pred-≥ (limit f) asc i with asc i
... | y , z rewrite ord-lt-unfold (f i) (f y) = (y , proj₁ z) , proj₂ z

pred-≈ : (o : Ord) → accending-subs o → pred o ≈ o
pred-≈ o asc = pred-≤ o , pred-≥ o asc

