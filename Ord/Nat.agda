module Ord.Nat a where

open import Level using (lower; lift)
open import Ord.Base a
open import Ord.RelProp a
open import Data.Nat using (fold; ℕ; z≤n; s≤s) renaming (_≤_ to _ℕ-≤_; _<_ to _ℕ-<_)
open import Function
open import Data.Product

⌜_⌝ : ℕ → Ord
⌜_⌝ = fold zero suc

one : Ord
one = ⌜ 1 ⌝

ω : Ord
ω = limit (⌜_⌝ ∘ lower)

small-nat : ∀ i → ⌜ i ⌝ < ω
small-nat i = lift i , ord-le-refl _

≤-nat : ∀ {x y} → x ℕ-≤ y → ⌜ x ⌝ ≤ ⌜ y ⌝
≤-nat z≤n = zero-least _
≤-nat (s≤s le) _ = , ≤-nat le

<-nat : ∀ {x y} → x ℕ-< y → ⌜ x ⌝ < ⌜ y ⌝
<-nat (s≤s lt) = , ≤-nat lt
