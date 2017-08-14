module Ord.Ackermann where

import Level

lvl = Level.zero

open import Data.Product
open import Data.Sum
open import Ord.Base lvl
open import Ord.Nat lvl
open import Ord.Unnat lvl
open import Ord.RelProp lvl
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Data.Nat using (ℕ)
open import Function

open import Induction.WellFounded


sz : ℕ × ℕ → Ord
sz (x , y) = ω ∙ ⌜ x ⌝ + ⌜ y ⌝ ⌝

------------------------------------------------------------------------

smaller : ∀ m i j → ω ∙ ⌜ m ⌝ + ⌜ i ⌝ < ω ∙ ⌜ ℕ.suc m ⌝ + ⌜ j ⌝
smaller m i j = lex₁ ω ⌜ m ⌝ ⌜ ℕ.suc m ⌝ ⌜ i ⌝ ⌜ j ⌝
                  (<-nat {m} ≤-refl)
                   (small-nat i)
  where
    open import Data.Nat.Properties using (≤-refl)

ackermann : (x y : ℕ) → Acc (_<_ on sz) (x , y) → ℕ
ackermann ℕ.zero n (acc rs) = ℕ.suc n
ackermann (ℕ.suc m) ℕ.zero (acc rs) = ackermann m 1 (rs _ (smaller m 1 0))

ackermann (ℕ.suc m) (ℕ.suc n) (acc rs) = ackermann m n′ (rs _ (smaller m n′ (ℕ.suc n)))
  where
    small : ω ∙ nat (ℕ.suc m) + nat n < ω ∙ nat (ℕ.suc m) + nat (ℕ.suc n)
    small = inj₂ _ , ord-le-refl _

    n′ = ackermann (ℕ.suc m) n (rs _ small)

------------------------------------------------------------------------

ackermann′ : (x y : ℕ) (fuel : Ord) → fuel ≡ ω ∙ nat x + nat y → ℕ
ackermann′ ℕ.zero n _ _ = ℕ.suc n
ackermann′ (ℕ.suc m) ℕ.zero (limit f) refl =
  ackermann′ m 1 (f (inj₁ (Level.lift 1 , _))) refl
ackermann′ (ℕ.suc m) (ℕ.suc n) (limit f) refl =
  let n′ = ackermann′ (ℕ.suc m) n (f (inj₂ _)) refl
  in ackermann′ m n′ (f (inj₁ ((Level.lift n′) , _))) refl


ackermann-ords : ℕ → ℕ → ℕ
ackermann-ords x y = ackermann′ x y (sz (x , y)) refl
