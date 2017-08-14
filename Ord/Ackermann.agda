module Ord.Ackermann where

import Level

lvl = Level.zero

open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Sum
open import Function
open import Ord.Arithmetic lvl
open import Ord.Base lvl
open import Ord.Nat lvl
open import Ord.RelProp lvl
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

open import Induction.WellFounded


sz : ℕ → ℕ → Ord
sz x y = ω ∙ ⌜ x ⌝ + ⌜ y ⌝

------------------------------------------------------------------------

smaller : ∀ m i j → sz m i < sz (ℕ.suc m) j
smaller m i j = lex₁ ω ⌜ m ⌝ ⌜ ℕ.suc m ⌝ ⌜ i ⌝ ⌜ j ⌝
                  (<-nat {m} ≤-refl)
                   (small-nat i)
  where
    open import Data.Nat.Properties using (≤-refl)

ackermann : (x y : ℕ) → Acc (_<_ on uncurry sz) (x , y) → ℕ
ackermann ℕ.zero n (acc rs) = ℕ.suc n
ackermann (ℕ.suc m) ℕ.zero (acc rs) = ackermann m 1 (rs _ (smaller m 1 0))

ackermann (ℕ.suc m) (ℕ.suc n) (acc rs) = ackermann m n′ (rs _ (smaller m n′ (ℕ.suc n)))
  where
    small : ω ∙ ⌜ ℕ.suc m ⌝ + ⌜ n ⌝ < ω ∙ ⌜ ℕ.suc m ⌝ + ⌜ ℕ.suc n ⌝
    small = inj₂ _ , ord-le-refl _

    n′ = ackermann (ℕ.suc m) n (rs _ small)

------------------------------------------------------------------------

ackermann′ : (x y : ℕ) (fuel : Ord) → fuel ≡ sz x y → ℕ

ackermann′ ℕ.zero n _ _ = ℕ.suc n

ackermann′ (ℕ.suc m) ℕ.zero (limit f) refl =
  let fuel = f (inj₁ (Level.lift 1 , _))
  in ackermann′ m 1 fuel refl

ackermann′ (ℕ.suc m) (ℕ.suc n) (limit f) refl =
  let fuel₁ = f (inj₂ _)
      n′    = ackermann′ (ℕ.suc m) n fuel₁ refl
      fuel₂ = f (inj₁ (Level.lift n′ , _))
  in ackermann′ m n′ fuel₂ refl


ackermann-ords : ℕ → ℕ → ℕ
ackermann-ords x y = ackermann′ x y (sz x y) refl
