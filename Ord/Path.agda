module Ord.Path a where

open import Ord.Base a
open import Ord.Pred a
open import Data.Product
open import Data.Nat using (ℕ)

data Path (o : Ord) : ℕ → Set a where
  done : Path o 0
  step : ∀ i n → Path (subord o i) n → Path o (ℕ.suc n)


less : ∀ α β → α ≤ β → ∀ {n} → Path α n → Path β n
less (limit f) (limit g) le done = done
less (limit f) (limit g) le (step i n p) =
  let x , y = le i
  in step x n (less (f i) (g x) y p)

-- back : ∀ α β → (∀ {n} → Path α n → Path β n) → α ≤ β
-- back (limit f) (limit g) k i with k (step i 0 done)
-- ... | step j m _ = j , back (f i) (g j) {!!}

smaller : ∀ α β γ → ascending-subs γ → α < γ → β < γ → α + β < γ
smaller (limit f) (limit g) (limit h) asc (i , α≤γi) (j , β≤γj)
  = ?
