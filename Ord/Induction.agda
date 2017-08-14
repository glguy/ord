module Ord.Induction a where

open import Ord.Base a

open import Induction

Ord-Rec : ∀ ℓ → RecStruct Ord ℓ _
Ord-Rec _ P f = ∀ i → P (subord f i)

Ord-rec-builder : ∀ {ℓ} → RecursorBuilder (Ord-Rec ℓ)
Ord-rec-builder P rec (limit g) i = rec (g i) (Ord-rec-builder P rec (g i))

