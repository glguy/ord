open import Data.Empty using (⊥-elim)
open import Data.Product
open import Data.Sum
open import Data.Unit using (⊤)
open import Function
open import Level using (Level; lower; Lift; lift)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary

module Ord.Base (a : Level) where

data Ord : Set (Level.suc a) where
  limit : {A : Set a} → (A → Ord) → Ord

ord-index : Ord → Set a
ord-index (limit {A} _) = A

subord : (o : Ord) → ord-index o → Ord
subord (limit f) = f

_<_ : Rel Ord a
_≤_ : Rel Ord a

x < limit g = ∃ λ j → x ≤ g j
limit f ≤ y = ∀ i → f i < y

_≥_ : Rel Ord a
x ≥ y = y ≤ x

_>_ : Rel Ord a
x > y = y < x

_≰_ : Rel Ord a
x ≰ y = ¬ x ≤ y

_≱_ : Rel Ord a
x ≱ y = ¬ x ≥ y

_≮_ : Rel Ord a
x ≮ y = ¬ x < y

_≯_ : Rel Ord a
x ≯ y = ¬ x > y

_≈_ : Rel Ord a
x ≈ y = x ≤ y × y ≤ x

_≉_ : Rel Ord a
x ≉ y = ¬ x ≈ y

infix 4 _≈_ _<_ _>_ _≤_ _≥_ _≉_ _≮_ _≯_ _≰_ _≱_

------------------------------------------------------------------------

ord-lt-unfold : ∀ x y → (x < y) ≡ ∃ λ i → x ≤ subord y i
ord-lt-unfold _ (limit _) = refl

ord-le-unfold : ∀ x y → (x ≤ y) ≡ ∀ i → subord x i < y
ord-le-unfold (limit _) _ = refl

ord-lt-le : ∀ {x y} → x < y → x ≤ y
ord-lt-le {limit f} {limit g} (j , fi<gj) i with f i | ord-lt-le (fi<gj i)
... | limit fi | b = j , b

ord-le-refl : ∀ x → x ≤ x
ord-le-refl (limit f) i
  rewrite ord-lt-unfold (f i) (limit f)
  = i , ord-le-refl (f i)

------------------------------------------------------------------------

zero : Ord
zero = limit (⊥-elim ∘ lower)

suc : Ord → Ord
suc x = limit {Lift ⊤} λ _ → x

-- Least upper bound
_⊔_ : Ord → Ord → Ord
limit f ⊔ limit g = limit [ f , g ]

-- greatest lower bound
_⊓_ : Ord → Ord → Ord
limit f ⊓ limit g = limit λ { (i , j) → f i ⊓ g j }

-- Natural addition
_⊕_ : Ord → Ord → Ord
limit f ⊕ limit g =
  let recˡ = limit λ i → f i ⊕ limit g
      recʳ = limit λ j → limit f ⊕ g j
  in recˡ ⊔ recʳ

infixl 5 _⊔_ _⊓_
infixl 6 _⊕_
