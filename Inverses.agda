module Inverses where

open import Function.Inverse
open import Data.Product
open import Data.Sum
open import Level
open import Level
open import Relation.Binary.PropositionalEquality

open Inverse
open _InverseOf_

Σ-assoc :
  ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
  Σ A (λ x → Σ (B x) (C x)) ↔ Σ (Σ A B) (uncurry C)
to Σ-assoc = →-to-⟶ λ { (x , y , z) → (x , y) , z}
from Σ-assoc = →-to-⟶ λ { ((x , y) , z) → x , y , z }
left-inverse-of (inverse-of Σ-assoc) _ = refl
right-inverse-of (inverse-of Σ-assoc) _ = refl

×-comm : ∀ {a b} {A : Set a} {B : Set b} → (A × B) ↔ (B × A)
to ×-comm =  →-to-⟶ Data.Product.swap
from ×-comm = →-to-⟶ Data.Product.swap
left-inverse-of (inverse-of ×-comm) _ = refl
right-inverse-of (inverse-of ×-comm) _ = refl

⊎-assoc :
  ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  ((A ⊎ B) ⊎ C) ↔ (A ⊎ (B ⊎ C))
to ⊎-assoc = →-to-⟶ λ
  { (inj₁ (inj₁ x)) → inj₁ x
  ; (inj₁ (inj₂ x)) → inj₂ (inj₁ x)
  ; (inj₂ x) → inj₂ (inj₂ x)}
from ⊎-assoc = →-to-⟶ λ
  { (inj₁ x) → inj₁ (inj₁ x)
  ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
  ; (inj₂ (inj₂ x)) → inj₂ x}
left-inverse-of (inverse-of ⊎-assoc) (inj₁ (inj₁ x)) = refl
left-inverse-of (inverse-of ⊎-assoc) (inj₁ (inj₂ y)) = refl
left-inverse-of (inverse-of ⊎-assoc) (inj₂ y) = refl
right-inverse-of (inverse-of ⊎-assoc) (inj₁ x) = refl
right-inverse-of (inverse-of ⊎-assoc) (inj₂ (inj₁ x)) = refl
right-inverse-of (inverse-of ⊎-assoc) (inj₂ (inj₂ y)) = refl

⊎-comm : ∀ {a b} {A : Set a} {B : Set b} → (A ⊎ B) ↔ (B ⊎ A)
to ⊎-comm =  →-to-⟶ ([_,_] inj₂ inj₁)
from ⊎-comm = →-to-⟶ ([_,_] inj₂ inj₁)
left-inverse-of (inverse-of ⊎-comm) = [_,_] (λ x → refl) (λ x → refl)
right-inverse-of (inverse-of ⊎-comm) = [_,_] (λ x → refl) (λ x → refl)
