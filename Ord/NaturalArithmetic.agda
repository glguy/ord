module Ord.NaturalArithmetic a where

open import Level using (lift)
open import Ord.Base a
open import Ord.RelProp a
open import Data.Sum
open import Data.Product
open import Algebra
open import Algebra.FunctionProperties
open import Algebra.Structures

⊕-isCommutativeMonoid : IsCommutativeMonoid _≈_ _⊕_ zero

≤-⊕-cong : Congruent₂ _≤_ _⊕_
≤-⊕-cong {limit _} {limit _} {limit _} {limit _} x≤y u≤v (inj₁ i)
  = let j , xᵢ≤yⱼ = x≤y i in inj₁ j , ≤-⊕-cong xᵢ≤yⱼ u≤v
≤-⊕-cong {limit f₁} {limit g₁} {limit f₂} {limit g₂} x≤y u≤v (inj₂ i)
  = let j , uᵢ≤vⱼ = u≤v i in inj₂ j , ≤-⊕-cong x≤y uᵢ≤vⱼ

IsMagma.isEquivalence (IsSemigroup.isMagma (IsCommutativeMonoid.isSemigroup ⊕-isCommutativeMonoid))
  = ≈-isEquivalence

IsSemigroup.assoc (IsCommutativeMonoid.isSemigroup ⊕-isCommutativeMonoid) x y z
  = lem₁ x y z , lem₂ x y z
  where
    lem₁ : Associative _≤_ _⊕_
    lem₁ (limit f) (limit g) (limit h) (inj₁ (inj₁ i)) = inj₁ i        , lem₁ (f i) (limit g) (limit h)
    lem₁ (limit f) (limit g) (limit h) (inj₁ (inj₂ j)) = inj₂ (inj₁ j) , lem₁ (limit f) (g j) (limit h)
    lem₁ (limit f) (limit g) (limit h) (inj₂ k)        = inj₂ (inj₂ k) , lem₁ (limit f) (limit g) (h k)

    lem₂ : Associative _≥_ _⊕_
    lem₂ (limit f) (limit g) (limit h) (inj₁ i)        = inj₁ (inj₁ i) , lem₂ (f i) (limit g) (limit h)
    lem₂ (limit f) (limit g) (limit h) (inj₂ (inj₁ j)) = inj₁ (inj₂ j) , lem₂ (limit f) (g j) (limit h)
    lem₂ (limit f) (limit g) (limit h) (inj₂ (inj₂ k)) = inj₂ k        , lem₂ (limit f) (limit g) (h k)

IsMagma.∙-cong (IsSemigroup.isMagma (IsCommutativeMonoid.isSemigroup ⊕-isCommutativeMonoid)) (x≤y , y≤x) (u≤v , v≤u) = ≤-⊕-cong x≤y u≤v , ≤-⊕-cong y≤x v≤u

IsCommutativeMonoid.identityˡ ⊕-isCommutativeMonoid x = lem₁ x , lem₂ x
  where
    lem₁ : LeftIdentity _≤_ zero _⊕_
    lem₁ (limit _) (inj₁ (lift ()))
    lem₁ (limit f) (inj₂ i) = i , lem₁ (f i)

    lem₂ : LeftIdentity _≥_ zero _⊕_
    lem₂ (limit f) i = inj₂ i , lem₂ (f i)

IsCommutativeMonoid.comm ⊕-isCommutativeMonoid x y = lem x y , lem y x
  where
    lem : Commutative _≤_ _⊕_
    lem (limit f) (limit g) (inj₁ i) = inj₂ i , lem (f i) (limit g)
    lem (limit f) (limit g) (inj₂ j) = inj₁ j , lem (limit f) (g j)

⊕-commutativeMonoid : CommutativeMonoid _ _
⊕-commutativeMonoid = record
  { Carrier = Ord; _≈_ = _≈_; _∙_ = _⊕_; ε = zero
  ; isCommutativeMonoid = ⊕-isCommutativeMonoid }

------------------------------------------------------------------------


suc-⊕-comm : ∀ x y → suc x ⊕ y ≈ suc (x ⊕ y)
suc-⊕-comm x y = lem₁ x y , lem₂ x y
  where
    lem₁ : ∀ x y → suc x ⊕ y ≤ suc (x ⊕ y)
    lem₁ (limit f) (limit g) (inj₁ _) = _ , [ (λ i → inj₁ i , ord-le-refl _) , (λ i → inj₂ i , ord-le-refl _) ]
    lem₁ (limit f) (limit g) (inj₂ i) = _ , ≤-≤-trans (lem₁ (limit f) (g i)) (λ _ → inj₂ i , ord-le-refl _)

    lem₂ : ∀ x y → suc x ⊕ y ≥ suc (x ⊕ y)
    lem₂ (limit f) (limit g) _ = inj₁ _ , [ (λ i → inj₁ i , ord-le-refl _) , (λ i → inj₂ i , ord-le-refl _) ]

-- _⊗_ : Ord → Ord → Ord
-- limit f ⊗ limit g
--   = limit (λ i → f i ⊗ limit g) ⊕ limit f
--   ⊔ limit (λ i → limit f ⊗ g i) ⊕ limit g
-- 
-- open import Relation.Binary.PartialOrderReasoning ≤-poset
-- 
-- dist : ∀ x y z → x ⊗ (y ⊕ z) ≤ x ⊗ y ⊕ x ⊗ z
-- dist (limit f) (limit g) (limit h) (inj₁ (inj₁ i)) = (inj₁ (inj₁ (inj₁ i))) , (
--   begin f i ⊗ (limit g ⊕ limit h) ⊕ limit f ≤⟨ {!!} ⟩
-- 
--       f i ⊗ limit g ⊕ limit f ⊕ limit f ⊗ limit h ∎)
-- dist (limit f) (limit g) (limit h) (inj₁ (inj₂ i)) = {!!}
-- dist (limit f) (limit g) (limit h) (inj₂ (inj₁ (inj₁ i))) = (inj₁ (inj₂ {!!})) , {!!}
-- dist (limit f) (limit g) (limit h) (inj₂ (inj₁ (inj₂ i))) = {!!}
-- dist (limit f) (limit g) (limit h) (inj₂ (inj₂ i)) = {!!}
