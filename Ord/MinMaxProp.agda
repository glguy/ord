module Ord.MinMaxProp a where

open import Level using (lift)
open import Data.Sum
open import Data.Product
open import Ord.Base a
open import Ord.RelProp a
open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Algebra
open import Inverses
open import Function.Inverse

------------------------------------------------------------------------

⊔-mono-≤ : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
⊔-mono-≤ {limit _} {limit _} {limit _} {limit _} x≤y u≤v (inj₁ i)
  = let j , xi≤yj = x≤y i in inj₁ j , xi≤yj
⊔-mono-≤ {limit _} {limit _} {limit _} {limit _} x≤y u≤v (inj₂ i)
  = let j , ui≤vj = u≤v i in inj₂ j , ui≤vj

⊔-max : ∀ α β → β ≤ α ⊔ β
⊔-max (limit f) (limit g) i = inj₂ i , ord-le-refl _

⊔-pick : ∀ {α β} → α ≤ β → α ⊔ β ≈ β
⊔-pick {limit f} {limit g} le = [ (λ x → le x) , (λ x → x , (ord-le-refl _)) ] , ⊔-max (limit f) (limit g)

⊔-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _≈_ _⊔_ zero

IsMagma.isEquivalence
    (IsSemigroup.isMagma
       (IsCommutativeMonoid.isSemigroup
          (IsIdempotentCommutativeMonoid.isCommutativeMonoid
             ⊔-isIdempotentCommutativeMonoid)))
  = ≈-isEquivalence

IsIdempotentCommutativeMonoid.idem ⊔-isIdempotentCommutativeMonoid
  x = ⊔-pick (ord-le-refl x)

IsSemigroup.assoc
  (IsCommutativeMonoid.isSemigroup
    (IsIdempotentCommutativeMonoid.isCommutativeMonoid
       ⊔-isIdempotentCommutativeMonoid))
  (limit f) (limit g) (limit h) =
    limit-cong (left-inverse ⊎-assoc) [ ref f , [ ref g , ref h ] ]
  where
    open Inverse
    open Setoid ≈-setoid using (refl)

    ref : ∀ {A : Set a} (f : A → Ord) x → f x ≈ f x
    ref f x = refl

IsCommutativeMonoid.identityˡ
  (IsIdempotentCommutativeMonoid.isCommutativeMonoid
    ⊔-isIdempotentCommutativeMonoid)
  x = lem₁ x , lem₂ x
  where
    lem₁ : LeftIdentity _≤_ zero _⊔_
    lem₁ (limit f) (inj₁ (lift ()))
    lem₁ (limit f) (inj₂ i) = i , ord-le-refl (f i)

    lem₂ : LeftIdentity _≥_ zero _⊔_
    lem₂ (limit f) i = inj₂ i , ord-le-refl (f i)

IsCommutativeMonoid.comm
  (IsIdempotentCommutativeMonoid.isCommutativeMonoid
    ⊔-isIdempotentCommutativeMonoid)
  x y = lem x y , lem y x
  where
    lem : Commutative _≤_ _⊔_
    lem (limit f) (limit g) (inj₁ i) = inj₂ i , ord-le-refl (f i)
    lem (limit f) (limit g) (inj₂ i) = inj₁ i , ord-le-refl (g i)


IsMagma.∙-cong
  (IsSemigroup.isMagma
     (IsCommutativeMonoid.isSemigroup
        (IsIdempotentCommutativeMonoid.isCommutativeMonoid
           ⊔-isIdempotentCommutativeMonoid))) 
  (x≤y , y≤x) (u≤v , v≤u) = ⊔-mono-≤ x≤y u≤v , ⊔-mono-≤ y≤x v≤u

------------------------------------------------------------------------

⊓-comm : Commutative _≈_ _⊓_
⊓-comm x y = lem x y , lem y x
  where
    lem : Commutative _≤_ _⊓_
    lem (limit f) (limit g) (i , j) = (j , i) , lem (f i) (g j)


⊓-min : ∀ x y → x ⊓ y ≤ x
⊓-min (limit f) (limit g) (i , j) = i , ⊓-min (f i) (g j)

⊓-pick : ∀ {α β} → α ≤ β → α ⊓ β ≈ α
⊓-pick α≤β = ⊓-min _ _ , lem α≤β
  where
    lem : ∀ {α β} → α ≤ β → α ⊓ β ≥ α
    lem {α@(limit f)} {β@(limit g)} α≤β i =
      let x , y = α≤β i
      in (i , x) , lem y


⊓-leftZero : LeftZero _≈_ zero _⊓_
⊓-leftZero x = ⊓-pick (zero-least x)

⊓-idem : Idempotent _≈_ _⊓_
⊓-idem x = ⊓-pick (ord-le-refl x)

⊓-mono-≤ : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
⊓-mono-≤ {limit _} {limit _} {limit _} {limit _}
  x≤y u≤v (i , j) =
    let a , b = x≤y i
        c , d = u≤v j
    in (a , c) , ⊓-mono-≤ b d

------------------------------------------------------------------------

⊔-⊓-distrib : ∀ x y z → x ⊔ (y ⊓ z) ≈ (x ⊔ y) ⊓ (x ⊔ z)
⊔-⊓-distrib x y z = lem₁ x y z , lem₂ x y z
  where
    lem₁ : ∀ x y z → x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ (x ⊔ z)
    lem₁ (limit f) (limit g) (limit h) (inj₁ i) = (inj₁ i , inj₁ i) , proj₂ (⊓-idem _)
    lem₁ (limit f) (limit g) (limit h) (inj₂ (i , j)) = (inj₂ i , inj₂ j) , ord-le-refl _

    lem₂ : ∀ x y z → x ⊔ (y ⊓ z) ≥ (x ⊔ y) ⊓ (x ⊔ z)
    lem₂ (limit f) (limit g) (limit h) (inj₁ x , j) = (inj₁ x) , (⊓-min (f x) ([ f , h ] j))
    lem₂ (limit f) (limit g) (limit h) (inj₂ y , inj₁ x) = (inj₁ x) , ≤-≤-trans (proj₁ (⊓-comm (g y) (f x))) (⊓-min _ _)
    lem₂ (limit f) (limit g) (limit h) (inj₂ y , inj₂ y₁) = (inj₂ (y , y₁)) , ord-le-refl _

⊓-⊔-distrib : ∀ x y z → x ⊓ (y ⊔ z) ≈ (x ⊓ y) ⊔ (x ⊓ z)
⊓-⊔-distrib x y z = lem₁ x y z , lem₂ x y z
  where
    lem₁ : ∀ x y z → x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z)
    lem₁ (limit f) (limit g) (limit h) (i , inj₁ j) = inj₁ (i , j) , ord-le-refl _
    lem₁ (limit f) (limit g) (limit h) (i , inj₂ j) = inj₂ (i , j) , ord-le-refl _

    lem₂ : ∀ x y z → x ⊓ (y ⊔ z) ≥ (x ⊓ y) ⊔ (x ⊓ z)
    lem₂ (limit f) (limit g) (limit h) (inj₁ (i , j)) = (i , inj₁ j) , (ord-le-refl _)
    lem₂ (limit f) (limit g) (limit h) (inj₂ (i , j)) = (i , inj₂ j) , (ord-le-refl _)

⊓-isSemigroup : IsSemigroup _≈_ _⊓_

IsSemigroup.assoc ⊓-isSemigroup x y z = lem₁ x y z , lem₂ x y z
  where
    lem₁ : Associative _≤_ _⊓_
    lem₁ (limit f) (limit g) (limit h) ((i , j) , k)
      = (i , j , k) , lem₁ (f i) (g j) (h k)

    lem₂ : Associative _≥_ _⊓_
    lem₂ (limit f) (limit g) (limit h) (i , j , k)
      = ((i , j) , k) , lem₂ (f i) (g j) (h k)

IsMagma.isEquivalence (IsSemigroup.isMagma ⊓-isSemigroup) = ≈-isEquivalence


IsMagma.∙-cong (IsSemigroup.isMagma ⊓-isSemigroup) (x≤y , x≥y) (u≤v , u≥v)
  = ⊓-mono-≤ x≤y u≤v , ⊓-mono-≤ x≥y u≥v

------------------------------------------------------------------------

⊔-⊓-≤-absorb : ∀ x y → x ⊔ (x ⊓ y) ≤ x
⊔-⊓-≤-absorb (limit f) (limit g) (inj₁ i) = i , ord-le-refl _
⊔-⊓-≤-absorb (limit f) (limit g) (inj₂ (i , j)) = i , ⊓-min (f i) (g j)

⊔-⊓-≥-absorb : ∀ x y → x ⊔ (x ⊓ y) ≥ x
⊔-⊓-≥-absorb (limit f) (limit g) i = inj₁ i , ord-le-refl _

------------------------------------------------------------------------

⊔-commutativeMonoid : IdempotentCommutativeMonoid _ _
⊔-commutativeMonoid = record
  { Carrier = Ord; _≈_ = _≈_; _∙_ = _⊔_; ε = zero
  ; isIdempotentCommutativeMonoid = ⊔-isIdempotentCommutativeMonoid }

⊓-semigroup : Semigroup _ _
⊓-semigroup = record
  { Carrier = Ord ; _≈_ = _≈_ ; _∙_ = _⊓_
  ; isSemigroup = ⊓-isSemigroup }

⊔-⊓-isSemiringWithoutOne : IsSemiringWithoutOne _≈_ _⊔_ _⊓_ zero
IsSemiringWithoutOne.+-isCommutativeMonoid ⊔-⊓-isSemiringWithoutOne
  = IsIdempotentCommutativeMonoid.isCommutativeMonoid ⊔-isIdempotentCommutativeMonoid
IsSemiringWithoutOne.*-isSemigroup ⊔-⊓-isSemiringWithoutOne = ⊓-isSemigroup
IsSemiringWithoutOne.distrib ⊔-⊓-isSemiringWithoutOne =
  ⊓-⊔-distrib , (λ x y z →
    begin y ⊔ z ⊓ x ≈⟨ ⊓-comm _ _ ⟩
          x ⊓ (y ⊔ z) ≈⟨ ⊓-⊔-distrib _ _ _ ⟩
          x ⊓ y ⊔ (x ⊓ z) ≈⟨ IsIdempotentCommutativeMonoid.∙-cong
                               ⊔-isIdempotentCommutativeMonoid (⊓-comm _ _) (⊓-comm _ _) ⟩
          y ⊓ x ⊔ (z ⊓ x) ∎ )
  where
    open import Relation.Binary.EqReasoning ≈-setoid

IsSemiringWithoutOne.zero ⊔-⊓-isSemiringWithoutOne =
  ⊓-leftZero ,
  λ x → begin x ⊓ zero ≈⟨ ⊓-comm _ _ ⟩
              zero ⊓ x ≈⟨ ⊓-leftZero _ ⟩
              zero ∎
  where
    open import Relation.Binary.EqReasoning ≈-setoid

⊔-⊓-semiringWithoutOne : SemiringWithoutOne _ _
⊔-⊓-semiringWithoutOne = record
  { Carrier = Ord; _≈_ = _≈_; _+_ = _⊔_; _*_ = _⊓_; 0# = zero
  ; isSemiringWithoutOne = ⊔-⊓-isSemiringWithoutOne }
