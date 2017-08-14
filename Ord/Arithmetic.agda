module Ord.Arithmetic a where

open import Ord.Base a
open import Function
open import Level using (lower; lift)
open import Ord.RelProp a
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Ord.MinMaxProp a
open import Ord.Nat a
open import Algebra.Structures
open import Relation.Nullary
open import Relation.Binary

+-≤-cong : ∀ {x y u v} → x ≤ y → u ≤ v → x + u ≤ y + v
+-≤-cong {limit _} {limit _} {limit _} {limit _} x≤y u≤v =
  ⊔-≤-cong x≤y (λ i → (proj₁ (u≤v i)) , +-≤-cong x≤y (proj₂ (u≤v i)))

∙-≤-cong : ∀ {x y u v} → x ≤ y → u ≤ v → x ∙ u ≤ y ∙ v
∙-≤-cong {limit e} {limit f} {limit g} {limit h} x≤y u≤v (i , j) =
  let a , ei≤fa = x≤y i
      c , gj≤hc = u≤v j
  in (a , c) , +-≤-cong (∙-≤-cong x≤y gj≤hc) ei≤fa


+-isMonoid : IsMonoid _≈_ _+_ zero

IsSemigroup.isEquivalence (IsMonoid.isSemigroup +-isMonoid) = ≈-isEquivalence

IsSemigroup.assoc (IsMonoid.isSemigroup +-isMonoid) α β γ = lem₁ α β γ , lem₂ α β γ
  where
    lem₁ : ∀ α β γ → (α + β) + γ ≤ α + (β + γ)
    lem₁ (limit f) (limit g) (limit h) (inj₁ (inj₁ i)) = (inj₁ i) , (ord-le-refl _)
    lem₁ (limit f) (limit g) (limit h) (inj₁ (inj₂ i)) = (inj₂ (inj₁ i)) , (ord-le-refl _)
    lem₁ (limit f) (limit g) (limit h) (inj₂ i) = (inj₂ (inj₂ i)) , lem₁ _ _ (h i)

    lem₂ : ∀ α β γ → (α + β) + γ ≥ α + (β + γ)
    lem₂ (limit f) (limit g) (limit h) (inj₁ i) = (inj₁ (inj₁ i)) , (ord-le-refl _)
    lem₂ (limit f) (limit g) (limit h) (inj₂ (inj₁ i)) = (inj₁ (inj₂ i)) , (ord-le-refl _)
    lem₂ (limit f) (limit g) (limit h) (inj₂ (inj₂ i)) = (inj₂ i) , lem₂ _ _ (h i)


IsSemigroup.∙-cong (IsMonoid.isSemigroup +-isMonoid)
  (x≤y , y≤x) (u≤v , v≤u) = +-≤-cong x≤y u≤v , +-≤-cong y≤x v≤u

IsMonoid.identity +-isMonoid = +-identityˡ , +-identityʳ
  where
    +-identityʳ : ∀ x → x + zero ≈ x
    +-identityʳ x = lem₁ x , lem₂ x
      where
        lem₁ : ∀ x → x + zero ≤ x
        lem₁ x@(limit f) (inj₁ i) = i , (ord-le-refl _)
        lem₁ x@(limit f) (inj₂ (lift ()))
        lem₂ : ∀ x → x + zero ≥ x
        lem₂ x@(limit f) i = (inj₁ i) , (ord-le-refl _)

    +-identityˡ : ∀ x → zero + x ≈ x
    +-identityˡ x = lem₁ x , lem₂ x
      where
        lem₁ : ∀ x → zero + x ≤ x
        lem₁ x@(limit f) (inj₁ ())
        lem₁ x@(limit f) (inj₂ i) = i , (lem₁ (f i))
        lem₂ : ∀ x → zero + x ≥ x
        lem₂ x@(limit f) i = (inj₂ i) , (lem₂ (f i))


+-≤-<-cong : ∀ {β₁ β₂ γ₁ γ₂} → β₁ ≤ β₂ → γ₁ < γ₂ → β₁ + γ₁ < β₂ + γ₂
+-≤-<-cong {β₁@(limit g₁)} {β₂@(limit g₂)} {limit h₁} {limit h₂} β₁≤β₂ (j , h₁_<h₂j) =
  let rec = λ x → +-≤-<-cong β₁≤β₂ (h₁ x <h₂j)
  in inj₂ j , [ lem , rec ]
  where
    open import Relation.Binary.PartialOrderReasoning ≤-poset
    open IsMonoid +-isMonoid

    lem : β₁ ≤ β₂ + h₂ j
    lem = begin β₁ ≤⟨ proj₂ (proj₂ identity β₁) ⟩
                 β₁ + zero ≤⟨ +-≤-cong β₁≤β₂ (zero-least (h₂ j)) ⟩
                 β₂ + h₂ j ∎


+-∙-dist : ∀ α β γ → α ∙ (β + γ) ≈ α ∙ β + α ∙ γ
+-∙-dist α β γ = lem₁ α β γ , lem₂ α β γ
  where
    lem₁ : ∀ α β γ → α ∙ (β + γ) ≤ α ∙ β + α ∙ γ
    lem₁ (limit f) (limit g) (limit h) (i , inj₁ j) = (inj₁ (i , j)) , (ord-le-refl _)
    lem₁ x@(limit f) y@(limit g) z@(limit h) (i , inj₂ j) = (inj₂ (i , j)) ,
       (begin x ∙ (y + h j) + f i ≤⟨ +-≤-cong (lem₁ x y (h j)) (ord-le-refl (f i)) ⟩
              x ∙ y + x ∙ h j + f i ≤⟨ proj₁ (assoc (x ∙ y) (x ∙ h j) (f i)) ⟩
              x ∙ y + (x ∙ h j + f i) ∎)
      where
        open import Relation.Binary.PartialOrderReasoning ≤-poset
        open IsMonoid +-isMonoid

    lem₂ : ∀ α β γ → α ∙ (β + γ) ≥ α ∙ β + α ∙ γ
    lem₂ (limit f) (limit g) (limit h) (inj₁ (i , j)) = (i , inj₁ j) , (ord-le-refl _)
    lem₂ α@(limit f) β@(limit g) γ@(limit h) (inj₂ (i , j)) = (i , inj₂ j) ,
       (begin α ∙ β + (α ∙ h j + f i) ≤⟨ proj₂ (assoc (α ∙ β) (α ∙ h j) (f i)) ⟩
              α ∙ β + α ∙ h j + f i ≤⟨ +-≤-cong (lem₂ α β (h j)) (ord-le-refl (f i))  ⟩
              α ∙ (β + h j) + f i ∎)
      where
        open IsMonoid +-isMonoid
        open import Relation.Binary.PartialOrderReasoning ≤-poset



¬‿+-comm : ∃₂ λ α β → α + β ≰ β + α
¬‿+-comm = ω , one , λ ω+1≤1+ω →  <-irref P.refl (≤-<-trans ω+1≤1+ω (≤-<-trans counter counter₂))
  where
    import Data.Nat as ℕ
    import Relation.Binary.PropositionalEquality as P
    open import Relation.Binary.StrictPartialOrderReasoning <-strictPartialOrder
    open Setoid ≈-setoid

    0<1 : zero < one
    0<1 = , zero-least _

    go : ∀ i → one + ⌜ i ⌝ ≤ ⌜ ℕ.suc i ⌝
    go ℕ.zero (inj₁ _) = , zero-least _
    go ℕ.zero (inj₂ ())
    go (ℕ.suc i) (inj₁ _) = , zero-least _
    go (ℕ.suc i) (inj₂ _) = , go i

    counter : one + ω ≤ ω
    counter (inj₁ _) = lift 0 , zero-least _
    counter (inj₂ (lift i)) = lift (ℕ.suc i) , go i

    counter₂ : ω < ω + one
    counter₂ = from-inj₁
             $ begin ω        ≈⟨ Setoid.sym ≈-setoid (proj₂ identity ω) ⟩
                     ω + zero <⟨ +-≤-<-cong (ord-le-refl ω) 0<1 ⟩
                     ω + one ∎
      where
        open IsMonoid +-isMonoid

∙-zeroˡ : ∀ α → zero ∙ α ≤ zero
∙-zeroˡ α@(limit f) (lift () , _)

∙-zeroʳ : ∀ α → α ∙ zero ≤ zero
∙-zeroʳ α@(limit f) (_ , lift ())

∙-isMonoid : IsMonoid _≈_ _∙_ one
IsSemigroup.isEquivalence (IsMonoid.isSemigroup ∙-isMonoid) = ≈-isEquivalence
IsSemigroup.assoc         (IsMonoid.isSemigroup ∙-isMonoid)
  α β γ = lem₁ α β γ , lem₂ α β γ
  where
    lem₁ : ∀ α β γ → (α ∙ β) ∙ γ ≤ α ∙ (β ∙ γ)

    lem₁ α@(limit f) β@(limit g) γ@(limit h) ((i , j) , k) = (i , j , k) ,
          (begin α ∙  β ∙ h k  + (α ∙ g j + f i) ≤⟨ +-≤-cong (lem₁ α β (h k)) (ord-le-refl (α ∙ g j + f i)) ⟩
                 α ∙ (β ∙ h k) + (α ∙ g j + f i) ≤⟨ proj₂ (assoc (α ∙ (β ∙ h k)) (α ∙ g j) (f i)) ⟩
              α ∙ (β ∙ h k) + α ∙ g j + f i
                  ≤⟨ +-≤-cong ( proj₂ (+-∙-dist α (β ∙ h k) (g j))  ) (ord-le-refl (f i)) ⟩
              α ∙ (β ∙ h k + g j) + f i ∎)
     where
       open import Relation.Binary.PartialOrderReasoning ≤-poset
       open IsMonoid +-isMonoid

    lem₂ : ∀ α β γ → (α ∙ β) ∙ γ ≥ α ∙ (β ∙ γ)
    lem₂ α@(limit f) β@(limit g) γ@(limit h) (i , j , k) = ((i , j) , k) ,
       (begin α ∙ (β ∙ h k + g j) + f i ≤⟨ +-≤-cong (proj₁ (+-∙-dist α (β ∙ h k) (g j))) (ord-le-refl (f i)) ⟩
              α ∙ (β ∙ h k) + α ∙ g j + f i ≤⟨ proj₁ (assoc (α ∙ (β ∙ h k)) (α ∙ g j) (f i)) ⟩
              α ∙ (β ∙ h k) + (α ∙ g j + f i) ≤⟨ +-≤-cong (lem₂ α β (h k)) (ord-le-refl (α ∙ g j + f i)) ⟩
              α ∙ β ∙ h k + (α ∙ g j + f i) ∎)
     where
       open import Relation.Binary.PartialOrderReasoning ≤-poset
       open IsMonoid +-isMonoid


IsSemigroup.∙-cong (IsMonoid.isSemigroup ∙-isMonoid)
  (x≤y , y≤x) (u≤v , v≤u) = ∙-≤-cong x≤y u≤v , ∙-≤-cong y≤x v≤u

IsMonoid.identity ∙-isMonoid = (λ α → lem₁ α , lem₂ α) , (λ α → lem₃ α , lem₄ α)
  where
    open import Relation.Binary.PartialOrderReasoning ≤-poset
    open IsMonoid +-isMonoid

    lem₁ : ∀ α → one ∙ α ≤ α
    lem₁ α@(limit f) (_ , i) = i ,
      (begin
         one ∙ f i + zero ≤⟨ proj₁ (proj₂ identity (one ∙ f i)) ⟩
         one ∙ f i  ≤⟨ lem₁ (f i) ⟩
         f i ∎)

    lem₂ : ∀ α → one ∙ α ≥ α
    lem₂ α@(limit f) i = (_ , i) ,
       (begin f i ≤⟨ lem₂ (f i) ⟩
             one ∙ f i ≤⟨ proj₂ (proj₂ identity (one ∙ f i)) ⟩
             one ∙ f i + zero ∎)

    lem₃ : ∀ α → α ∙ one ≤ α
    lem₃ α@(limit f) (i , _) = i ,
       (begin α ∙ zero + f i ≤⟨ +-≤-cong (∙-zeroʳ α) (ord-le-refl (f i)) ⟩
              zero + f i ≤⟨ proj₁ (proj₁ identity (f i)) ⟩
              f i ∎)

    lem₄ : ∀ α → α ∙ one ≥ α
    lem₄ α@(limit f) i = (i , _) ,
       (begin f i ≤⟨ proj₂ (proj₁ identity (f i)) ⟩
              zero + f i ≤⟨ +-≤-cong (zero-least (α ∙ zero)) (ord-le-refl (f i)) ⟩ α ∙ zero + f i ∎)



-- ^-+-dist : ∀ α β γ → (α ^ β) ^ γ ≈ α ^ (β ∙ γ)
-- ^-+-dist α β γ = lem₁ α β γ , lem₂ α β γ
--   where
--     lem₁ : ∀ α β γ → (α ^ β) ^ γ ≤ α ^ (β ∙ γ)
--     lem₁ α@(limit f) β@(limit g) γ@(limit h) (inj₁ i) = (inj₁ _) , (⊥-elim ∘ lower)
--     lem₁ α@(limit f) β@(limit g) γ@(limit h) (inj₂ (inj₁ i , j , k))  = inj₁ _ , {!!}
--     lem₁ α@(limit f) β@(limit g) γ@(limit h) (inj₂ (inj₂ i , j , k))  = {!!} , {!!}
-- 
--     lem₂ : ∀ α β γ → (α ^ β) ^ γ ≥ α ^ (β ∙ γ)
--     lem₂ α β γ = {!!}

simple : ∀ {A : Set a} f (x : A) → f x < limit f
simple f x rewrite ord-lt-unfold (f x) (limit f) = x , ord-le-refl _

lex₁ : ∀ α β₁ β₂ γ₁ γ₂ →
  β₁ < β₂ →
  γ₁ < α →
  α ∙ β₁ + γ₁ < α ∙ β₂ + γ₂

lex₂ : ∀ α β₁ β₂ γ₁ γ₂ →
  β₁ ≤ β₂ →
  γ₁ < γ₂ →
  α ∙ β₁ + γ₁ < α ∙ β₂ + γ₂


lex₁ α@(limit f) β₁@(limit g₁) β₂@(limit g₂) γ₁@(limit h₁) γ₂@(limit h₂) (i , g₁_<g₂i) (j , h₁_≤fj) =
  let rec₁ = λ j′ i′ → lex₁ α (g₁ i′) (g₂ i) (f  j′) (f j) (g₁ i′ <g₂i) (simple f j′)
      rec₂ = λ j′    → lex₂ α β₁      (g₂ i) (h₁ j′) (f j) (g₁_<g₂i)    (h₁ j′ ≤fj)
  in inj₁ (j , i) , [ uncurry rec₁ , rec₂ ]

lex₂ α@(limit f) β₁@(limit g₁) β₂@(limit g₂) γ₁@(limit h₁) γ₂@(limit h₂) β₁≤β₂ (j , h₁_<h₂j) =
     let rec₁ = λ j′ i → lex₁ α (g₁ i) β₂ (f  j′) (h₂ j) (<-≤-trans (simple g₁ i) β₁≤β₂) (simple f j′)
         rec₂ = λ j′   → lex₂ α β₁     β₂ (h₁ j′) (h₂ j) β₁≤β₂                           (h₁ j′ <h₂j)
     in inj₂ j , [ uncurry rec₁ , rec₂ ]


∙-<-cong : ∀ {α β γ} → zero < α → β < γ → α ∙ β < α ∙ γ
∙-<-cong {limit f} {limit g} {limit h} (i , _) (j , g_≤hj) =
  (i , j) , (λ { (a , b) → lex₁ (limit f) (g b) (h j) (f a) (f i) (g b ≤hj) (simple f a) })
