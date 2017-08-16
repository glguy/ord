module Ord.Arithmetic a where

open import Ord.Base a
open import Function
open import Level using (lower; lift)
open import Ord.RelProp a
open import Ord.Pred a
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Ord.MinMaxProp a
open import Ord.Nat a
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {limit _} {limit _} {limit _} {limit _} x≤y u≤v =
  ⊔-mono-≤ x≤y (λ i → (proj₁ (u≤v i)) , +-mono-≤ x≤y (proj₂ (u≤v i)))

∙-mono-≤ : _∙_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
∙-mono-≤ {limit e} {limit f} {limit g} {limit h} x≤y u≤v (i , j) =
  let a , ei≤fa = x≤y i
      c , gj≤hc = u≤v j
  in (a , c) , +-mono-≤ (∙-mono-≤ x≤y gj≤hc) ei≤fa


+-isMonoid : IsMonoid _≈_ _+_ zero

IsSemigroup.isEquivalence (IsMonoid.isSemigroup +-isMonoid) = ≈-isEquivalence

IsSemigroup.assoc (IsMonoid.isSemigroup +-isMonoid) α β γ = lem₁ α β γ , lem₂ α β γ
  where
    lem₁ : ∀ α β γ → (α + β) + γ ≤ α + (β + γ)
    lem₁ (limit f) (limit g) (limit h) (inj₁ (inj₁ i)) = inj₁ i , ord-le-refl _
    lem₁ (limit f) (limit g) (limit h) (inj₁ (inj₂ i)) = inj₂ (inj₁ i) , ord-le-refl _
    lem₁ (limit f) (limit g) (limit h) (inj₂ i) = inj₂ (inj₂ i) , lem₁ _ _ (h i)

    lem₂ : ∀ α β γ → (α + β) + γ ≥ α + (β + γ)
    lem₂ (limit f) (limit g) (limit h) (inj₁ i) = inj₁ (inj₁ i) , ord-le-refl _
    lem₂ (limit f) (limit g) (limit h) (inj₂ (inj₁ i)) = inj₁ (inj₂ i) , ord-le-refl _
    lem₂ (limit f) (limit g) (limit h) (inj₂ (inj₂ i)) = inj₂ i , lem₂ _ _ (h i)


IsSemigroup.∙-cong (IsMonoid.isSemigroup +-isMonoid)
  (x≤y , y≤x) (u≤v , v≤u) = +-mono-≤ x≤y u≤v , +-mono-≤ y≤x v≤u

IsMonoid.identity +-isMonoid = +-identityˡ , +-identityʳ
  where
    +-identityʳ : ∀ x → x + zero ≈ x
    +-identityʳ x@(limit f) =
       limit-cong
         (mk-left-inverse [ id , ⊥-elim ∘ lower ] inj₁
                          [ (λ _ → _≡_.refl) , ⊥-elim ∘ lower ])
             (λ i → refl)
      where
        open Setoid ≈-setoid using (refl)

    +-identityˡ : ∀ x → zero + x ≈ x
    +-identityˡ x = lem₁ x , lem₂ x
      where
        lem₁ : ∀ x → zero + x ≤ x
        lem₁ x@(limit f) (inj₁ ())
        lem₁ x@(limit f) (inj₂ i) = i , (lem₁ (f i))
        lem₂ : ∀ x → zero + x ≥ x
        lem₂ x@(limit f) i = (inj₂ i) , (lem₂ (f i))


+-≤-<-mono : _+_ Preserves₂ _≤_ ⟶ _<_ ⟶ _<_
+-≤-<-mono {β₁@(limit g₁)} {β₂@(limit g₂)} {limit h₁} {limit h₂} β₁≤β₂ (j , h₁_<h₂j) =
  let rec = λ x → +-≤-<-mono β₁≤β₂ (h₁ x <h₂j)
  in inj₂ j , [ lem , rec ]
  where
    open import Relation.Binary.PartialOrderReasoning ≤-poset
    open IsMonoid +-isMonoid

    lem : β₁ ≤ β₂ + h₂ j
    lem = begin β₁ ≤⟨ proj₂ (proj₂ identity β₁) ⟩
                 β₁ + zero ≤⟨ +-mono-≤ β₁≤β₂ (zero-least (h₂ j)) ⟩
                 β₂ + h₂ j ∎


+-∙-dist : ∀ α β γ → α ∙ (β + γ) ≈ α ∙ β + α ∙ γ
+-∙-dist α@(limit {A} f) β@(limit {B} g) γ@(limit {C} h) =
  limit-cong inv λ
  { (inj₁ (i , j)) → refl
  ; (inj₂ (i , j)) →
     begin
       α ∙ (β + h j) + f i ≈⟨ ∙-cong (+-∙-dist α β (h j)) (refl {f i}) ⟩
       α ∙ β + α ∙ h j + f i ≈⟨ assoc (α ∙ β) (α ∙ h j) (f i) ⟩
       α ∙ β + (α ∙ h j + f i) ∎ }
  where
    open import Function.LeftInverse using (_↞_)
    open import Relation.Binary.EqReasoning ≈-setoid
    open IsMonoid +-isMonoid

    inv : (A × (B ⊎ C)) ↞ (A × B ⊎ A × C)
    inv = mk-left-inverse (λ { (i , inj₁ j) → inj₁ (i , j)
                             ; (i , inj₂ j) → inj₂ (i , j) })
                          (λ { (inj₁ (i , j)) → (i , inj₁ j)
                             ; (inj₂ (i , j)) → (i , inj₂ j) })
                          (λ { (i , inj₁ j) → _≡_.refl
                             ; (i , inj₂ j) → _≡_.refl })


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
                     ω + zero <⟨ +-≤-<-mono (ord-le-refl ω) 0<1 ⟩
                     ω + one ∎
      where
        open IsMonoid +-isMonoid

∙-zeroˡ : ∀ α → zero ∙ α ≤ zero
∙-zeroˡ α@(limit f) (lift () , _)

∙-zeroʳ : ∀ α → α ∙ zero ≤ zero
∙-zeroʳ α@(limit f) (_ , lift ())

∙-isMonoid : IsMonoid _≈_ _∙_ one
IsSemigroup.isEquivalence (IsMonoid.isSemigroup ∙-isMonoid) = ≈-isEquivalence
IsSemigroup.assoc         (IsMonoid.isSemigroup ∙-isMonoid) = self
  where
    open import Relation.Binary.EqReasoning ≈-setoid
    open IsMonoid +-isMonoid

    self : Associative _≈_ _∙_
    self α@(limit f) β@(limit g) γ@(limit h)  =
      limit-cong (mk-left-inverse
                 (λ { ((i , j) , k) → i , j , k })
                 (λ { (i , j , k) → ((i , j) , k)})
                 (λ _ → _≡_.refl))
          λ { (i , j , k) → begin

     α ∙  β ∙ h k  + (α ∙ g j + f i)
        ≈⟨ ∙-cong (self α β (h k)) (refl {(α ∙ g j + f i) }) ⟩
     α ∙ (β ∙ h k) + (α ∙ g j + f i)
        ≈⟨ sym (assoc (α ∙ (β ∙ h k)) (α ∙ g j) (f i)) ⟩
     α ∙ (β ∙ h k) + α ∙ g j + f i
        ≈⟨ ∙-cong (sym (+-∙-dist α (β ∙ h k) (g j))) (refl {f i}) ⟩
     α ∙ (β ∙ h k + g j) + f i ∎ }


IsSemigroup.∙-cong (IsMonoid.isSemigroup ∙-isMonoid)
  (x≤y , y≤x) (u≤v , v≤u) = ∙-mono-≤ x≤y u≤v , ∙-mono-≤ y≤x v≤u

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
       (begin α ∙ zero + f i ≤⟨ +-mono-≤ (∙-zeroʳ α) (ord-le-refl (f i)) ⟩
              zero + f i ≤⟨ proj₁ (proj₁ identity (f i)) ⟩
              f i ∎)

    lem₄ : ∀ α → α ∙ one ≥ α
    lem₄ α@(limit f) i = (i , _) ,
       (begin f i ≤⟨ proj₂ (proj₁ identity (f i)) ⟩
              zero + f i ≤⟨ +-mono-≤ (zero-least (α ∙ zero)) (ord-le-refl (f i)) ⟩
              α ∙ zero + f i ∎)



-- ^-+-dist : ∀ α β γ → (α ^ β) ^ γ ≈ α ^ (β ∙ γ)
-- ^-+-dist α@(limit f) β@(limit g) γ@(limit h) =

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


∙-<-mono : ∀ {α β γ} → zero < α → β < γ → α ∙ β < α ∙ γ
∙-<-mono {limit f} {limit g} {limit h} (i , _) (j , g_≤hj) =
  (i , j) , (λ { (a , b) → lex₁ (limit f) (g b) (h j) (f a) (f i) (g b ≤hj) (simple f a) })


open import Data.Nat using (ℕ) renaming (_+_ to _ℕ-+_)

+-suc-comm : ∀ x y → x + suc y ≈ suc (x + y)
+-suc-comm x y = ⊔-pick (ord-lt-le (, ≤-≤-trans (proj₂ (proj₂ identity x))
                                   (+-mono-≤ (ord-le-refl x) (zero-least y))))
  where
    open IsMonoid +-isMonoid

suc-cong : ∀ {α β} → α ≈ β → suc α ≈ suc β
suc-cong (x , y) = (λ _ → , x) , (λ _ → , y)

suc-mono : ∀ {α β} → α ≤ β → α < suc β
suc-mono α≤β = , α≤β

add : ∀ i j → ⌜ i ℕ-+ j ⌝ ≈ ⌜ i ⌝ + ⌜ j ⌝
add x ℕ.zero = begin
  ⌜ x ℕ-+ 0 ⌝ ≈⟨ reflexive (cong ⌜_⌝ (+-comm x 0)) ⟩
  ⌜ x  ⌝ ≈⟨ sym (proj₂ identity ⌜ x ⌝) ⟩
  ⌜ x ⌝ + ⌜ 0 ⌝ ∎
  where
    open import Relation.Binary.EqReasoning ≈-setoid
    open import Data.Nat.Properties using (commutativeSemiring)
    open import Relation.Binary.PropositionalEquality using (cong; subst)
    open import Algebra
    open CommutativeSemiring commutativeSemiring using (+-comm)
    open IsMonoid +-isMonoid

add x (ℕ.suc y) =
  begin ⌜ x ℕ-+ ℕ.suc y ⌝ ≈⟨ reflexive (cong ⌜_⌝ (+-comm x (ℕ.suc y))) ⟩
        suc ⌜ y ℕ-+ x ⌝ ≈⟨ reflexive (cong (λ a₁ → suc ⌜ a₁ ⌝) (+-comm y x)) ⟩
        suc ⌜ x ℕ-+ y ⌝ ≈⟨ suc-cong (add x y) ⟩
        suc (⌜ x ⌝ + ⌜ y ⌝) ≈⟨ sym (+-suc-comm ⌜ x ⌝ ⌜ y ⌝) ⟩
        ⌜ x ⌝ + ⌜ ℕ.suc y ⌝ ∎
  where
    open import Relation.Binary.EqReasoning ≈-setoid
    open IsEquivalence ≈-isEquivalence
    open import Data.Nat.Properties using (commutativeSemiring)
    open import Relation.Binary.PropositionalEquality using (cong; subst)
    open import Algebra
    open CommutativeSemiring commutativeSemiring using (+-comm)

ω-dominates : ∀ i → ⌜ i ⌝ + ω ≤ ω
ω-dominates ℕ.zero = proj₁ (proj₁ identity ω)
  where
    open IsMonoid +-isMonoid
ω-dominates (ℕ.suc i) (inj₁ _) = lift i , ord-le-refl _
ω-dominates (ℕ.suc i) (inj₂ (lift j)) = lift (ℕ.suc i ℕ-+ j) , proj₂ (add (ℕ.suc i) j)

