module Ord.RelProp a where

open import Level using (lift)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Induction.WellFounded
open import Function
open import Function.LeftInverse using (_↞_; module LeftInverse; _LeftInverseOf_)
open import Function.Equality using (_⟨$⟩_)
open import Ord.Base a


≤-≤-trans : Transitive _≤_
<-≤-trans : Trans _<_ _≤_ _<_
≤-<-trans : Trans _≤_ _<_ _<_

≤-≤-trans {limit x} {y} {z} le₁ le₂ i
  = <-≤-trans {x i} {y} {z} (le₁ i) le₂

<-≤-trans {limit x} {limit y} {z} (j , k) le
  = ≤-<-trans {limit x} {y j} {z} k (le j)

≤-<-trans {limit x} {limit y} {limit z} le (j , k)
  = j , ≤-≤-trans {limit x} {limit y} {z j} le k

<-<-trans : Transitive _<_
<-<-trans {limit x} {limit y} {limit z} (i , f) (j , g)
  = j , λ k → <-<-trans {x k} {y i} {z j} (f k) (g i)

------------------------------------------------------------------------

<-wf : WellFounded _<_
<-wf = accessible ∘ ord-le-refl
  where
    accessible : ∀ {x y} → x ≤ y → Acc _<_ x
    accessible {limit _} {limit _} x≤y =
      acc λ z z<x →
        let _ , z≤yᵢ = <-≤-trans z<x x≤y
        in accessible z≤yᵢ

private
  wf-irref : ∀ {a ℓ} {A : Set a} {R : Rel A ℓ} → WellFounded R → Irreflexive _≡_ R
  wf-irref {R = R} wf {x} refl x<x = loop (wf x)
    where
      loop : ¬ Acc R x
      loop (acc rs) = loop (rs _ x<x)

<-irref : Irreflexive _≡_ _<_
<-irref = wf-irref <-wf

------------------------------------------------------------------------

≈-isEquivalence : IsEquivalence _≈_
IsEquivalence.refl  ≈-isEquivalence = ord-le-refl _ , ord-le-refl _
IsEquivalence.sym   ≈-isEquivalence (x≤y , y≤x) = y≤x , x≤y
IsEquivalence.trans ≈-isEquivalence (x≤y , y≤x) (y≤z , z≤y) =
   ≤-≤-trans x≤y y≤z , ≤-≤-trans z≤y y≤x

≤-isPartialOrder : IsPartialOrder _≈_ _≤_

IsPreorder.isEquivalence (IsPartialOrder.isPreorder ≤-isPartialOrder) = ≈-isEquivalence
IsPreorder.reflexive     (IsPartialOrder.isPreorder ≤-isPartialOrder) = proj₁
IsPreorder.trans         (IsPartialOrder.isPreorder ≤-isPartialOrder) = ≤-≤-trans
IsPartialOrder.antisym                              ≤-isPartialOrder  = _,_

<-isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_

IsStrictPartialOrder.isEquivalence <-isStrictPartialOrder = ≈-isEquivalence

IsStrictPartialOrder.irrefl <-isStrictPartialOrder (_ , y≤x) x<y =
  contradiction (<-≤-trans x<y y≤x) (<-irref refl)

IsStrictPartialOrder.trans <-isStrictPartialOrder = <-<-trans

IsStrictPartialOrder.<-resp-≈ <-isStrictPartialOrder = lem₁ , lem₂
  where
    lem₁ : {x : Ord} → _<_ x Respects _≈_
    lem₁ (y≤z , _) x<y = <-≤-trans x<y y≤z

    lem₂ : {x : Ord} → flip _<_ x Respects _≈_
    lem₂ (_ , z≤y) y<x = ≤-<-trans z≤y y<x

------------------------------------------------------------------------

≈-setoid : Setoid _ _
≈-setoid = record
  { Carrier = Ord ; _≈_ = _≈_
  ; isEquivalence = ≈-isEquivalence }

≤-poset : Poset _ _ _
≤-poset = record
  { Carrier = Ord ; _≈_ = _≈_ ; _≤_ = _≤_
  ; isPartialOrder = ≤-isPartialOrder }

<-strictPartialOrder : StrictPartialOrder _ _ _
<-strictPartialOrder = record
  { Carrier = Ord ; _≈_ = _≈_ ; _<_ = _<_
  ; isStrictPartialOrder = <-isStrictPartialOrder }

------------------------------------------------------------------------

limit-least : (x y : Ord) → (∀ i → subord x i < y) → x ≤ y
limit-least (limit f) y lt = lt

zero-least : ∀ x → zero ≤ x
zero-least (limit f) (lift ())

suc-small : ∀ x y → x < y → suc x ≤ y
suc-small x y x<y _ = x<y

suc-step : ∀ x → x < suc x
suc-step x = _ , ord-le-refl x

zero-suc : ∀ x → zero < suc x
zero-suc (limit x) = _ , zero-least _

limit-cong :
  ∀ {A B : Set a} {f : A → Ord} {g : B → Ord}
  (inv : A ↞ B) →
  ( (i : B) → f (LeftInverse.from inv ⟨$⟩ i) ≈ g i) →
  limit f ≈ limit g
limit-cong {A} {B} {f} {g} inv z = lem₁ , lem₂
  where
    open LeftInverse inv

    lem₁ : limit f ≤ limit g
    lem₁ i rewrite sym (left-inverse-of i) = _ , proj₁ (z (to ⟨$⟩ i))

    lem₂ : limit f ≥ limit g
    lem₂ i = _ , proj₂ (z i)

mk-left-inverse :
  ∀ {A B : Set a}
  (f : A → B) (g : B → A) → ((x : A) → g (f x) ≡ x) →
  A ↞ B
mk-left-inverse f g i =
  record { to = →-to-⟶ f ; from = →-to-⟶ g ; left-inverse-of = i }
  where
    open import Relation.Binary.PropositionalEquality using (→-to-⟶)
