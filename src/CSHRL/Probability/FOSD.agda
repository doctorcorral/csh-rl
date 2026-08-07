{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Probability.FOSD
--
-- First-Order Stochastic Dominance for finite distributions.
--
-- μ ≥_FOSD ν iff ∀ r. P(μ ≤ r) ≤ P(ν ≤ r)
--
-- Strictly stronger than expected-value comparison:
--   μ ≥_FOSD ν ⟹ E[μ] ≥ E[ν], but not conversely.
--
-- Preferred by ALL monotone utility functions, not just E[·].
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Probability.FOSD where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; z≤n; s≤s;
                            _∸_; _⊔_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Base using (T)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans;
         +-identityʳ; +-comm; +-assoc;
         +-mono-≤; m≤m+n; m≤n+m;
         m+n∸n≡m; m∸n≤m; ∸-mono;
         ≤ᵇ⇒≤; ≤⇒≤ᵇ; n≤1+n; m≤n⇒m≤1+n; m≤m⊔n; m≤n⊔m; n≤m⊔n; ≰⇒≥; ≰⇒>; ≤-antisym;
         *-distribˡ-+; *-zeroʳ; *-identityˡ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import CSHRL.Probability.Finite using (Dist; total-weight; weighted-sum; scale)

------------------------------------------------------------------------
-- Max value in support (for bounded FOSD check)
------------------------------------------------------------------------

max-support : Dist ℕ → ℕ
max-support []            = 0
max-support ((v , w) ∷ d) = v ⊔ max-support d

------------------------------------------------------------------------
-- CDF and Complement (computed together to share the decision)
------------------------------------------------------------------------

split : Dist ℕ → ℕ → ℕ × ℕ
split [] _ = (0 , 0)
split ((v , w) ∷ rest) r with v ≤? r
... | yes _ = let (c , k) = split rest r in (w + c , k)
... | no  _ = let (c , k) = split rest r in (c , w + k)

cdf-weight : Dist ℕ → ℕ → ℕ
cdf-weight d r = proj₁ (split d r)

comp-weight : Dist ℕ → ℕ → ℕ
comp-weight d r = proj₂ (split d r)

------------------------------------------------------------------------
-- CDF + Complement = Total Weight
------------------------------------------------------------------------

split-sum : ∀ (d : Dist ℕ) r →
            proj₁ (split d r) + proj₂ (split d r) ≡ total-weight d
split-sum [] _ = refl
split-sum ((v , w) ∷ rest) r with v ≤? r
... | yes _ =
  trans (+-assoc w (proj₁ (split rest r)) (proj₂ (split rest r)))
        (cong (w +_) (split-sum rest r))
... | no  _ =
  trans (+-comm (proj₁ (split rest r)) (w + proj₂ (split rest r)))
  (trans (+-assoc w (proj₂ (split rest r)) (proj₁ (split rest r)))
  (cong (w +_)
  (trans (+-comm (proj₂ (split rest r)) (proj₁ (split rest r)))
         (split-sum rest r))))

cdf+comp : ∀ (d : Dist ℕ) r →
           cdf-weight d r + comp-weight d r ≡ total-weight d
cdf+comp = split-sum

------------------------------------------------------------------------
-- Scale: cdf-weight and total-weight scale by k
------------------------------------------------------------------------

split-scale : ∀ (d : Dist ℕ) r k →
  split (scale k d) r ≡ (k * proj₁ (split d r) , k * proj₂ (split d r))
split-scale [] _ k = cong₂ _,_ (sym (*-zeroʳ k)) (sym (*-zeroʳ k))
split-scale ((v , w) ∷ rest) r k with v ≤? r
... | yes _ rewrite split-scale rest r k =
  cong₂ _,_ (sym (*-distribˡ-+ k w (proj₁ (split rest r)))) refl
... | no  _ rewrite split-scale rest r k =
  cong₂ _,_ refl (sym (*-distribˡ-+ k w (proj₂ (split rest r))))

cdf-weight-scale : ∀ (d : Dist ℕ) r k →
  cdf-weight (scale k d) r ≡ k * cdf-weight d r
cdf-weight-scale d r k = cong proj₁ (split-scale d r k)

total-weight-scale : ∀ (d : Dist ℕ) k →
  total-weight (scale k d) ≡ k * total-weight d
total-weight-scale [] k = sym (*-zeroʳ k)
total-weight-scale ((a , w) ∷ d) k
  rewrite total-weight-scale d k
  = sym (*-distribˡ-+ k w (total-weight d))

max-support-scale : ∀ (d : Dist ℕ) k → max-support (scale k d) ≡ max-support d
max-support-scale [] _ = refl
max-support-scale ((v , w) ∷ d) k = cong (v ⊔_) (max-support-scale d k)

------------------------------------------------------------------------
-- CDF distributes over list concatenation
------------------------------------------------------------------------

cdf-weight-++ : ∀ (d₁ d₂ : Dist ℕ) r →
  cdf-weight (d₁ ++ d₂) r ≡ cdf-weight d₁ r + cdf-weight d₂ r
cdf-weight-++ [] d₂ r = refl
cdf-weight-++ ((v , w) ∷ d₁) d₂ r with v ≤? r
... | yes _ = trans (cong (w +_) (cdf-weight-++ d₁ d₂ r))
                    (sym (+-assoc w (cdf-weight d₁ r) (cdf-weight d₂ r)))
... | no  _ = cdf-weight-++ d₁ d₂ r

total-weight-++ : ∀ (d₁ d₂ : Dist ℕ) →
  total-weight (d₁ ++ d₂) ≡ total-weight d₁ + total-weight d₂
total-weight-++ [] d₂ = refl
total-weight-++ ((_ , w) ∷ d₁) d₂ =
  trans (cong (w +_) (total-weight-++ d₁ d₂))
        (sym (+-assoc w (total-weight d₁) (total-weight d₂)))

------------------------------------------------------------------------
-- FOSD Ordering and Preorder
------------------------------------------------------------------------

_FOSD≤_ : Dist ℕ → Dist ℕ → Set
μ FOSD≤ ν = ∀ r → cdf-weight ν r ≤ cdf-weight μ r

FOSD-refl : ∀ (d : Dist ℕ) → d FOSD≤ d
FOSD-refl _ _ = ≤-refl

FOSD-trans : ∀ {a b c : Dist ℕ} → a FOSD≤ b → b FOSD≤ c → a FOSD≤ c
FOSD-trans ab bc r = ≤-trans (bc r) (ab r)

------------------------------------------------------------------------
-- Decidable FOSD (for synthesis observation layer)
--
-- μ FOSD≤ ν iff ∀r. cdf(ν,r) ≤ cdf(μ,r).
-- For finite distributions, check r = 0..max(support μ ⊔ support ν).
-- Beyond max, both CDFs = total weight; require total-weight ν ≤ total-weight μ.
------------------------------------------------------------------------

fosd?-go : Dist ℕ → Dist ℕ → ℕ → Bool
fosd?-go μ ν zero    = cdf-weight ν 0 ≤ᵇ cdf-weight μ 0
fosd?-go μ ν (suc r) =
  (cdf-weight ν (suc r) ≤ᵇ cdf-weight μ (suc r)) ∧
  fosd?-go μ ν r

fosd? : Dist ℕ → Dist ℕ → Bool
fosd? μ ν =
  let max-r = max-support μ ⊔ max-support ν
      tw-ok = total-weight ν ≤ᵇ total-weight μ
  in tw-ok ∧ fosd?-go μ ν max-r

------------------------------------------------------------------------
-- fosd?-sound: fosd? μ ν ≡ true → μ FOSD≤ ν
------------------------------------------------------------------------

-- When r ≥ max-support d, cdf-weight d r = total-weight d
cdf-max : ∀ (d : Dist ℕ) r → max-support d ≤ r →
  cdf-weight d r ≡ total-weight d
cdf-max [] _ _ = refl
cdf-max ((v , w) ∷ rest) r v⊔m≤r with v ≤? r
... | yes _ = cong (w +_) (cdf-max rest r (≤-trans (n≤m⊔n v (max-support rest)) v⊔m≤r))
... | no v≰r = ⊥-elim (v≰r (≤-trans (m≤m⊔n v (max-support rest)) v⊔m≤r))

-- fosd?-go μ ν r ≡ true implies cdf(ν,r') ≤ cdf(μ,r') for all r' ≤ r
fosd?-go-sound : ∀ μ ν r → fosd?-go μ ν r ≡ true →
  ∀ r' → r' ≤ r → cdf-weight ν r' ≤ cdf-weight μ r'
fosd?-go-sound μ ν zero eq r' r'≤0
  rewrite ≤-antisym r'≤0 z≤n = ≤ᵇ⇒≤ (cdf-weight ν 0) (cdf-weight μ 0)
    (subst T (sym eq) tt)
fosd?-go-sound μ ν (suc r) eq r' r'≤sr with r' ≤? r
... | yes r'≤r = fosd?-go-sound μ ν r (∧-project₂ eq) r' r'≤r
  where
    ∧-project₂ : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
    ∧-project₂ {true}  refl = refl
    ∧-project₂ {false} ()
... | no r'≰r with r' ≤? suc r
...   | no r'≰sr = ⊥-elim (r'≰sr r'≤sr)
...   | yes _    rewrite ≤-antisym r'≤sr (≰⇒> r'≰r) =
        ≤ᵇ⇒≤ (cdf-weight ν (suc r)) (cdf-weight μ (suc r))
          (subst T (sym (∧-project₁ eq)) tt)
  where
    ∧-project₁ : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
    ∧-project₁ {true}  refl = refl
    ∧-project₁ {false} ()

∧-project₁ : ∀ {a b : Bool} → (a ∧ b) ≡ true → a ≡ true
∧-project₁ {true}  refl = refl
∧-project₁ {false} ()

∧-project₂ : ∀ {a b : Bool} → (a ∧ b) ≡ true → b ≡ true
∧-project₂ {true}  refl = refl
∧-project₂ {false} ()

fosd?-sound : ∀ μ ν → fosd? μ ν ≡ true → μ FOSD≤ ν
fosd?-sound μ ν eq r with r ≤? (max-support μ ⊔ max-support ν)
... | yes r≤max = fosd?-go-sound μ ν (max-support μ ⊔ max-support ν)
    (∧-project₂ eq) r r≤max
... | no r≰max = subst₂ _≤_
    (sym (cdf-max ν r (≤-trans (n≤m⊔n (max-support μ) (max-support ν)) (≰⇒≥ r≰max))))
    (sym (cdf-max μ r (≤-trans (m≤m⊔n (max-support μ) (max-support ν)) (≰⇒≥ r≰max))))
    (≤ᵇ⇒≤ (total-weight ν) (total-weight μ)
      (subst T (sym (∧-project₁ eq)) tt))
cdf≤total : ∀ (d : Dist ℕ) r → cdf-weight d r ≤ total-weight d
cdf≤total d r = subst (cdf-weight d r ≤_) (cdf+comp d r) (m≤m+n _ _)

------------------------------------------------------------------------
-- fosd? (scale k μ) ν ≡ true when fosd? μ ν ≡ true and 1 ≤ k
------------------------------------------------------------------------

n≤k*n : ∀ n k → 1 ≤ k → n ≤ k * n
n≤k*n n (suc zero) 1≤k = subst (n ≤_) (sym (*-identityˡ n)) ≤-refl
n≤k*n n (suc (suc k)) 1≤k = m≤m+n n ((suc k) * n)

T-to-≡ : ∀ {b : Bool} → T b → b ≡ true
T-to-≡ {true}  _ = refl
T-to-≡ {false} ()

fosd?-go-scale : ∀ μ ν r k → fosd?-go μ ν r ≡ true → 1 ≤ k →
  fosd?-go (scale k μ) ν r ≡ true
fosd?-go-scale μ ν zero k eq 1≤k
  rewrite cdf-weight-scale μ 0 k
  = T-to-≡ (≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ (cdf-weight ν 0) (cdf-weight μ 0) (subst T (sym eq) tt))
        (n≤k*n (cdf-weight μ 0) k 1≤k)))
fosd?-go-scale μ ν (suc r) k eq 1≤k
  rewrite cdf-weight-scale μ (suc r) k
  = cong₂ _∧_
      (T-to-≡ (≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ (cdf-weight ν (suc r)) (cdf-weight μ (suc r))
        (subst T (sym (∧-project₁ eq)) tt))
          (n≤k*n (cdf-weight μ (suc r)) k 1≤k))))
      (fosd?-go-scale μ ν r k (∧-project₂ eq) 1≤k)

fosd?-scale : ∀ μ ν k → fosd? μ ν ≡ true → 1 ≤ k →
  fosd? (scale k μ) ν ≡ true
fosd?-scale μ ν k eq 1≤k
  rewrite total-weight-scale μ k
  | max-support-scale μ k
  = cong₂ _∧_
      (T-to-≡ (≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ (total-weight ν) (total-weight μ) (subst T (sym (∧-project₁ eq)) tt))
          (n≤k*n (total-weight μ) k 1≤k))))
      (fosd?-go-scale μ ν (max-support μ ⊔ max-support ν) k (∧-project₂ eq) 1≤k)

------------------------------------------------------------------------
-- fosd?-complete: μ FOSD≤ ν → fosd? μ ν ≡ true
--
-- The converse of fosd?-sound. Together they establish that fosd?
-- is a decision procedure: fosd? μ ν ≡ true ⟺ μ FOSD≤ ν.
------------------------------------------------------------------------

fosd?-go-complete : ∀ μ ν r →
  (∀ r' → r' ≤ r → cdf-weight ν r' ≤ cdf-weight μ r') →
  fosd?-go μ ν r ≡ true
fosd?-go-complete μ ν zero pf =
  T-to-≡ (≤⇒≤ᵇ (pf 0 z≤n))
fosd?-go-complete μ ν (suc r) pf =
  cong₂ _∧_
    (T-to-≡ (≤⇒≤ᵇ (pf (suc r) ≤-refl)))
    (fosd?-go-complete μ ν r (λ r' r'≤r → pf r' (m≤n⇒m≤1+n r'≤r)))

private
  n≤m⊔n′ : ∀ m n → n ≤ m ⊔ n
  n≤m⊔n′ zero    n       = ≤-refl
  n≤m⊔n′ (suc m) zero    = z≤n
  n≤m⊔n′ (suc m) (suc n) = s≤s (n≤m⊔n′ m n)

  fosd→tw : ∀ (μ ν : Dist ℕ) → μ FOSD≤ ν → total-weight ν ≤ total-weight μ
  fosd→tw μ ν fosd
    rewrite sym (cdf-max ν (max-support μ ⊔ max-support ν)
                  (n≤m⊔n′ (max-support μ) (max-support ν)))
    | sym (cdf-max μ (max-support μ ⊔ max-support ν)
                  (m≤m⊔n (max-support μ) (max-support ν)))
    = fosd (max-support μ ⊔ max-support ν)

fosd?-complete : ∀ μ ν → μ FOSD≤ ν → fosd? μ ν ≡ true
fosd?-complete μ ν fosd = cong₂ _∧_ tw-part go-part
  where
    tw-part : (total-weight ν ≤ᵇ total-weight μ) ≡ true
    tw-part = T-to-≡ (≤⇒≤ᵇ (fosd→tw μ ν fosd))

    go-part : fosd?-go μ ν (max-support μ ⊔ max-support ν) ≡ true
    go-part = fosd?-go-complete μ ν (max-support μ ⊔ max-support ν)
      (λ r' _ → fosd r')

------------------------------------------------------------------------
-- FOSD ⟹ Complement Dominance
------------------------------------------------------------------------

private
  comp-from-total : ∀ (d : Dist ℕ) r →
    total-weight d ∸ cdf-weight d r ≡ comp-weight d r
  comp-from-total d r rewrite sym (cdf+comp d r)
    | +-comm (cdf-weight d r) (comp-weight d r)
    = m+n∸n≡m (comp-weight d r) (cdf-weight d r)

fosd→comp : ∀ {μ ν : Dist ℕ} →
  total-weight μ ≡ total-weight ν →
  μ FOSD≤ ν →
  ∀ r → comp-weight μ r ≤ comp-weight ν r
fosd→comp {μ} {ν} tw fosd r
  rewrite sym (comp-from-total μ r)
  | sym (comp-from-total ν r)
  | tw
  = ∸-mono (≤-refl {total-weight ν})
           (fosd r)

------------------------------------------------------------------------
-- Complement at 0 = Weighted Sum (for 0/1 distributions)
------------------------------------------------------------------------

AllBelow : Dist ℕ → ℕ → Set
AllBelow [] _ = ℕ
AllBelow ((v , _) ∷ rest) M = v ≤ M × AllBelow rest M

comp0≡ws : ∀ (d : Dist ℕ) → AllBelow d 1 →
           comp-weight d 0 ≡ weighted-sum d
comp0≡ws [] _ = refl
comp0≡ws ((zero , w) ∷ rest) (_ , ab)
  rewrite comp0≡ws rest ab = refl
comp0≡ws ((suc zero , w) ∷ rest) (_ , ab)
  rewrite +-identityʳ w | comp0≡ws rest ab = refl
comp0≡ws ((suc (suc _) , _) ∷ _) (s≤s () , _)

------------------------------------------------------------------------
-- FOSD ⟹ E[X] Dominance (0/1 Distributions, Fully Proved)
------------------------------------------------------------------------

fosd→ev : ∀ (μ ν : Dist ℕ) →
  AllBelow μ 1 → AllBelow ν 1 →
  total-weight μ ≡ total-weight ν →
  μ FOSD≤ ν →
  weighted-sum μ ≤ weighted-sum ν
fosd→ev μ ν ab-μ ab-ν tw fosd
  rewrite sym (comp0≡ws μ ab-μ) | sym (comp0≡ws ν ab-ν)
  = fosd→comp {μ} {ν} tw fosd 0

------------------------------------------------------------------------
-- Computational Tests: BiasedBandit
------------------------------------------------------------------------

armA : Dist ℕ
armA = (1 , 2) ∷ (0 , 1) ∷ []

armB : Dist ℕ
armB = (1 , 1) ∷ (0 , 2) ∷ []

test-cdf-A0 : cdf-weight armA 0 ≡ 1
test-cdf-A0 = refl

test-cdf-A1 : cdf-weight armA 1 ≡ 3
test-cdf-A1 = refl

test-cdf-B0 : cdf-weight armB 0 ≡ 2
test-cdf-B0 = refl

test-cdf-B1 : cdf-weight armB 1 ≡ 3
test-cdf-B1 = refl

test-tw : total-weight armA ≡ total-weight armB
test-tw = refl

bandit-fosd : armB FOSD≤ armA
bandit-fosd zero = s≤s z≤n
bandit-fosd (suc _) = ≤-refl

bandit-ev : weighted-sum armB ≤ weighted-sum armA
bandit-ev = fosd→ev armB armA
  (s≤s z≤n , z≤n , 0) (s≤s z≤n , z≤n , 0)
  refl bandit-fosd

test-ws-A : weighted-sum armA ≡ 2
test-ws-A = refl

test-ws-B : weighted-sum armB ≡ 1
test-ws-B = refl

-- Decidable FOSD matches bandit-fosd: armB FOSD≤ armA
test-fosd? : fosd? armB armA ≡ true
test-fosd? = refl
