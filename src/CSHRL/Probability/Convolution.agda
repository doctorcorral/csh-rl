{-# OPTIONS --safe --guardedness #-}

------------------------------------------------------------------------
-- CSHRL.Probability.Convolution
--
-- Convolution (independent sum) of finite distributions, and the
-- proof that FOSD and SD[k] are closed under convolution.
--
-- The convolution theorem is the natural composition law for product
-- MDPs with summed rewards:  if two pairs of distributions each
-- satisfy stochastic dominance, then pairwise independent sums
-- also satisfy stochastic dominance.
--
-- Proof structure (Abel summation via induction):
--   1. CDF of convolution decomposes via generalized weighted sum
--   2. Kernel direction: pointwise h comparison (gws-mono)
--   3. Base direction: FOSD implies gws dominance for non-increasing
--      h, proved by induction on the support bound M
--   4. FOSD-conv combines both directions via transitivity
--   5. SD-conv lifts to the full hierarchy
--
-- All --safe, no postulates.
------------------------------------------------------------------------

module CSHRL.Probability.Convolution where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≤?_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym;
         +-identityʳ; +-assoc; +-comm;
         +-mono-≤;
         *-distribˡ-+; *-monoʳ-≤; *-comm; *-zeroʳ;
         m≤m+n; m≤n+m; n≤1+n;
         m+n∸n≡m;
         ∸-mono; ≰⇒>)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import CSHRL.Probability.Finite
  using (Dist; fmap; _>>=_; scale; total-weight)
open import CSHRL.Probability.FOSD
  using (cdf-weight; _FOSD≤_; FOSD-refl; FOSD-trans;
         cdf-weight-++; cdf-weight-scale;
         total-weight-++; total-weight-scale)
open import CSHRL.Probability.SD
  using (_SD[_]≤_; SD-subsumes)

------------------------------------------------------------------------
-- Convolution: independent sum of two distributions
------------------------------------------------------------------------

conv : Dist ℕ → Dist ℕ → Dist ℕ
conv d₁ d₂ = d₁ >>= λ v₁ → fmap (v₁ +_) d₂

------------------------------------------------------------------------
-- Generalized weighted sum: Σ_{(v,w) ∈ d} w * h(v)
------------------------------------------------------------------------

gws : Dist ℕ → (ℕ → ℕ) → ℕ
gws [] h = 0
gws ((v , w) ∷ d) h = w * h v + gws d h

------------------------------------------------------------------------
-- CDF of convolution decomposes as gws
------------------------------------------------------------------------

cdf-conv : ∀ (d₁ d₂ : Dist ℕ) r →
  cdf-weight (conv d₁ d₂) r ≡ gws d₁ (λ v → cdf-weight (fmap (v +_) d₂) r)
cdf-conv [] d₂ r = refl
cdf-conv ((v₁ , w₁) ∷ rest) d₂ r =
  trans (cdf-weight-++ (scale w₁ (fmap (v₁ +_) d₂)) (conv rest d₂) r)
  (cong₂ _+_
    (cdf-weight-scale (fmap (v₁ +_) d₂) r w₁)
    (cdf-conv rest d₂ r))

------------------------------------------------------------------------
-- gws pointwise monotonicity
------------------------------------------------------------------------

gws-mono : ∀ (d : Dist ℕ) {h₁ h₂ : ℕ → ℕ} →
  (∀ v → h₁ v ≤ h₂ v) → gws d h₁ ≤ gws d h₂
gws-mono [] _ = z≤n
gws-mono ((v , w) ∷ d) mono =
  +-mono-≤ (*-monoʳ-≤ w (mono v)) (gws-mono d mono)

------------------------------------------------------------------------
-- Arithmetic helpers
------------------------------------------------------------------------

private
  n∸n≡0 : ∀ n → n ∸ n ≡ 0
  n∸n≡0 zero = refl
  n∸n≡0 (suc n) = n∸n≡0 n

  0∸n≡0 : ∀ n → 0 ∸ n ≡ 0
  0∸n≡0 zero    = refl
  0∸n≡0 (suc _) = refl

  ∸+≡ : ∀ {m n} → n ≤ m → m ∸ n + n ≡ m
  ∸+≡ {m}     {zero}  z≤n       = +-identityʳ m
  ∸+≡ {suc m} {suc n} (s≤s n≤m) =
    trans (+-comm (m ∸ n) (suc n))
    (trans (cong suc (+-comm n (m ∸ n)))
           (cong suc (∸+≡ n≤m)))

  suc≰ : ∀ {m n} → m ≤ n → ¬ (suc n ≤ m)
  suc≰ z≤n ()
  suc≰ (s≤s m≤n) (s≤s sn≤m) = suc≰ m≤n sn≤m

  rearrange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  rearrange a b c d =
    trans (+-assoc a b (c + d))
    (trans (cong (a +_) (sym (+-assoc b c d)))
    (trans (cong (a +_) (cong (_+ d) (+-comm b c)))
    (trans (cong (a +_) (+-assoc c b d))
           (sym (+-assoc a c (b + d))))))

  subst₂ : ∀ {A B : Set} (P : A → B → Set)
    {x x' y y'} → x ≡ x' → y ≡ y' → P x y → P x' y'
  subst₂ _ refl refl p = p

------------------------------------------------------------------------
-- CDF of shifted distribution: cdf(fmap (k+_) d, r)
------------------------------------------------------------------------

cdf-fmap-add : ∀ k (d : Dist ℕ) r → k ≤ r →
  cdf-weight (fmap (k +_) d) r ≡ cdf-weight d (r ∸ k)
cdf-fmap-add k [] r k≤r = refl
cdf-fmap-add k ((u , w) ∷ rest) r k≤r
  with k + u ≤? r | u ≤? (r ∸ k)
... | yes _    | yes _     = cong (w +_) (cdf-fmap-add k rest r k≤r)
... | no _     | no _      = cdf-fmap-add k rest r k≤r
... | yes ku≤r | no ¬u≤r∸k = ⊥-elim (¬u≤r∸k
  (subst (_≤ r ∸ k) (m+n∸n≡m u k)
    (∸-mono (subst (_≤ r) (+-comm k u) ku≤r) (≤-refl {k}))))
... | no ¬ku≤r | yes u≤r∸k = ⊥-elim (¬ku≤r
  (subst (_≤ r) (sym (+-comm k u))
    (subst (u + k ≤_) (∸+≡ k≤r)
      (+-mono-≤ u≤r∸k (≤-refl {k})))))

cdf-fmap-zero : ∀ k (d : Dist ℕ) r → ¬ (k ≤ r) →
  cdf-weight (fmap (k +_) d) r ≡ 0
cdf-fmap-zero k [] r _ = refl
cdf-fmap-zero k ((u , w) ∷ rest) r ¬k≤r with k + u ≤? r
... | yes ku≤r = ⊥-elim (¬k≤r (≤-trans (m≤m+n k u) ku≤r))
... | no _     = cdf-fmap-zero k rest r ¬k≤r

------------------------------------------------------------------------
-- FOSD preserved under shifting
------------------------------------------------------------------------

FOSD-shift : ∀ k {μ ν : Dist ℕ} → μ FOSD≤ ν →
  fmap (k +_) μ FOSD≤ fmap (k +_) ν
FOSD-shift k {μ} {ν} fosd r with k ≤? r
... | yes k≤r rewrite cdf-fmap-add k ν r k≤r | cdf-fmap-add k μ r k≤r
  = fosd (r ∸ k)
... | no ¬k≤r rewrite cdf-fmap-zero k ν r ¬k≤r | cdf-fmap-zero k μ r ¬k≤r
  = ≤-refl

------------------------------------------------------------------------
-- Shift CDF is non-increasing
------------------------------------------------------------------------

shift-cdf-mono : ∀ (d : Dist ℕ) v r →
  cdf-weight (fmap (suc v +_) d) r ≤ cdf-weight (fmap (v +_) d) r
shift-cdf-mono [] v r = z≤n
shift-cdf-mono ((u , w) ∷ rest) v r
  with suc (v + u) ≤? r | v + u ≤? r
... | yes _ | yes _ = +-mono-≤ ≤-refl (shift-cdf-mono rest v r)
... | yes p | no ¬q = ⊥-elim (¬q (≤-trans (n≤1+n (v + u)) p))
... | no _  | yes _ = ≤-trans (shift-cdf-mono rest v r) (m≤n+m _ w)
... | no _  | no _  = shift-cdf-mono rest v r

------------------------------------------------------------------------
-- Shift CDF is eventually zero
------------------------------------------------------------------------

shift-cdf-zero : ∀ (d : Dist ℕ) r →
  cdf-weight (fmap (suc r +_) d) r ≡ 0
shift-cdf-zero [] r = refl
shift-cdf-zero ((u , w) ∷ rest) r with suc (r + u) ≤? r
... | yes p = ⊥-elim (suc≰ (m≤m+n r u) p)
... | no _  = shift-cdf-zero rest r

------------------------------------------------------------------------
-- Non-increasing function propagation
------------------------------------------------------------------------

private
  h-vanish : ∀ (h : ℕ → ℕ) → (∀ v → h (suc v) ≤ h v) →
    ∀ M → h M ≡ 0 → ∀ n → h (n + M) ≡ 0
  h-vanish h mono M h0 zero = h0
  h-vanish h mono M h0 (suc n) =
    ≤-antisym
      (subst (h (suc (n + M)) ≤_) (h-vanish h mono M h0 n) (mono (n + M)))
      z≤n

  mono-chain : ∀ (h : ℕ → ℕ) → (∀ v → h (suc v) ≤ h v) →
    ∀ m n → h (m + n) ≤ h n
  mono-chain h mono zero n = ≤-refl
  mono-chain h mono (suc m) n = ≤-trans (mono (m + n)) (mono-chain h mono m n)

------------------------------------------------------------------------
-- Base case: gws when h is nonzero only at 0
------------------------------------------------------------------------

private
  gws-base : ∀ (d : Dist ℕ) (h : ℕ → ℕ) →
    (∀ v → h (suc v) ≤ h v) → h 1 ≡ 0 →
    gws d h ≡ h 0 * cdf-weight d 0
  gws-base [] h mono h1 = sym (*-zeroʳ (h 0))
  gws-base ((zero , w) ∷ rest) h mono h1 with zero ≤? 0
  ... | yes _ =
    trans (cong (w * h 0 +_) (gws-base rest h mono h1))
    (trans (cong (_+ h 0 * cdf-weight rest 0) (*-comm w (h 0)))
           (sym (*-distribˡ-+ (h 0) w (cdf-weight rest 0))))
  ... | no ¬p = ⊥-elim (¬p z≤n)
  gws-base ((suc v' , w) ∷ rest) h mono h1 with suc v' ≤? 0
  ... | yes ()
  ... | no _ =
    trans (cong (_+ gws rest h) (trans (cong (w *_) hv≡0) (*-zeroʳ w)))
          (gws-base rest h mono h1)
    where hv≡0 : h (suc v') ≡ 0
          hv≡0 = subst (λ x → h x ≡ 0) (+-comm v' 1)
                   (h-vanish h mono 1 h1 v')

------------------------------------------------------------------------
-- Decomposition: gws d h = gws d h' + c * cdf(d, M)
--
-- where c = h M, h' v = h v ∸ c.
-- Preconditions: h non-increasing, h (suc M) = 0.
-- This is the discrete Abel summation identity.
------------------------------------------------------------------------

private
  gws-split : ∀ (d : Dist ℕ) (h : ℕ → ℕ) (M : ℕ) →
    (∀ v → h (suc v) ≤ h v) →
    h (suc M) ≡ 0 →
    gws d h ≡ gws d (λ v → h v ∸ h M) + h M * cdf-weight d M

  gws-split [] h M mono hsM = sym (*-zeroʳ (h M))

  gws-split ((v , w) ∷ rest) h M mono hsM with v ≤? M
  ... | yes v≤M =
    let c = h M
        ih = gws-split rest h M mono hsM
        hM≤hv : c ≤ h v
        hM≤hv = subst (λ x → h x ≤ h v) (∸+≡ v≤M)
                   (mono-chain h mono (M ∸ v) v)
        hv-eq : h v ≡ (h v ∸ c) + c
        hv-eq = sym (∸+≡ hM≤hv)
    in
    trans (cong₂ _+_ (cong (w *_) hv-eq) ih)
    (trans (cong (_+ (gws rest (λ v → h v ∸ c) + c * cdf-weight rest M))
                 (*-distribˡ-+ w (h v ∸ c) c))
    (trans (rearrange (w * (h v ∸ c)) (w * c)
                      (gws rest (λ v → h v ∸ c)) (c * cdf-weight rest M))
    (cong ((w * (h v ∸ c) + gws rest (λ v → h v ∸ c)) +_)
      (trans (cong (_+ c * cdf-weight rest M) (*-comm w c))
             (sym (*-distribˡ-+ c w (cdf-weight rest M)))))))

  ... | no ¬v≤M =
    trans (cong₂ _+_ whv≡0 ih)
    (sym (cong₂ _+_ (cong (_+ gws rest (λ v₁ → h v₁ ∸ c)) whv∸c≡0) refl))
    where
      c = h M
      ih = gws-split rest h M mono hsM
      v>M : suc M ≤ v
      v>M = ≰⇒> ¬v≤M
      hv≡0 : h v ≡ 0
      hv≡0 = subst (λ x → h x ≡ 0) (∸+≡ v>M)
                (h-vanish h mono (suc M) hsM (v ∸ suc M))
      hv∸c≡0 : h v ∸ c ≡ 0
      hv∸c≡0 = subst (λ x → x ∸ c ≡ 0) (sym hv≡0) (0∸n≡0 c)
      whv≡0 : w * h v ≡ 0
      whv≡0 = trans (cong (w *_) hv≡0) (*-zeroʳ w)
      whv∸c≡0 : w * (h v ∸ c) ≡ 0
      whv∸c≡0 = trans (cong (w *_) hv∸c≡0) (*-zeroʳ w)

------------------------------------------------------------------------
-- The Abel induction: FOSD implies gws dominance for non-increasing h
------------------------------------------------------------------------

fosd-gws : ∀ M {μ ν : Dist ℕ} (h : ℕ → ℕ) →
  total-weight μ ≡ total-weight ν →
  μ FOSD≤ ν →
  (∀ v → h (suc v) ≤ h v) →
  h (suc M) ≡ 0 →
  gws ν h ≤ gws μ h

fosd-gws zero {μ} {ν} h tw fosd mono h1 =
  subst₂ _≤_
    (sym (gws-base ν h mono h1))
    (sym (gws-base μ h mono h1))
    (*-monoʳ-≤ (h 0) (fosd 0))

fosd-gws (suc M) {μ} {ν} h tw fosd mono hssM =
  subst₂ _≤_ (sym decomp-ν) (sym decomp-μ)
    (+-mono-≤ ih (*-monoʳ-≤ c (fosd (suc M))))
  where
    c = h (suc M)
    h' = λ v → h v ∸ c
    h'mono : ∀ v → h' (suc v) ≤ h' v
    h'mono v = ∸-mono (mono v) (≤-refl {c})
    h'sM : h' (suc M) ≡ 0
    h'sM = n∸n≡0 (h (suc M))
    ih = fosd-gws M {μ} {ν} h' tw fosd h'mono h'sM
    decomp-ν = gws-split ν h (suc M) mono hssM
    decomp-μ = gws-split μ h (suc M) mono hssM

------------------------------------------------------------------------
-- FOSD closed under convolution
--
-- If μ₁ FOSD≤ ν₁ (with equal total weights) and μ₂ FOSD≤ ν₂,
-- then conv μ₁ μ₂ FOSD≤ conv ν₁ ν₂.
------------------------------------------------------------------------

FOSD-conv : ∀ {μ₁ ν₁ μ₂ ν₂ : Dist ℕ} →
  total-weight μ₁ ≡ total-weight ν₁ →
  μ₁ FOSD≤ ν₁ → μ₂ FOSD≤ ν₂ →
  conv μ₁ μ₂ FOSD≤ conv ν₁ ν₂
FOSD-conv {μ₁} {ν₁} {μ₂} {ν₂} tw fosd₁ fosd₂ r
  rewrite cdf-conv ν₁ ν₂ r | cdf-conv μ₁ μ₂ r
  = ≤-trans
      (gws-mono ν₁
        {λ v → cdf-weight (fmap (v +_) ν₂) r}
        {λ v → cdf-weight (fmap (v +_) μ₂) r}
        (λ v → FOSD-shift v {μ₂} {ν₂} fosd₂ r))
      (fosd-gws r {μ₁} {ν₁}
        (λ v → cdf-weight (fmap (v +_) μ₂) r) tw fosd₁
        (λ v → shift-cdf-mono μ₂ v r)
        (shift-cdf-zero μ₂ r))

------------------------------------------------------------------------
-- FOSD on inputs lifts convolution to any SD level
------------------------------------------------------------------------

FOSD→SD-conv : ∀ k {μ₁ ν₁ μ₂ ν₂ : Dist ℕ} →
  total-weight μ₁ ≡ total-weight ν₁ →
  μ₁ FOSD≤ ν₁ → μ₂ FOSD≤ ν₂ →
  conv μ₁ μ₂ SD[ k ]≤ conv ν₁ ν₂
FOSD→SD-conv zero    {μ₁} {ν₁} {μ₂} {ν₂} tw f₁ f₂ =
  FOSD-conv {μ₁} {ν₁} {μ₂} {ν₂} tw f₁ f₂
FOSD→SD-conv (suc k) {μ₁} {ν₁} {μ₂} {ν₂} tw f₁ f₂ =
  SD-subsumes k (FOSD→SD-conv k {μ₁} {ν₁} {μ₂} {ν₂} tw f₁ f₂)
