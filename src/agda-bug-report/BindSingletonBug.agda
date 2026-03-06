{-# OPTIONS --safe #-}
-- Minimal reproduction for Agda type-inference bug:
-- When >>=-singleton is present, Agda reports:
--   B != A of type Set
--   when checking that the expression [] >>= f has type List (Σ A (λ v → ℕ))

module agda-bug-report.BindSingletonBug where

open import Data.Nat using (ℕ; _*_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.List.Properties using (++-identityʳ)

Dist : Set → Set
Dist A = List (A × ℕ)

scale : ∀ {A} → ℕ → Dist A → Dist A
scale k = map (λ { (a , w) → a , k * w })

-- Join first (avoids [] >>= f in definition)
join : ∀ {A} → Dist (Dist A) → Dist A
join [] = []
join ((d , w) ∷ dd) = scale w d ++ join dd

mapK : ∀ {A B} → (A → Dist B) → Dist A → Dist (Dist B)
mapK f = map (λ { (a , w) → f a , w })

_>>=_ : ∀ {A B} → Dist A → (A → Dist B) → Dist B
d >>= f = join (mapK f d)

>>=-singleton : ∀ {A B} (x : A) (w : ℕ) (f : A → Dist B) →
  ((x , w) ∷ []) >>= f ≡ scale w (f x)
>>=-singleton x w f = ++-identityʳ (scale w (f x))
