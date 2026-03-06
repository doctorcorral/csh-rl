# Agda Bug Report Prompt (for another agent)

## Task

Report the following bug to the Agda team (GitHub: https://github.com/agda/agda/issues).

## Bug Summary

**Title:** Type inference error "B != A" when proving monad bind lemma for list-like Kleisli structure

**Agda version:** 2.8.0

**Environment:** macOS, standard-library

## Description

When defining a Kleisli extension (`>>=`) for a list-based monad (`Dist A = List (A × ℕ)`), the module typechecks. However, adding a simple correctness lemma `>>=-singleton` causes Agda to report:

```
B != A of type Set
when checking that the expression [] >>= f has type
List (Data.Product.Σ A (λ v → ℕ))
```

The lemma is mathematically trivial: `(x , w) ∷ [] >>= f ≡ scale w (f x)`, provable by `++-identityʳ`. The error suggests Agda infers the wrong expected type (`List (A × ℕ)`) for `[] >>= f` instead of the correct `List (B × ℕ)`.

**Without the lemma:** module typechecks ✓  
**With the lemma:** B != A error ✗

## Minimal Reproduction

**Standalone file** (create `Bug.agda` in a fresh project with standard-library):

```agda
{-# OPTIONS --safe #-}
module Bug where

open import Data.Nat using (ℕ; _*_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.Properties using (++-identityʳ)

Dist : Set → Set
Dist A = List (A × ℕ)

scale : ∀ {A} → ℕ → Dist A → Dist A
scale k = map (λ { (a , w) → a , k * w })

join : ∀ {A} → Dist (Dist A) → Dist A
join [] = []
join ((d , w) ∷ dd) = scale w d ++ join dd

mapK : ∀ {A B} → (A → Dist B) → Dist A → Dist (Dist B)
mapK f = map (λ { (a , w) → f a , w })

_>>=_ : ∀ {A B} → Dist A → (A → Dist B) → Dist B
d >>= f = join (mapK f d)

-- BUG: Comment out the next 4 lines and the module typechecks
>>=-singleton : ∀ {A B} (x : A) (w : ℕ) (f : A → Dist B) →
  (x , w) ∷ [] >>= f ≡ scale w (f x)
>>=-singleton x w f = ++-identityʳ (scale w (f x))
```

To reproduce: `agda Bug.agda` (with standard-library in path).  
To verify fix: comment out `>>=-singleton`; module should typecheck.

## Expected Behavior

The lemma should typecheck. The definition `d >>= f = join (mapK f d)` correctly produces `Dist B` for all inputs; the empty case reduces to `join [] = []` which has type `Dist B` when the context expects it.

## Possible Cause

The presence of the lemma may trigger additional bidirectional type-checking or constraint propagation that incorrectly unifies the result type of `[] >>= f` with `List (A × ℕ)` (from the first argument's type) instead of `List (B × ℕ)` (from the return type).

## Additional Note

A separate internal error (`__IMPOSSIBLE__` in `Serialise/Instances/Common.hs:311`) occurs when typechecking larger modules that import this code (e.g. `GamblersRuinFOSDSynth`). This may or may not be related.
