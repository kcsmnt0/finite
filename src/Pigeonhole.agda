{-# OPTIONS --type-in-type #-}

module Pigeonhole where

open import Data.List
open import Data.List.Any
open import Data.List.Any.Membership.Propositional
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum as ⊎
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality

-- based on https://github.com/effectfully/random-stuff/blob/master/pigeonhole.agda

open IsFinite

infixl 6 _–_
_–_ : ∀ {A x} (xs : List A) → x ∈ xs → List A
(x ∷ xs) – (here refl) = xs
(x ∷ xs) – (there e) = x ∷ xs – e

swap-⊆ : ∀ {A x y} {xs : List A} → x ∷ y ∷ xs ⊆ y ∷ x ∷ xs
swap-⊆ (here refl) = there (here refl)
swap-⊆ (there (here refl)) = here refl
swap-⊆ (there (there e)) = there (there e)

cut : ∀ {A x} {xs ys : List A} → x ∷ xs ⊆ x ∷ ys → x ∈ xs ⊎ xs ⊆ ys
cut {xs = []} p = inj₂ λ ()
cut {xs = x ∷ xs} p with p (there (here refl))
… | here refl = inj₁ (here refl)
… | there e = ⊎.map there lem (cut (p ∘ swap-⊆ ∘ there))
      where
        lem = λ p′ → λ where
          (here refl) → e
          (there e′) → p′ e′

bubble : ∀ {A x} {xs ys : List A} → x ∷ xs ⊆ ys → (e : x ∈ ys) → x ∷ xs ⊆ x ∷ ys – e
bubble p (here refl) e′ = p e′
bubble p (there e) e′ with p e′
… | here refl = there (here refl)
… | there e′′ = swap-⊆ (there (bubble lem e (there e′′)))
      where
        lem : _ ∷ _ ⊆ _
        lem (here refl) = e
        lem (there e′′′) = e′′′

reduceLength : ∀ {A x} {xs : List A}
  (e : x ∈ xs) (ys : List A) →
  length xs ≤ length ys →
  length (xs – e) < length ys
reduceLength (here refl) ys le = le
reduceLength (there e) [] ()
reduceLength (there e) (y ∷ ys) (s≤s le) = s≤s (reduceLength e ys le)

data Repeats {A} : List A → Set where
  here : ∀ {x xs} → x ∈ xs → Repeats (x ∷ xs)
  there : ∀ {x xs} → Repeats xs → Repeats (x ∷ xs)

pigeonhole : ∀ {A} (xs ys : List A) → xs ⊆ ys → length xs > length ys → Repeats xs
pigeonhole [] ys p ()
pigeonhole (x ∷ xs) ys p (s≤s gt) with cut (bubble p (p (here refl)))
… | inj₁ e = here e
… | inj₂ p′ = there (pigeonhole xs (ys – p (here refl)) p′ (reduceLength (p (here refl)) xs gt))

finitePigeonhole : ∀ {A} (af : IsFinite A) (xs : List A) → length xs > size af → Repeats xs
finitePigeonhole af xs = pigeonhole xs (elements af) (finiteSubset af)
