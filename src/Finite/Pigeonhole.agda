module Finite.Pigeonhole where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as ×
open import Data.Sum as ⊎
open import Data.Vec
open import Data.Vec.Properties
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- based on https://github.com/effectfully/random-stuff/blob/master/pigeonhole.agda

open IsFinite

Vec< : ∀ {ℓ} → Set ℓ → ℕ → Set ℓ
Vec< A n = ∃ λ m → m < n × Vec A m

module _ {ℓ} {A : Set ℓ} where
  infix 4 _⊆V_
  _⊆V_ : ∀ {m n} → Vec A m → Vec A n → Set _
  xs ⊆V ys = ∀ {x} → x ∈ xs → x ∈ ys

  data Repeats : ∀ {n} → Vec A n → Set ℓ where
    here : ∀ {x n} {xs : Vec A n} → x ∈ xs → Repeats (x ∷ xs)
    there : ∀ {x n} {xs : Vec A n} → Repeats xs → Repeats (x ∷ xs)

  fromVec< : ∀ {n} (xs : Vec< A n) → Vec A (proj₁ xs)
  fromVec< = proj₂ ∘ proj₂

  remove< : ∀ {x n} {xs : Vec A n} → x ∈ xs → Vec< A n
  remove< {xs = x ∷ xs} here = , ≤-refl , xs
  remove< {xs = x ∷ xs} (there p) = ×.map _ (×.map s≤s (x ∷_)) (remove< p)

  swap-⊆ : ∀ {x y n} {xs : Vec A n} → x ∷ y ∷ xs ⊆V y ∷ x ∷ xs
  swap-⊆ here = there here
  swap-⊆ (there here) = here
  swap-⊆ (there (there e)) = there (there e)

  cut : ∀ {x m n} {xs : Vec A m} {ys : Vec A n} → x ∷ xs ⊆V x ∷ ys → x ∈ xs ⊎ xs ⊆V ys
  cut {xs = []} p = inj₂ λ ()
  cut {xs = x ∷ xs} p with p (there here)
  … | here = inj₁ here
  … | there e = ⊎.map there lem (cut (p ∘ swap-⊆ ∘ there))
        where
          lem = λ p′ → λ where
            here → e
            (there e′) → p′ e′

  bubble : ∀ {x m n} {xs : Vec A m} {ys : Vec A n} →
    x ∷ xs ⊆V ys →
    (e : x ∈ ys) →
    x ∷ xs ⊆V x ∷ fromVec< (remove< e)
  bubble p here e′ = p e′
  bubble p (there e) e′ with p e′
  … | here = there here
  … | there e′′ = swap-⊆ (there (bubble lem e (there e′′)))
        where
          lem : _ ∷ _ ⊆V _
          lem here = e
          lem (there e′′′) = e′′′

  reduceLength : ∀ {x m n} {xs : Vec A m} (e : x ∈ xs) (ys : Vec A n) → m ≤ n → proj₁ (remove< e) < n
  reduceLength here ys le = le
  reduceLength (there e) (y ∷ ys) (s≤s le) = s≤s (reduceLength e ys le)

  pigeonhole : ∀ {m n} (xs : Vec A m) (ys : Vec A n) → xs ⊆V ys → m > n → Repeats xs
  pigeonhole [] ys p ()
  pigeonhole (x ∷ xs) ys p (s≤s gt) with cut (bubble p (p here))
  … | inj₁ e = here e
  … | inj₂ p′ = there (pigeonhole xs (fromVec< (remove< (p here))) p′ (reduceLength (p here) xs gt))

  finitePigeonhole : ∀ {n} (af : IsFinite A) (xs : Vec A n) → n > size af → Repeats xs
  finitePigeonhole af xs =
    pigeonhole
      xs
      (fromList (elements af))
      (List-∈⇒∈ ∘ finite-⊆ af ∘ ∈⇒List-∈)
