{-# OPTIONS --type-in-type #-}

module Finite.Pigeonhole where

open import Data.List as List using (List; []; _∷_)
open import Data.List.Any using (here; there)
open import Data.List.Any.Membership.Propositional using () renaming (_⊆_ to _⊆L_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as ×
open import Data.Sum as ⊎
open import Data.Vec
open import Data.Vec.Properties
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality

-- based on https://github.com/effectfully/random-stuff/blob/master/pigeonhole.agda

open IsFinite

infix 4 _⊆V_
_⊆V_ : ∀ {A m n} → Vec A m → Vec A n → Set
xs ⊆V ys = ∀ {x} → x ∈ xs → x ∈ ys

data Repeats {A} : ∀ {n} → Vec A n → Set where
  here : ∀ {x n} {xs : Vec A n} → x ∈ xs → Repeats (x ∷ xs)
  there : ∀ {x n} {xs : Vec A n} → Repeats xs → Repeats (x ∷ xs)

id≡toList∘fromList : ∀ {A} {xs : List A} → xs ≡ toList (fromList xs)
id≡toList∘fromList {xs = []} = refl
id≡toList∘fromList {xs = x ∷ xs} = cong (x ∷_) id≡toList∘fromList

fromList∘toList-⊆ : ∀ {A x n} {xs : Vec A n} → x ∈ fromList (toList xs) → x ∈ xs
fromList∘toList-⊆ {xs = []} ()
fromList∘toList-⊆ {xs = x ∷ xs} here = here
fromList∘toList-⊆ {xs = x ∷ xs} (there e) = there (fromList∘toList-⊆ e)

List-⊆⇒⊆ : ∀ {A m n} {xs : Vec A m} {ys : Vec A n} → toList xs ⊆L toList ys → xs ⊆V ys
List-⊆⇒⊆ p e = fromList∘toList-⊆ (List-∈⇒∈ (p (∈⇒List-∈ e)))

Vec< : Set → ℕ → Set
Vec< A n = ∃ λ m → m < n × Vec A m

fromVec< : ∀ {A n} (xs : Vec< A n) → Vec A (proj₁ xs)
fromVec< = proj₂ ∘ proj₂

remove : ∀ {A x n} {xs : Vec A n} → x ∈ xs → Vec< A n
remove {xs = x ∷ xs} here = , ≤-refl , xs
remove {xs = x ∷ xs} (there p) = ×.map _ (×.map s≤s (x ∷_)) (remove p)

swap-⊆ : ∀ {A x y n} {xs : Vec A n} → x ∷ y ∷ xs ⊆V y ∷ x ∷ xs
swap-⊆ here = there here
swap-⊆ (there here) = here
swap-⊆ (there (there e)) = there (there e)

cut : ∀ {A x m n} {xs : Vec A m} {ys : Vec A n} → x ∷ xs ⊆V x ∷ ys → x ∈ xs ⊎ xs ⊆V ys
cut {xs = []} p = inj₂ λ ()
cut {xs = x ∷ xs} p with p (there here)
… | here = inj₁ here
… | there e = ⊎.map there lem (cut (p ∘ swap-⊆ ∘ there))
      where
        lem = λ p′ → λ where
          here → e
          (there e′) → p′ e′

bubble : ∀ {A x m n} {xs : Vec A m} {ys : Vec A n} →
  x ∷ xs ⊆V ys →
  (e : x ∈ ys) →
  x ∷ xs ⊆V x ∷ fromVec< (remove e)
bubble p here e′ = p e′
bubble p (there e) e′ with p e′
… | here = there here
… | there e′′ = swap-⊆ (there (bubble lem e (there e′′)))
      where
        lem : _ ∷ _ ⊆V _
        lem here = e
        lem (there e′′′) = e′′′

reduceLength : ∀ {A x m n} {xs : Vec A m} (e : x ∈ xs) (ys : Vec A n) → m ≤ n → proj₁ (remove e) < n
reduceLength here ys le = le
reduceLength (there e) (y ∷ ys) (s≤s le) = s≤s (reduceLength e ys le)

pigeonhole : ∀ {A m n} (xs : Vec A m) (ys : Vec A n) → xs ⊆V ys → m > n → Repeats xs
pigeonhole [] ys p ()
pigeonhole (x ∷ xs) ys p (s≤s gt) with cut (bubble p (p here))
… | inj₁ e = here e
… | inj₂ p′ = there (pigeonhole xs (fromVec< (remove (p here))) p′ (reduceLength (p here) xs gt))

finitePigeonhole : ∀ {A n} (af : IsFinite A) (xs : Vec A n) → n > size af → Repeats xs
finitePigeonhole {A} {n} af xs =
  pigeonhole
    xs
    (fromList (elements af))
    (List-⊆⇒⊆ (subst (toList xs ⊆L_) id≡toList∘fromList (finite-⊆ af)))
