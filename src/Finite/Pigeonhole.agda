module Finite.Pigeonhole where

open import Data.List as List using (List; []; _∷_)
open import Data.List.Any using (here; there; any)
open import Data.List.Any.Membership.Propositional using () renaming (_∈_ to _∈L_)
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

  module _ (_≟_ : (a b : A) → Dec (a ≡ b)) where
    infix 4 _∈?_
    _∈?_ : ∀ {n} a (as : Vec A n) → Dec (a ∈ as)
    a ∈? [] = no λ ()
    a ∈? b ∷ as =
      case a ≟ b of λ where
        (yes refl) → yes here
        (no a≢b) → case a ∈? as of λ where
          (yes a∈as) → yes (there a∈as)
          (no a∉as) → no λ where
            here → a≢b refl
            (there a∈as) → a∉as a∈as

    repeats? : ∀ {n} → (as : Vec A n) → Dec (Repeats as)
    repeats? [] = no λ ()
    repeats? (a ∷ as) =
      case a ∈? as of λ where
        (yes a∈as) → yes (here a∈as)
        (no a∉as) → case repeats? as of λ where
          (yes r) → yes (there r)
          (no ¬r) → no λ where
            (here a∈as) → a∉as a∈as
            (there r) → ¬r r

  id≡toList∘fromList : {xs : List A} → xs ≡ toList (fromList xs)
  id≡toList∘fromList {xs = []} = refl
  id≡toList∘fromList {xs = x ∷ xs} = cong (x ∷_) id≡toList∘fromList

  fromList∘toList-⊆ : ∀ {x n} {xs : Vec A n} → x ∈ fromList (toList xs) → x ∈ xs
  fromList∘toList-⊆ {xs = []} ()
  fromList∘toList-⊆ {xs = x ∷ xs} here = here
  fromList∘toList-⊆ {xs = x ∷ xs} (there e) = there (fromList∘toList-⊆ e)

  List-⊆⇒⊆ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} → (∀ {x} → x ∈L toList xs → x ∈L toList ys) → xs ⊆V ys
  List-⊆⇒⊆ p e = fromList∘toList-⊆ (List-∈⇒∈ (p (∈⇒List-∈ e)))

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
  finitePigeonhole {n} af xs =
    pigeonhole
      xs
      (fromList (elements af))
      (List-∈⇒∈ ∘ finite-⊆ af ∘ ∈⇒List-∈)
