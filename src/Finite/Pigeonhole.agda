module Finite.Pigeonhole where

open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as FinProps
open import Data.Irrelevant as Irrelevant
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product as Σ
open import Data.Sum as ⊎
open import Data.Vec as Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Membership.Propositional.Properties
open import Data.Vec.Properties
open import Data.Vec.Relation.Unary.Any using (Any; here; there; index)
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation

open ≡-Reasoning

open IsFinite

data Repeats {a} {A : Set a} : ∀ {n} → Vec A n → Set a where
  here : ∀ {x n} {xs : Vec A n} → x ∈ xs → Repeats (x ∷ xs)
  there : ∀ {x n} {xs : Vec A n} → Repeats xs → Repeats (x ∷ xs)

Acyclic : ∀ {a n} {A : Set a} → Vec A n → Set _
Acyclic xs = ¬ Repeats xs

repeatedElement : ∀ {a n} {A : Set a} {as : Vec A n} → Repeats as → A
repeatedElement (here {x} _) = x
repeatedElement (there i) = repeatedElement i

firstIndex : ∀ {a n} {A : Set a} {as : Vec A n} (r : Repeats as) → repeatedElement r ∈ as
firstIndex (here _) = here refl
firstIndex (there i) = there (firstIndex i)

secondIndex : ∀ {a n} {A : Set a} {as : Vec A n} (r : Repeats as) → repeatedElement r ∈ as
secondIndex (here i) = there i
secondIndex (there i) = there (secondIndex i)

module _ {a} {A : Set a} (_≟_ : (a b : A) → Dec (a ≡ b)) where
  infix 4 _∈?_
  _∈?_ : ∀ {n} a (as : Vec A n) → Dec (a ∈ as)
  a ∈? [] = no λ ()
  a ∈? b ∷ as =
    case a ≟ b of λ where
      (yes refl) → yes (here refl)
      (no a≢b) → case a ∈? as of λ where
        (yes a∈as) → yes (there a∈as)
        (no a∉as) → no λ where
          (here px) → a≢b px
          (there a∈as) → a∉as a∈as

  repeats? : ∀ {n} (as : Vec A n) → Dec (Repeats as)
  repeats? [] = no λ ()
  repeats? (a ∷ as) =
    case a ∈? as of λ where
      (yes a∈as) → yes (here a∈as)
      (no a∉as) → case repeats? as of λ where
        (yes r) → yes (there r)
        (no ¬r) → no λ where
          (here a∈as) → a∉as a∈as
          (there r) → ¬r r

  acyclic? : ∀ {n} (as : Vec A n) → Dec (Acyclic as)
  acyclic? = ¬? ∘ repeats?

infix 4 _⊆_
_⊆_ : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Set _
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

⊆-inject : ∀ {a m n} {A : Set a} (xs : Vec A m) (ys : Vec A n) → xs ⊆ ys → Fin m → Fin n
⊆-inject xs ys f = index ∘ f ∘ flip ∈-lookup xs

pigeonholeVec : ∀ {a m n} {A : Set a}
  (xs : Vec A m) (ys : Vec A n) →
  n < m →
  (f : Fin m → Fin n) →
  (g : ∀ i → lookup xs i ≡ lookup ys (f i)) →
  ∃₂ λ i j → i ≢ j × lookup xs i ≡ lookup xs j
pigeonholeVec xs ys p f g with FinProps.pigeonhole p f
… | i , j , i<j , q =
      i , j , (λ where refl → n≮n _ i<j) ,
        (begin
          lookup xs i
        ≡⟨ g i ⟩
          lookup ys (f i)
        ≡⟨ cong (lookup ys) q ⟩
          lookup ys (f j)
        ≡⟨ sym (g j) ⟩
          lookup xs j
        ∎)

lookup-repeats : ∀ {a n} {A : Set a}
  (xs : Vec A n) (i j : Fin n) →
  i ≢ j → lookup xs i ≡ lookup xs j → Repeats xs
lookup-repeats (x ∷ xs) zero zero i≢j p = contradiction refl i≢j
lookup-repeats (x ∷ xs) zero (suc j) i≢j refl = here (∈-lookup j xs)
lookup-repeats (x ∷ xs) (suc i) zero i≢j refl = here (∈-lookup i xs)
lookup-repeats (x ∷ xs) (suc i) (suc j) i≢j p = there (lookup-repeats xs i j (i≢j ∘ cong suc) p)

lookup-⊆ : ∀ {a m n} {A : Set a}
  (xs : Vec A m) (ys : Vec A n) →
  (f : Fin m → Fin n) →
  (∀ i → lookup xs i ≡ lookup ys (f i)) →
  xs ⊆ ys
lookup-⊆ .(_ ∷ _) ys f g (here refl) rewrite g zero = ∈-lookup (f zero) ys
lookup-⊆ .(_ ∷ _) ys f g (there i) = lookup-⊆ _ ys (f ∘ suc) (g ∘ suc) i

lookup-index : ∀ {a n} {A : Set a} {x} {xs : Vec A n} (i : x ∈ xs) → x ≡ lookup xs (index i)
lookup-index (here refl) = refl
lookup-index (there i) = lookup-index i

lookup-⊆-≡ : ∀ {a m n} {A : Set a}
  (xs : Vec A m) (ys : Vec A n)
  (f : xs ⊆ ys) →
  ∀ i → lookup xs i ≡ lookup ys (⊆-inject xs ys f i)
lookup-⊆-≡ xs ys f = lookup-index ∘ f ∘ flip ∈-lookup xs

pigeonhole : ∀ {a m n} {A : Set a}
  (xs : Vec A m) (ys : Vec A n) →
  n < m → xs ⊆ ys → Repeats xs
pigeonhole xs ys p f =
  let
    i , j , i≢j , q = pigeonholeVec xs ys p (⊆-inject xs ys f) (lookup-⊆-≡ xs ys f)
  in
    lookup-repeats xs i j i≢j q

finitePigeonhole : ∀ {a n} {A : Set a}
  (af : IsFinite A) (xs : Vec A n) →
  n > size af → Repeats xs
finitePigeonhole af xs p =
  pigeonhole
    xs (fromList (elements af))
      p
      (∈-fromList⁺ ∘ finite-⊆ af ∘ ∈-toList⁺)
