module Finite where

open import Data.Empty
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Function
open import Level
open import Relation.Nullary

FiniteRec : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} → (A → Set ℓ₂) → Set ℓ₃ → Set _
FiniteRec {A = A} P B = ∀ {m n} (xs : Vec A m) (ys : Vec A n) → (∀ a → (a ∈ xs × P a) ⊎ (a ∈ ys)) → B

record IsFinite {ℓ₁} (A : Set ℓ₁) : Set ℓ₁ where
  constructor finite
  field
    {size} : ℕ
    elements : Vec A size
    membership : ∀ a → a ∈ elements

  finiteRec : ∀ {ℓ₂ ℓ₃} {B : Set ℓ₂} {P : A → Set ℓ₃} → FiniteRec P B → B
  finiteRec rec = rec [] elements (inj₂ ∘ membership)

  module _ {ℓ₂} {P : A → Set ℓ₂} (¿ : ∀ a → Dec (P a)) where
    ∃? = finiteRec go
      where
        go : FiniteRec (¬_ ∘ P) _
        go xs [] elem = no λ where
          (a , pa) → case elem a of λ where
            (inj₁ (_ , ¬pa)) → ¬pa pa
            (inj₂ ())
        go xs (y ∷ ys) elem = case ¿ y of λ where
          (yes py) → yes (, py)
          (no ¬py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , ¬pa)) → inj₁ (there a∈xs , ¬pa)
              (inj₂ here) → inj₁ (here , ¬py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    ∀? = finiteRec go
      where
        go : FiniteRec P _
        go xs [] elem = yes λ a → case elem a of λ where
          (inj₁ (_ , pa)) → pa
          (inj₂ ())
        go xs (y ∷ ys) elem = case ¿ y of λ where
          (no ¬py) → no λ py → ¬py (py _)
          (yes py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , pa)) → inj₁ (there a∈xs , pa)
              (inj₂ here) → inj₁ (here , py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys
