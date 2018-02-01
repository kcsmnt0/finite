module Data.Product.Finite where

open import Data.List
open import Data.Product
open import Data.Vec
open import Data.Vec.Properties
open import Finite

open IsFinite

instance
  ×-IsFinite : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → IsFinite A → IsFinite B → IsFinite (A × B)
  ×-IsFinite af bf = finite _ λ where
    (a , b) → ∈⇒List-∈ (∈-allPairs (List-∈⇒∈ (membership af a)) (List-∈⇒∈ (membership bf b)))
