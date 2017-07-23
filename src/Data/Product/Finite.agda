open import Finite

module Data.Product.Finite {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {{_ : IsFinite A}} {{_ : IsFinite B}} where

open import Data.Product
open import Data.Vec
open import Data.Vec.Properties

open IsFinite {{…}}

instance
  ×-IsFinite : IsFinite (A × B)
  ×-IsFinite = finite (allPairs elements elements) λ where
    (a , b) → ∈-allPairs (membership a) (membership b)
