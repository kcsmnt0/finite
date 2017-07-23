open import Finite

module Data.Sum.Finite {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {{_ : IsFinite A}} {{_ : IsFinite B}} where

open import Data.Sum
open import Data.Vec as Vec
open import Data.Vec.Properties

open IsFinite {{…}}

instance
  ⊎-IsFinite : IsFinite (A ⊎ B)
  ⊎-IsFinite = finite (Vec.map inj₁ elements ++ Vec.map inj₂ elements) λ where
    (inj₁ a) → ∈-++ₗ (∈-map inj₁ (membership a))
    (inj₂ b) → ∈-++ᵣ (Vec.map inj₁ elements) (∈-map inj₂ (membership b))
