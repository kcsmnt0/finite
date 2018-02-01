open import Finite

module Data.Sum.Finite where

open import Data.List as List
open import Data.Vec as Vec
open import Data.Vec.Properties
open import Data.Sum

open IsFinite

instance
  ⊎-IsFinite : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → IsFinite A → IsFinite B → IsFinite (A ⊎ B)
  ⊎-IsFinite af bf = finite _ λ where
    (inj₁ a) → ∈⇒List-∈ (∈-++ₗ (∈-map inj₁ (List-∈⇒∈ (membership af a))))
    (inj₂ b) → ∈⇒List-∈ (∈-++ᵣ (Vec.map inj₁ (elementsVec af)) (∈-map inj₂ (List-∈⇒∈ (membership bf b))))
