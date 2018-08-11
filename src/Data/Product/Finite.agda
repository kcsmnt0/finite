module Data.Product.Finite where

open import Data.List as List
open import Data.List.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.Product
open import Data.Vec.Properties
open import Finite
open import Function

open IsFinite

instance
  Σ-IsFinite : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} →
    IsFinite A → (∀ a → IsFinite (P a)) → IsFinite (∃ P)
  Σ-IsFinite af pf = finite _ λ where
    (a , p) → ∈-concat⁺′ (∈-map⁺ (membership (pf a) p)) (∈-map⁺ (membership af a))

  ×-IsFinite : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → IsFinite A → IsFinite B → IsFinite (A × B)
  ×-IsFinite af = Σ-IsFinite af ∘ const
