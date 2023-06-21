open import Finite

module Data.Sum.Finite where

open import Data.List as List
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Sum
open import Function

open IsFinite

instance
  ⊎-IsFinite : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
    {{IsFinite A}} → {{IsFinite B}} → IsFinite (A ⊎ B)
  ⊎-IsFinite {{af}} {{bf}} = record
    { elements = List.map inj₁ (elements af) List.++ List.map inj₂ (elements bf)
    ; membership =
        [ ∈-++⁺ˡ ∘ ∈-map⁺ _ ∘ membership af
        , ∈-++⁺ʳ _ ∘ ∈-map⁺ _ ∘ membership bf
        ]
    }
