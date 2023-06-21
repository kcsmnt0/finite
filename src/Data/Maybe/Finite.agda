module Data.Maybe.Finite where

open import Data.List as List
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Maybe
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality

instance
  Maybe-IsFinite : ∀ {a} {A : Set a} → {{IsFinite A}} → IsFinite (Maybe A)
  Maybe-IsFinite {{finite es _∈es}} =
    record { membership = maybe (there ∘ ∈-map⁺ _ ∘ _∈es) (here refl) }
