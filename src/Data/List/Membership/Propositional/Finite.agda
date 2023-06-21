module Data.List.Membership.Propositional.Finite where

open import Finite
open import Data.List as List
open import Data.List.Membership.Propositional as ∈
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.List.Relation.Unary.Any as Any
open import Data.Product as ×
open import Relation.Binary.PropositionalEquality as ≡

instance
  ∈-IsFinite : ∀ {a} {A : Set a} {xs : List A} → IsFinite (∃ (_∈ xs))
  ∈-IsFinite {xs = []} = finite [] λ ()
  ∈-IsFinite {xs = x ∷ xs} =
    let finite es _∈es = ∈-IsFinite in
      finite ((-, here refl) ∷ List.map (×.map _ there) es) λ where
        (_ , here refl) → here refl
        (_ , there i) → there (∈-map⁺ _ ((-, i) ∈es))
