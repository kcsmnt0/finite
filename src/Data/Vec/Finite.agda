open import Finite

module Data.Vec.Finite where

open import Data.List as List
open import Data.List.Any
open import Data.Nat
open import Data.Product
open import Data.Vec as Vec
open import Data.Vec.Membership.Propositional
open import Data.Vec.Membership.Propositional.Properties
open import Data.Vec.Properties
open import Relation.Binary.PropositionalEquality

open IsFinite

instance
  Vec-IsFinite : ∀ {ℓ} {A : Set ℓ} n → IsFinite A → IsFinite (Vec A n)
  elements (Vec-IsFinite zero af) = List.[ [] ]
  elements (Vec-IsFinite (suc n) af) = toList (Vec.map (uncurry _∷_) (allPairs (elementsVec af) (elementsVec (Vec-IsFinite n af))))

  membership (Vec-IsFinite n af) [] = here refl
  membership (Vec-IsFinite (suc n) af) (a ∷ as) =
    ∈-toList⁺
      (∈-map⁺ _
        (∈-allPairs⁺
          (∈-fromList⁺ (membership af a))
          (∈-fromList⁺ (membership (Vec-IsFinite n af) as))))
