open import Finite

module Data.Vec.Finite {ℓ₁} {A : Set ℓ₁} {{_ : IsFinite A}} where

open import Data.Nat
open import Data.Product
open import Data.Vec as Vec
open import Data.Vec.Properties

open IsFinite {{…}}

infixr 8 _^_

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc y = x * x ^ y

instance
  Vec-IsFinite : ∀ {n} → IsFinite (Vec A n)

  size {{Vec-IsFinite {n}}} = size {_}{A} ^ n

  elements {{Vec-IsFinite {zero}}} = [ [] ]
  elements {{Vec-IsFinite {suc n}}} = Vec.map (uncurry _∷_) (allPairs elements elements)

  membership {{Vec-IsFinite}} [] = here
  membership {{Vec-IsFinite}} (a ∷ as) = ∈-map _ (∈-allPairs (membership a) (membership as))
