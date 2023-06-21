module Data.Bool.Finite where

open import Data.Bool
open import Data.List
open import Data.List.Relation.Unary.Any
open import Finite
open import Relation.Binary.PropositionalEquality

instance
  Bool-IsFinite : IsFinite Bool
  Bool-IsFinite = finite (true ∷ false ∷ []) λ where true → here refl; false → there (here refl)
