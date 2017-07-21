module Data.Bool.Finite where

open import Data.Bool
open import Data.Vec
open import Finite

instance
  Bool-IsFinite : IsFinite Bool
  Bool-IsFinite = finite (true ∷ false ∷ []) λ where true → here; false → there here
