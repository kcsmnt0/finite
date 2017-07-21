module Data.Fin.Finite where

open import Data.Fin
open import Data.Vec
open import Data.Vec.Properties
open import Finite

instance
  Fin-IsFinite : ∀ {n} → IsFinite (Fin n)
  Fin-IsFinite = finite _ ∈-allFin
