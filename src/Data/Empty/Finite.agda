module Data.Empty.Finite where

open import Data.Empty
open import Data.List
open import Finite

instance
  ⊥-IsFinite : IsFinite ⊥
  ⊥-IsFinite = finite [] λ ()
