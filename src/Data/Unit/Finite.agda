module Data.Unit.Finite where

open import Data.List
open import Data.List.Any
open import Data.Unit
open import Finite
open import Relation.Binary.PropositionalEquality using (refl)

instance
  ⊤-IsFinite : IsFinite ⊤
  ⊤-IsFinite = finite [ tt ] λ where tt → here refl
