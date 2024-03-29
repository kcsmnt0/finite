{-# OPTIONS --type-in-type #-}

module Finite.Deriving where

open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Empty
open import Data.List as List hiding (filter)
open import Data.List.Properties as ListProps
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Finite
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.Nat.Induction as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Product as Σ
open import Data.Product.Finite as Σ
open import Data.Sum as ⊎
open import Data.Unit as ⊤
open import Finite
open import Function
open import Function.Construct.Composition
open import Function.Equality as Π using (_⟨$⟩_; cong)
open import Induction.WellFounded
open import Relation.Binary
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; refl; subst)
open import Relation.Nullary as Nullary
open import Relation.Nullary.Decidable as Decidable
open import Relation.Nullary.Negation
import Relation.Unary as Unary

module Desc (I : Set) where
  data Desc : Set where
    arg : ∀ A → (I → List A) → (A → Desc) → Desc
    rec : I → Desc → Desc
    ret : I → Desc

  module FiniteDesc
    (_<_ : I → I → Set)
    (<-wellFounded : WellFounded _<_)
    (<-IsFinite : (i j : I) → IsFinite (i < j))
    (≡-IsFinite : (i j : I) → IsFinite (i ≡ j))
    where

    data Struct (R : Desc) : Desc → I → Set where
      arg : ∀ {i A ι D} (a : A) → a ∈ ι i → Struct R (D a) i → Struct R (arg A ι D) i
      rec : ∀ {i h D} → h < i → Struct R R h → Struct R D i → Struct R (rec h D) i
      ret : ∀ {i} → Struct R (ret i) i

    Data : Desc → I → Set
    Data D = Struct D D

    Struct-IsFinite : ∀
      {R} i →
      WfRec _<_ (λ j → ∀ D → IsFinite (Struct R D j)) i →
      ∀ D → IsFinite (Struct R D i)
    Struct-IsFinite i ind (arg A ι D) =
      via-left-inverse
        (Σ-IsFinite {{∈-IsFinite}} {{λ where {a , _} → Struct-IsFinite i ind (D a)}})
        record
          { to = λ where ((a , ix) , x) → arg a ix x
          ; from = λ where (arg a ix x) → ((a , ix) , x)
          ; to-cong = λ where refl → refl
          ; from-cong = λ where refl → refl
          ; inverseˡ = λ where (arg _ _ _) → refl
          }
    Struct-IsFinite {R} i ind (rec j D) =
      via-left-inverse (Σ-IsFinite {{<-IsFinite j i}} {{λ {j<i} → ×-IsFinite {{ind j j<i R}} {{Struct-IsFinite i ind D}}}}) record
        { to = λ where (j<i , x , y) → rec j<i x y
        ; from = λ where (rec j<i x y) → (j<i , x , y)
        ; to-cong = λ where refl → refl
        ; from-cong = λ where refl → refl
        ; inverseˡ = λ where (rec j<i x y) → refl
        }
    Struct-IsFinite i ind (ret j) =
      via-left-inverse (≡-IsFinite i j) record
        { to = λ where refl → ret
        ; from = λ where ret → refl
        ; to-cong = λ where refl → refl
        ; from-cong = λ where refl → refl
        ; inverseˡ = λ where ret → refl
        }

    Data-IsFinite : ∀ D i → IsFinite (Data D i)
    Data-IsFinite D i = All.wfRec <-wellFounded _ _ Struct-IsFinite i D

module `Fin where
  open MinimalEnumeration
  open import Data.Fin as Fin
  open Desc ℕ
  open FiniteDesc
    ℕ._<_
    ℕ.<-wellFounded
    (λ i j → via-irrelevant-dec ℕ.<-irrelevant (i ℕ.<? j))
    (λ i j → via-irrelevant-dec ℕ.≡-irrelevant (i ℕ.≟ j))

  `zero＠ : ℕ → Desc
  `zero＠ n = ret (suc n)

  `suc＠ : ℕ → Desc
  `suc＠ n = rec n (ret (suc n))

  `Fin＠ : ℕ → Desc
  `Fin＠ n = arg Bool (λ _ → true ∷ false ∷ []) (if_then `suc＠ n else `zero＠ n)

  `Fin : Desc
  `Fin = arg ℕ (List.[_] ∘ ℕ.pred) `Fin＠

  `zero : ∀ {n} → Data `Fin (suc n)
  `zero {n} =
    Struct.arg n (here refl)
      (arg false (there (here refl))
        ret)

  `sucBy : ∀ {n} → n ℕ.< suc n → Data `Fin n → Data `Fin (suc n)
  `sucBy {n} n<1+n i =
    arg n (here refl)
      (arg true (here refl)
        (rec n<1+n i
          ret))

  `suc : ∀ {n} → Data `Fin n → Data `Fin (suc n)
  `suc = `sucBy ≤-refl

  ¬`Fin₀ : ¬ Data `Fin zero
  ¬`Fin₀ (arg .(ℕ.pred zero) (here refl) (arg .true (here refl) (rec x i _))) = ¬`Fin₀ i
  ¬`Fin₀ (arg .(ℕ.pred zero) (here refl) (arg true (there (here ())) i))
  ¬`Fin₀ (arg .(ℕ.pred zero) (here refl) (arg true (there (there ())) i))

  `Fin→Fin : ∀ {n} → Data `Fin n → Fin n
  `Fin→Fin {zero} i = contradiction i ¬`Fin₀
  `Fin→Fin {suc n} (arg _ (here refl) (arg .false (there (here refl)) ret)) = zero
  `Fin→Fin {suc n} (arg _ (here refl) (arg .true (here refl) (rec x i ret))) = suc (`Fin→Fin i)

  Fin→`Fin : ∀ {n} → Fin n → Data `Fin n
  Fin→`Fin zero = `zero
  Fin→`Fin (suc i) = `suc (Fin→`Fin i)

  Fin→`Fin→Fin≗id : ∀ {n} → `Fin→Fin {n} ∘ Fin→`Fin ≗ id
  Fin→`Fin→Fin≗id zero = refl
  Fin→`Fin→Fin≗id (suc i) = ≡.cong suc (Fin→`Fin→Fin≗id i)

  `Fin→Fin→`Fin≗id : ∀ {n} → Fin→`Fin {n} ∘ `Fin→Fin ≗ id
  `Fin→Fin→`Fin≗id {zero} (arg _ (here refl) i) = contradiction i (¬`Fin₀ ∘ arg _ (here refl))
  `Fin→Fin→`Fin≗id {suc n} (arg _ (here refl) (arg .false (there (here refl)) ret)) = refl
  `Fin→Fin→`Fin≗id {suc n} (arg _ (here refl) (arg .true (here refl) (rec lt i ret))) =
    ≡.cong₂ `sucBy (≤-irrelevant _ _) (`Fin→Fin→`Fin≗id i)

  Fin↔`Fin : ∀ {n} → Fin n ↔ Data `Fin n
  Fin↔`Fin = mk↔ {to = Fin→`Fin} (`Fin→Fin→`Fin≗id , Fin→`Fin→Fin≗id)

  Data-complete : ∀ {A : Set} (A… : IsFinite A) → (A ↔ Data `Fin (cardinality A…))
  Data-complete A… = minimalNumbering (Finite.deduplicate A…) ↔-∘ Fin↔`Fin
