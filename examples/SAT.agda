module SAT where

open import Data.Bool renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Bool.Finite
open import Data.Fin
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Data.Vec
open import Data.Vec.Finite
open import Finite
open import Function
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable

infix 5 π_ σ_ δ_
infixr 6 _⇒_ _⇔_
infixr 7 _∨_ _⊻_
infixr 8 _∧_

open IsFinite {{…}}

data Formula : ℕ → Set where
  ⟨_⟩ : ∀ {n} → Fin n → Formula n
  _∧_ : ∀ {n} → Formula n → Formula n → Formula n
  ¬ : ∀ {n} → Formula n → Formula n
  ϟ : ∀ {n} → (Bool → Bool → Bool) → Formula (suc n) → Formula n

_∨_ : ∀ {n} → Formula n → Formula n → Formula n
p ∨ q = ¬ (¬ p ∧ ¬ q)

_⊻_ : ∀ {n} → Formula n → Formula n → Formula n
p ⊻ q = (p ∨ q) ∧ ¬ (p ∧ q)

_⇒_ : ∀ {n} → Formula n → Formula n → Formula n
p ⇒ q = ¬ p ∨ q

_⇔_ : ∀ {n} → Formula n → Formula n → Formula n
p ⇔ q = (p ⇒ q) ∧ (q ⇒ p)

-- all/universal
π_ : ∀ {n} → Formula (suc n) → Formula n
π_ = ϟ _&&_

-- some/existential
σ_ : ∀ {n} → Formula (suc n) → Formula n
σ_ = ϟ _||_

-- one/differential
δ_ : ∀ {n} → Formula (suc n) → Formula n
δ_ = ϟ _xor_

Ctx = Vec Bool

eval : ∀ {n} → Ctx n → Formula n → Bool
eval g ⟨ i ⟩ = lookup i g
eval g (p ∧ q) = eval g p && eval g q
eval g (¬ p) = not (eval g p)
eval g (ϟ _∙_ p) = eval (true ∷ g) p ∙ eval (false ∷ g) p

_⊧_ : ∀ {n} → Ctx n → Formula n → Set
Γ ⊧ p = T (eval Γ p)

_⊧?_ : ∀ {n} (Γ : Ctx n) p → Dec (Γ ⊧ p)
Γ ⊧? p with eval Γ p
… | true = yes tt
… | false = no id

module _ {n} (p : Formula n) where
  valid? = ∀? λ Γ → Γ ⊧? p
  satisfiable? = ∃? λ Γ → Γ ⊧? p

  model : True satisfiable? -> Ctx n
  model = proj₁ ∘ toWitness

∧-comm : True $ valid? {2} $ ⟨ # 0 ⟩ ∧ ⟨ # 1 ⟩ ⇔ ⟨ # 1 ⟩ ∧ ⟨ # 0 ⟩
∧-comm = tt

∀-∧-comm : True $ valid? {0} $ π π ⟨ # 0 ⟩ ∧ ⟨ # 1 ⟩ ⇔ ⟨ # 1 ⟩ ∧ ⟨ # 0 ⟩
∀-∧-comm = tt

∀-∃!-⊻ : True $ valid? {0} $ π δ ⟨ # 0 ⟩ ⊻ ⟨ # 1 ⟩
∀-∃!-⊻ = tt

sat1 : Formula 3
sat1 =
  ((⟨ # 0 ⟩ ∧ ⟨ # 1 ⟩) ∨ (⟨ # 1 ⟩ ∧ ⟨ # 2 ⟩) ∨ (⟨ # 2 ⟩ ∧ ⟨ # 0 ⟩))
    ∧ ¬ (⟨ # 0 ⟩ ∧ ⟨ # 1 ⟩ ∧ ⟨ # 2 ⟩)

sat1-model : Ctx 3
sat1-model = model sat1 tt
