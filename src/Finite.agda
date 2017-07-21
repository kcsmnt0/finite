module Finite where

open import Data.Empty
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Function
open import Level
open import Relation.Nullary

FiniteRec : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} → (A → Set ℓ₂) → Set ℓ₃ → Set _
FiniteRec {A = A} P B = ∀ {m n} (xs : Vec A m) (ys : Vec A n) → (∀ a → (a ∈ xs × P a) ⊎ (a ∈ ys)) → B

record IsFiniteSubset {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor finite
  field
    {size} : ℕ
    elements : Vec A size
    vecMembership : ∀ {a} → P a → a ∈ elements
    setMembership : ∀ {a} → a ∈ elements → P a

  FiniteSubsetRec : ∀ {ℓ₃ ℓ₄} → (A → Set ℓ₃) → Set ℓ₄ → Set _
  FiniteSubsetRec Q B = ∀
    {m n} (xs : Vec A m) (ys : Vec A n) →
    (∀ {a} → (a ∈ xs) ⊎ (a ∈ ys) → P a) →
    (∀ {a} → P a → (a ∈ xs × Q a) ⊎ (a ∈ ys)) →
    B

  finiteSubsetRec : ∀ {ℓ₃ ℓ₄} {Q : A → Set ℓ₃} {B : Set ℓ₄} → FiniteSubsetRec Q B → B
  finiteSubsetRec rec = rec [] elements [ (λ {()}) , setMembership ]′ (inj₂ ∘ vecMembership)

  module _ {ℓ₃} {Q : A → Set ℓ₃} (P? : ∀ a → Dec (P a)) (Q? : ∀ a → Dec (Q a)) where
    any? : Dec (∃ λ a → P a × Q a)
    any? = finiteSubsetRec go
      where
        go : FiniteSubsetRec (¬_ ∘ Q) (Dec (∃ λ a → P a × Q a))
        go xs [] p bin = no λ where
          (a , pa , qa) → case bin pa of λ where
            (inj₁ (_ , ¬qa)) → ¬qa qa
            (inj₂ ())
        go xs (y ∷ ys) p bin = case Q? y of λ where
          (yes qy) → yes (, setMembership (vecMembership loc) , qy)
          (no ¬qy) → go (y ∷ xs) ys p′ λ pa → case bin pa of λ where
            (inj₁ (a∈xs , ¬qa)) → inj₁ (there a∈xs , ¬qa)
            (inj₂ here) → inj₁ (here , ¬qy)
            (inj₂ (there a∈ys)) → inj₂ a∈ys
              where
                loc = p (inj₂ here)

                p′ : ∀ {a} → (a ∈ y ∷ xs) ⊎ (a ∈ ys) → _
                p′ (inj₁ here) = loc
                p′ (inj₁ (there a∈xs)) = p (inj₁ a∈xs)
                p′ (inj₂ a∈ys) = p (inj₂ (there a∈ys))

IsFinite′ : ∀ {ℓ} → Set ℓ → Set _
IsFinite′ A = IsFiniteSubset λ where tt → A

record IsFinite {ℓ₁} (A : Set ℓ₁) : Set ℓ₁ where
  constructor finite
  field
    {size} : ℕ
    elements : Vec A size
    membership : ∀ a → a ∈ elements

  finiteRec : ∀ {ℓ₂ ℓ₃} {B : Set ℓ₂} {P : A → Set ℓ₃} → FiniteRec P B → B
  finiteRec rec = rec [] elements (inj₂ ∘ membership)

  module _ {ℓ₂} {P : A → Set ℓ₂} (¿ : ∀ a → Dec (P a)) where
    any? = finiteRec go
      where
        go : FiniteRec (¬_ ∘ P) _
        go xs [] elem = no λ where
          (a , pa) → case elem a of λ where
            (inj₁ (_ , ¬pa)) → ¬pa pa
            (inj₂ ())
        go xs (y ∷ ys) elem = case ¿ y of λ where
          (yes py) → yes (, py)
          (no ¬py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , ¬pa)) → inj₁ (there a∈xs , ¬pa)
              (inj₂ here) → inj₁ (here , ¬py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    all? = finiteRec go
      where
        go : FiniteRec P _
        go xs [] elem = yes λ a → case elem a of λ where
          (inj₁ (_ , pa)) → pa
          (inj₂ ())
        go xs (y ∷ ys) elem = case ¿ y of λ where
          (no ¬py) → no λ py → ¬py (py _)
          (yes py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , pa)) → inj₁ (there a∈xs , pa)
              (inj₂ here) → inj₁ (here , py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys
