module Finite where

open import Data.Empty
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Properties as Fin using (suc-injective)
open import Data.List as List using (List; []; _∷_; length; [_])
open import Data.List.Properties as ListProps
open import Data.List.Membership.Propositional as ∈
open import Data.List.Membership.Propositional.Properties as ∈ hiding (finite)
open import Data.List.Membership.Setoid.Properties as ∈ using (unique⇒irrelevant)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties as Any
open import Data.List.Relation.Unary.Enumerates.Setoid as Enumerates
open import Data.List.Relation.Unary.Enumerates.Setoid.Properties as Enumerates
open import Data.Nat as ℕ using (ℕ; zero; suc)
import Data.List.Relation.Unary.Unique.DecPropositional
open import Data.List.Relation.Unary.Unique.DecPropositional.Properties
open import Data.Product as Σ
open import Data.Sum as ⊎
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Unit as ⊤ using (⊤; tt)
open import Function
open import Function.Consequences
open import Level as ℓ using (Level)
open import Relation.Binary as Binary
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; refl; subst)
open import Relation.Binary.PropositionalEquality.WithK as ≡
open import Relation.Nullary as Nullary
open import Relation.Nullary.Decidable as Dec using (True; fromWitness; toWitness)
open import Relation.Nullary.Negation

open ≡.≡-Reasoning

fromWitness∘toWitness≗id : ∀ {ℓ} {A : Set ℓ} {A? : Dec A} → fromWitness {a? = A?} ∘ toWitness ≗ id
fromWitness∘toWitness≗id {A? = A?} with A?
… | yes a = λ where tt → refl
… | no ¬a = λ ()

indexElement-injective : ∀
  {ℓ} {A : Set ℓ} {x y : A} {xs}
  (i : x ∈ xs) (j : y ∈ xs) →
  index i ≡ index j →
  x ≡ y
indexElement-injective (here refl) (here refl) eq = refl
indexElement-injective (here refl) (there j) ()
indexElement-injective (there i) (here refl) ()
indexElement-injective (there i) (there j) eq = indexElement-injective i j (suc-injective eq)

index-∈-lookup : ∀ {ℓ} {A : Set ℓ} {xs : List A} i → index (∈-lookup {xs = xs} i) ≡ i
index-∈-lookup {xs = x ∷ xs} zero = refl
index-∈-lookup {xs = x ∷ xs} (suc i) = ≡.cong suc (index-∈-lookup {xs = xs} i)

FiniteRec : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} → (A → List A → Set ℓ₂) → Set ℓ₃ → Set _
FiniteRec P B = ∀ xs ys → (∀ a → (a ∈ xs × P a xs) ⊎ (a ∈ ys)) → B

record IsFinite {ℓ₁} (A : Set ℓ₁) : Set ℓ₁ where
  constructor finite
  field
    elements : List A
    membership : IsEnumeration (≡.setoid A) elements

  size = length elements
  elementsVec = Vec.fromList elements
  indexOf = index ∘ membership

  finite-⊆ : ∀ {xs} → xs ⊆ elements
  finite-⊆ {x = x} _ = membership x

  finiteRec : ∀ {ℓ₂ ℓ₃} {B : Set ℓ₂} {P : A → List A → Set ℓ₃} → FiniteRec P B → B
  finiteRec rec = rec [] elements (inj₂ ∘ membership)

  numbering : A ↣ Fin size
  numbering = mk↣ (indexElement-injective (membership _) (membership _))

  dec : Dec A
  dec with elements | membership
  dec | [] | _∈[] = no λ a → case a ∈[] of λ ()
  dec | a ∷ as | _ = yes a

  _≟_ : DecidableEquality A
  x ≟ y with indexOf x Fin.≟ indexOf y
  … | yes i≡j = yes (indexElement-injective (membership x) (membership y) i≡j)
  … | no i≢j = no λ where refl → i≢j refl

  decSetoid : DecSetoid ℓ₁ ℓ₁
  decSetoid = ≡.decSetoid _≟_

  _≤_ : REL A _ _
  x ≤ y = indexOf x Fin.≤ indexOf y

  _<_ : REL A _ _
  x < y = indexOf x Fin.< indexOf y

  module _ {ℓ₂} {P : A → Set ℓ₂} (P? : ∀ a → Dec (P a)) where
    ∃? : Dec (∃ P)
    ∃? = finiteRec go
      where
        go : FiniteRec (λ a _ → ¬ P a) _
        go xs [] elem = no λ where
          (a , pa) → case elem a of λ where
            (inj₁ (_ , ¬pa)) → ¬pa pa
            (inj₂ ())
        go xs (y ∷ ys) elem = case P? y of λ where
          (yes py) → yes (-, py)
          (no ¬py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , ¬pa)) → inj₁ (there a∈xs , ¬pa)
              (inj₂ (here refl)) → inj₁ (here refl , ¬py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    ∀? : Dec (∀ x → P x)
    ∀? = finiteRec go
      where
        go : FiniteRec (λ a _ → P a) _
        go xs [] elem = yes λ a → case elem a of λ where
          (inj₁ (_ , pa)) → pa
          (inj₂ ())
        go xs (y ∷ ys) elem = case P? y of λ where
          (no ¬py) → no λ py → ¬py (py _)
          (yes py) → go (y ∷ xs) ys λ a →
            case elem a of λ where
              (inj₁ (a∈xs , pa)) → inj₁ (there a∈xs , pa)
              (inj₂ (here refl)) → inj₁ (here refl , py)
              (inj₂ (there a∈ys)) → inj₂ a∈ys

    filter-∃ : List A → List (∃ P)
    filter-∃ [] = []
    filter-∃ (a ∷ as) =
      case P? a of λ where
        (yes pa) → (-, pa) ∷ filter-∃ as
        (no ¬pa) → filter-∃ as

    filter-∃-∈ : ∀ {a as} → a ∈ as → (pa : True (P? a)) → (a , toWitness pa) ∈ filter-∃ as
    filter-∃-∈ {as = a ∷ as} (here refl) pa with P? a
    filter-∃-∈ (here refl) pa | yes pa′ = here refl
    filter-∃-∈ (here refl) () | no ¬pa
    filter-∃-∈ {as = a ∷ as} (there e) pa with P? a
    filter-∃-∈ (there e) pa | yes pa′ = there (filter-∃-∈ e pa)
    filter-∃-∈ (there e) pa | no ¬pa = filter-∃-∈ e pa

    filter-∃-True : List A → List (∃ (True ∘ P?))
    filter-∃-True = List.map (Σ.map₂ fromWitness) ∘ filter-∃

    filter-∃-True-∈ : ∀ {a as} → a ∈ as → (pa : True (P? a)) → (a , pa) ∈ filter-∃-True as
    filter-∃-True-∈ {a} e pa =
      subst
        (λ pa′ → (a , pa′) ∈ _)
        (fromWitness∘toWitness≗id _)
        (∈-map⁺ _ (filter-∃-∈ e pa))

    filter : IsFinite (∃ (True ∘ P?))
    filter = record
      { elements = filter-∃-True elements
      ; membership = λ where (a , pa) → filter-∃-True-∈ (membership a) pa
      }

  module Ordered {ℓ₂ ℓ₃} {_≈_ : A → A → Set ℓ₂} {_<_ : A → A → Set ℓ₃}
    (<-po : IsDecStrictPartialOrder _≈_ _<_)
    where
    open IsDecStrictPartialOrder <-po

    _≮_ : A → A → Set _
    a ≮ b = ¬ (a < b)

    Maximal : A → Set _
    Maximal x = ∀ y → x ≮ y

    maxOf : A → ∀ as → ∃ λ a → ∀ {x} → x ∈ as → a ≮ x
    maxOf p [] = p , λ ()
    maxOf p (a ∷ as) =
      let x , f = maxOf p as in
        case (a <? x) ,′ (x <? a) of λ where
          (yes a<x , _) → x , λ {y} y∈a∷as x<y →
            case y∈a∷as of λ where
              (here refl) → asym x<y a<x
              (there y∈as) → f y∈as x<y
          (_ , yes x<a) → a , λ {y} y∈a∷as a<y →
            case y∈a∷as of λ where
              (here refl) → irrefl Eq.refl a<y
              (there y∈as) → f y∈as (trans x<a a<y)
          (no a≮x , no x≮a) → x , λ {y} y∈a∷as x<y →
            case y∈a∷as of λ where
              (here refl) → x≮a x<y
              (there y∈as) → f y∈as x<y

    max : (¬ A) ⊎ (∃ Maximal)
    max =
      case dec of λ where
        (yes a) → let x , m = maxOf a elements in inj₂ (x , (m ∘ membership))
        (no ¬a) → inj₁ ¬a

    pointedMax : A → ∃ Maximal
    pointedMax x =
      case max of λ where
        (inj₁ ¬a) → contradiction x ¬a
        (inj₂ a) → a

record MinimalEnumeration {ℓ} (A : Set ℓ) : Set ℓ where
  field
    isFinite : IsFinite A

  open IsFinite isFinite public
  open Data.List.Relation.Unary.Unique.DecPropositional _≟_

  field
    unique : Unique elements

  ∈-unique : ∀ {x} (i j : x ∈ elements) → i ≡ j
  ∈-unique = ∈.unique⇒irrelevant (≡.setoid _) ≡-irrelevant unique

  indexOfUnique : ∀ i → indexOf (List.lookup elements i) ≡ i
  indexOfUnique i =
    begin
      indexOf (List.lookup elements i)
    ≡⟨ ≡.cong index (∈-unique (membership (List.lookup elements i)) (∈-lookup i)) ⟩
      index (∈-lookup i)
    ≡⟨ index-∈-lookup i ⟩
      i
    ∎

  minimalNumbering : A ↔ Fin (length elements)
  minimalNumbering =
    mk↔ {to = indexOf}
      ((λ where refl → indexOfUnique _) , λ where refl → ≡.sym (lookup-index (membership _)))

module _ {ℓ} {A : Set ℓ} (finA : IsFinite A) where
  open IsFinite finA

  deduplicate : MinimalEnumeration A
  deduplicate = record
    { isFinite = finite (List.deduplicate _≟_ elements) (Enumerates.deduplicate⁺ (≡.decSetoid _≟_) membership)
    ; unique = deduplicate-! _≟_ elements
    }

  cardinality : ℕ
  cardinality = MinimalEnumeration.size deduplicate

open IsFinite

via-surjection : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → IsFinite B → (B ↠ A) → IsFinite A
via-surjection finB h .elements = List.map (Surjection.to h) (finB .elements)
via-surjection finB h .membership x =
  subst (_∈ _)
    (proj₂ (Surjection.surjective h x) refl)
    (∈-map⁺ _ (finB .membership (Surjection.to⁻ h x)))

via-left-inverse : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → IsFinite B → (B ↩ A) → IsFinite A
via-left-inverse finB h =
  via-surjection finB
    (mk↠
      {to = LeftInverse.to h}
      (inverseˡ⇒surjective _≡_ (LeftInverse.inverseˡ h)))

via-irrelevant-dec : ∀ {ℓ} {A : Set ℓ} → Nullary.Irrelevant A → Dec A → IsFinite A
via-irrelevant-dec p (yes a) = finite [ a ] (here ∘ flip p a)
via-irrelevant-dec p (no ¬a) = finite [] (⊥-elim ∘ ¬a)
