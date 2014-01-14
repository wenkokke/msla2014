open import Function using (_∘_)
open import Data.Unit using (tt) renaming (⊤ to 1')
open import Data.Empty using () renaming (⊥ to 0'; ⊥-elim to exfalso)
open import Data.Product using (∃; _×_; _,_; map; proj₁; proj₂)
open import Data.Sum using ([_,_]) renaming (_⊎_ to _+_; inj₁ to inl; inj₂ to inr)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; trans; cong)

module Connectives (U : Set) where

  infixr 20 _⇒_
  infixr 30 _∧_ _∨_
  infixr 40 ¬_

  data Type : Set where
    el   : (A : U) → Type
    _⇒_ : Type → Type → Type
    _∧_  : Type → Type → Type
    _∨_  : Type → Type → Type
    ⊤    : Type
    ⊥    : Type

  ¬_ : Type → Type
  ¬_ A = A ⇒ ⊥



  -- defines some injectivity principles for the connectives along
  -- the propositional equality relation

  el-inj : ∀ {A B} → el A ≡ el B → A ≡ B
  el-inj refl = refl

  arr-injl : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → A ≡ C
  arr-injl refl = refl

  arr-injr : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → B ≡ D
  arr-injr refl = refl

  conj-injl : ∀ {A B C D} → A ∧ B ≡ C ∧ D → A ≡ C
  conj-injl refl = refl

  conj-injr : ∀ {A B C D} → A ∧ B ≡ C ∧ D → B ≡ D
  conj-injr refl = refl

  disj-injl : ∀ {A B C D} → A ∨ B ≡ C ∨ D → A ≡ C
  disj-injl refl = refl

  disj-injr : ∀ {A B C D} → A ∨ B ≡ C ∨ D → B ≡ D
  disj-injr refl = refl



  -- defines a standard interpretation of the logical connectives in
  -- agda's type theory (needs an interpretation of the universe)

  module Reify (⟦_⟧ᵁ : U → Set) where

    ⟦_⟧ : Type → Set
    ⟦ el A ⟧ = ⟦ A ⟧ᵁ
    ⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
    ⟦ A ∧ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
    ⟦ A ∨ B ⟧ = ⟦ A ⟧ + ⟦ B ⟧
    ⟦ ⊤ ⟧ = 1'
    ⟦ ⊥ ⟧ = 0'



  -- defines a decidable equality for the logical connectives (needs
  -- a decidable equality for the universe)

  module DecidableEquality (_≟ᵁ_ : (x y : U) → Dec (x ≡ y)) where

    _≟ᵀ_ : (x y : Type) → Dec (x ≡ y)
    el A ≟ᵀ el  B with A ≟ᵁ B
    el A ≟ᵀ el .A | yes refl = yes refl
    el A ≟ᵀ el  B | no  A≢B  = no (A≢B ∘ el-inj)
    el _ ≟ᵀ (_ ⇒ _) = no (λ ())
    el _ ≟ᵀ _ ∧ _ = no (λ ())
    el _ ≟ᵀ _ ∨ _ = no (λ ())
    el _ ≟ᵀ ⊤ = no (λ ())
    el _ ≟ᵀ ⊥ = no (λ ())
    (_ ⇒ _) ≟ᵀ el _ = no (λ ())
    (x ⇒ y) ≟ᵀ (x′ ⇒ y′) with x ≟ᵀ x′
    (x ⇒ y) ≟ᵀ (x′ ⇒ y′) | no x≢x′ = no (x≢x′ ∘ arr-injl)
    (x ⇒ y) ≟ᵀ (.x ⇒ y′) | yes refl with y ≟ᵀ y′
    (x ⇒ y) ≟ᵀ (.x ⇒ y′) | yes refl | no y≢y′ = no (y≢y′ ∘ arr-injr)
    (x ⇒ y) ≟ᵀ (.x ⇒ .y) | yes refl | yes refl = yes refl
    (_ ⇒ _) ≟ᵀ _ ∧ _ = no (λ ())
    (_ ⇒ _) ≟ᵀ _ ∨ _ = no (λ ())
    (_ ⇒ _) ≟ᵀ ⊤ = no (λ ())
    (_ ⇒ _) ≟ᵀ ⊥ = no (λ ())
    _ ∧ _ ≟ᵀ el _ = no (λ ())
    _ ∧ _ ≟ᵀ (_ ⇒ _) = no (λ ())
    x ∧ y ≟ᵀ x′ ∧ y′ with x ≟ᵀ x′
    (x ∧ y) ≟ᵀ (x′ ∧ y′) | no x≢x′ = no (x≢x′ ∘ conj-injl)
    (x ∧ y) ≟ᵀ (.x ∧ y′) | yes refl with y ≟ᵀ y′
    (x ∧ y) ≟ᵀ (.x ∧ y′) | yes refl | no y≢y′ = no (y≢y′ ∘ conj-injr)
    (x ∧ y) ≟ᵀ (.x ∧ .y) | yes refl | yes refl = yes refl
    _ ∧ _ ≟ᵀ _ ∨ _ = no (λ ())
    _ ∧ _ ≟ᵀ ⊤ = no (λ ())
    _ ∧ _ ≟ᵀ ⊥ = no (λ ())
    _ ∨ _ ≟ᵀ el _ = no (λ ())
    _ ∨ _ ≟ᵀ (_ ⇒ _) = no (λ ())
    _ ∨ _ ≟ᵀ _ ∧ _ = no (λ ())
    x ∨ y ≟ᵀ x′ ∨ y′ with x ≟ᵀ x′
    (x ∨ y) ≟ᵀ (x′ ∨ y′) | no x≢x′ = no (x≢x′ ∘ disj-injl)
    (x ∨ y) ≟ᵀ (.x ∨ y′) | yes refl with y ≟ᵀ y′
    (x ∨ y) ≟ᵀ (.x ∨ y′) | yes refl | no y≢y′ = no (y≢y′ ∘ disj-injr)
    (x ∨ y) ≟ᵀ (.x ∨ .y) | yes refl | yes refl = yes refl
    _ ∨ _ ≟ᵀ ⊤ = no (λ ())
    _ ∨ _ ≟ᵀ ⊥ = no (λ ())
    ⊤ ≟ᵀ el _ = no (λ ())
    ⊤ ≟ᵀ (_ ⇒ _) = no (λ ())
    ⊤ ≟ᵀ _ ∧ _ = no (λ ())
    ⊤ ≟ᵀ _ ∨ _ = no (λ ())
    ⊤ ≟ᵀ ⊤ = yes refl
    ⊤ ≟ᵀ ⊥ = no (λ ())
    ⊥ ≟ᵀ el _ = no (λ ())
    ⊥ ≟ᵀ (_ ⇒ _) = no (λ ())
    ⊥ ≟ᵀ _ ∧ _ = no (λ ())
    ⊥ ≟ᵀ _ ∨ _ = no (λ ())
    ⊥ ≟ᵀ ⊤ = no (λ ())
    ⊥ ≟ᵀ ⊥ = yes refl
