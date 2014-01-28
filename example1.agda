open import Data.Fin using (Fin; suc; zero)
open import Data.Vec as Vec using (Vec) renaming (_∷_ to _,_; [] to ∅)

module example1 where

infix  4  _⊢_

data Type : Set where
  E     : Type
  T     : Type
  _×_   : Type → Type → Type
  _⇒_  : Type → Type → Type

data _⊢_ : ∀ {k} (Γ : Vec Type k) (A : Type) → Set where
  var   : ∀ {k} {Γ : Vec Type k} (i : Fin k) → Γ ⊢ Vec.lookup i Γ
  abs   : ∀ {A B} {k} {Γ : Vec Type k} → A , Γ ⊢ B → Γ ⊢ A ⇒ B
  app   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  pair  : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A × B
  fst   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A × B → Γ ⊢ A
  snd   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A × B → Γ ⊢ B

swap : ∀ {A B} {n} {Γ : Vec Type n} → A × B , Γ ⊢ B × A
swap {A} {B} {n} {Γ} = {!!}
