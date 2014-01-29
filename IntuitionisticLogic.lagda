%include paper.fmt
%include IntuitionisticLogic.fmt

\hidden{
\begin{code}
open import Function using (id)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec as Vec using (Vec) renaming (_∷_ to _,_; [] to ∅)
open import Data.List using (_∷_; [])
open import Data.List as List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.Product using (∃; _,_; map)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong)
\end{code}
}

\hidden{
\begin{code}
module IntuitionisticLogic (U : Set) where
\end{code}
}

\hidden{
\begin{code}
infix  30 _⊗_
infixr 20 _⇒_
\end{code}
}

\todo{mention module-level abstraction over atomic types}

%<*type>
\begin{code}
data Type : Set where
  el    : (A : U) → Type
  _⊗_   : Type → Type → Type
  _⇒_  : Type → Type → Type
\end{code}
%</type>

\hidden{
\begin{code}
module Implicit where
\end{code}
}

\hidden{
\begin{code}
  infix  4  _⊢_
\end{code}
}

%<*il-implicit>
\begin{code}
  data _⊢_ : ∀ {k} (Γ : Vec Type k) (A : Type) → Set where
    var   : ∀ {k} {Γ : Vec Type k} (x : Fin k) → Γ ⊢ Vec.lookup x Γ
    abs   : ∀ {A B} {k} {Γ : Vec Type k} → A , Γ ⊢ B → Γ ⊢ A ⇒ B
    app   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    pair  : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⊗ B
    fst   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B → Γ ⊢ A
    snd   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B → Γ ⊢ B
\end{code}
%</il-implicit>

\begin{code}
  swap : ∀ {A B} {k} {Γ : Vec Type k} → A ⊗ B , Γ ⊢ B ⊗ A
  swap = pair (snd (var zero)) (fst (var zero))
\end{code}

\begin{code}
  Vec-exch : ∀ {k} → ∀ i → Vec Type (suc k) → Vec Type (suc k)
  Vec-exch  zero    (A , B , Γ)  = B , (A , Γ)
  Vec-exch (suc i)  (A , Γ)      = A , (Vec-exch i Γ)
\end{code}

\begin{code}
  lemma-var : ∀ {k} {Γ : Vec Type (suc k)} → ∀ i x → ∃ λ y → Vec.lookup x Γ ≡ Vec.lookup y (Vec-exch i Γ)
  lemma-var {Γ = A , B , Γ} zero     zero           = suc zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc zero)     = zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc (suc x))  = suc (suc x) , refl
  lemma-var {Γ = A , Γ} (suc i)  zero           = zero , refl
  lemma-var {Γ = A , Γ} (suc i)  (suc x)        = map suc id (lemma-var {Γ = Γ} i x)
\end{code}

\begin{code}
  exch : ∀ {k} {Γ : Vec Type (suc k)} {A} → ∀ i → Γ ⊢ A → Vec-exch i Γ ⊢ A
  exch {Γ = Γ} i (var x) with lemma-var {Γ = Γ} i x
  exch {Γ = Γ} i (var x) | y , p rewrite p  = var y
  exch i (abs t)         = abs (exch (suc i) t)
  exch i (app s t)       = app (exch i s) (exch i t)
  exch i (pair s t)      = pair (exch i s) (exch i t)
  exch i (fst t)         = fst (exch i t)
  exch i (snd t)         = snd (exch i t)
\end{code}

\hidden{
\begin{code}
module Explicit where
\end{code}
}

\hidden{
\begin{code}
  infix  4  _⊢_
\end{code}
}

%<*il-explicit>
\begin{code}
  data _⊢_ : ∀ (Γ : List Type) (A : Type) → Set where
    var   : ∀ {A} → A , ∅ ⊢ A
    abs   : ∀ {Γ A B} → A , Γ ⊢ B → Γ ⊢ A ⇒ B
    app   : ∀ {Γ Δ A B} → Γ ⊢ A ⇒ B → Δ ⊢ A → Γ ++ Δ ⊢ B
    pair  : ∀ {Γ Δ A B} → Γ ⊢ A → Δ ⊢ B → Γ ++ Δ ⊢ A ⊗ B
    case  : ∀ {Γ Δ A B C} → Γ ⊢ A ⊗ B → A , B , Δ ⊢ C → Γ ++ Δ ⊢ C
    weak  : ∀ {Γ A B} → Γ ⊢ B → A , Γ ⊢ B
    cont  : ∀ {Γ A B} → A , A , Γ ⊢ B → A , Γ ⊢ B
    exch  : ∀ {Σ Γ Δ Π A} →  (Σ ++ Δ) ++ (Γ ++ Π) ⊢ A
          →  (Σ ++ Γ) ++ (Δ ++ Π) ⊢ A
\end{code}
%</il-explicit>

\hidden{
\begin{code}
  exch₀ : ∀ {Γ A B C} → B , A , Γ ⊢ C → A , B , Γ ⊢ C
  exch₀ {Γ} {A} {B} = exch {∅} {A , ∅} {B , ∅} {Γ}
\end{code}
}

\todo{explain meaning of exch₀}

\begin{code}
  swap : ∀ {A B} → A ⊗ B , ∅ ⊢ B ⊗ A
  swap = case var (exch₀ (pair var var))
\end{code}
%}
