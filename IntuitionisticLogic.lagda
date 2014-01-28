%include agda.fmt
%format zero = "0"

\hidden{
\begin{code}
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec as Vec using (Vec) renaming (_∷_ to _,_; [] to ∅)
open import Data.List using (_∷_; [])
open import Data.List as List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong)
\end{code}
}

\section{Intuitionistic Logic (IL)}
%{
%include IntuitionisticLogic.fmt

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
    var   : ∀ {k} {Γ : Vec Type k} (i : Fin k) → Γ ⊢ Vec.lookup i Γ
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
    weak  : ∀ {Γ Δ A} → Δ ⊢ A → Γ ++ Δ ⊢ A
    cont  : ∀ {Γ A B} → A , A , Γ ⊢ B → A , Γ ⊢ B
    exch  : ∀ {Σ Γ Δ Π A} →  (Σ ++ Δ) ++ (Γ ++ Π) ⊢ A
          →  (Σ ++ Γ) ++ (Δ ++ Π) ⊢ A
\end{code}
%</il-explicit>

\begin{code}
  exch₀ : ∀ {Γ A B C} → B , A , Γ ⊢ C → A , B , Γ ⊢ C
  exch₀ {Γ} {A} {B} = exch {∅} {A , ∅} {B , ∅} {Γ}
\end{code}

\begin{code}
  xs++[]=xs : ∀ {a} {A : Set a} (xs : List A) → xs ++ [] ≡ xs
  xs++[]=xs [] = refl
  xs++[]=xs (x ∷ xs) = cong (λ xs → x ∷ xs) (xs++[]=xs xs)
\end{code}
%}
