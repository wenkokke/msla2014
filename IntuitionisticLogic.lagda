%include agda.fmt
%format zero = "0"

\ifverbose
\begin{code}
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec as Vec using (Vec) renaming (_∷_ to _,_; [] to ∅)
\end{code}
\fi

\section{Intuitionistic Logic (IL)}
%{
%include IntuitionisticLogic.fmt

\ifverbose
\begin{code}
module IntuitionisticLogic (U : Set) where
\end{code}
\fi

\ifverbose
\begin{code}
infix  30 _⊗_
infixr 20 _⇒_
infix  4  _⊢_
\end{code}
\fi

\begin{code}
data Type : Set where
  el    : (A : U) → Type
  _⊗_   : Type → Type → Type
  _⇒_  : Type → Type → Type
\end{code}

\begin{code}
data _⊢_ : ∀ {k} (Γ : Vec Type k) (A : Type) → Set where
  var   : ∀ {k} {Γ : Vec Type k} (i : Fin k) → Γ ⊢ Vec.lookup i Γ
  abs   : ∀ {A B} {k} {Γ : Vec Type k} → A , Γ ⊢ B → Γ ⊢ A ⇒ B
  app   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  pair  : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⊗ B
  fst   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B → Γ ⊢ A
  snd   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B → Γ ⊢ B
\end{code}

\begin{code}
swap : ∀ {A B} {k} {Γ : Vec Type k} → A ⊗ B , Γ ⊢ B ⊗ A
swap = pair (snd (var zero)) (fst (var zero))
\end{code}
%}
