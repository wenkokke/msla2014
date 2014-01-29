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
\todo{mention de Bruijn notation}
\todo{mention the alternative syntax for Lists and Vectors (using $∅$ and $\_,\_$)}

\begin{figure}[h]
  \centering
  \begin{tabular}{l l}
     Named & de Bruijn
  \\ \hline
  \\ $\lambda x \to x$
   & $\textcolor{red}{\lambda}\ \textcolor{red}{0}$
  \\ $\lambda x \to \lambda y \to x$
   & $\textcolor{red}{\lambda}\ \textcolor{blue}{\lambda}\ \textcolor{red}{1}$
  \\ $\lambda x \to \lambda y \to \lambda z \to x \ z \ (y \ z)$
   & $\textcolor{red}{\lambda}\ \textcolor{blue}{\lambda}\ \textcolor{green}{\lambda}\
      \textcolor{red}{2}\ \textcolor{green}{0}\ (\textcolor{blue}{1}\ \textcolor{green}{0})$
  \end{tabular}
  \caption{Named notation versus de Bruijn notation \citep{mazzoli2013}.}
  \label{fig:namedvsdebruijn}
\end{figure}

\begin{figure}[h]
  \begin{mdframed}
    \begin{scprooftree}{0.8}
      \AXC{}
      \RightLabel{\scriptsize Axiom}
      \UIC{$\Gamma \fCenter (var \ i) : \Gamma_i$}
    \end{scprooftree}

    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma, A \fCenter e : B$}
        \RightLabel{\scriptsize $\to$-intro}
        \UIC{$\Gamma \fCenter (lam \ e) : A \to B$}
      \end{scprooftree}
    \end{minipage}%
    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma \fCenter e_1 : A \to B$}
        \AXC{$\Gamma \fCenter e_2 : A$}
        \RightLabel{\scriptsize $\to$-elim}
        \BIC{$\Gamma \fCenter (app \ e_1 \ e_2) : B$}
      \end{scprooftree}
    \end{minipage}

    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma \fCenter e_1 : A$}
        \AXC{$\Gamma \fCenter e_2 : B$}
        \RightLabel{\scriptsize $\times$-intro}
        \BIC{$\Gamma \fCenter (pair \ e_1 \ e_2) : A \times B$}
      \end{scprooftree}
    \end{minipage}%
    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma \fCenter e_1 : A \times B$}
        \AXC{$\Gamma \fCenter e_2 : A \to B \to C$}
        \RightLabel{\scriptsize $\times$-elim}
        \BIC{$\Gamma \fCenter (case \ e_1 \ e_2) : C$}
      \end{scprooftree}
    \end{minipage}
  \end{mdframed}

  \caption{Inference rules for \textbf{IL} corresponding to the de Bruijn notation.}
  \label{fig:intuitionisticlogic}
\end{figure}

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
