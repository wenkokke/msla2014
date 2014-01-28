%<*agdafmt>
%include agda.fmt
%</agdafmt>

\begin{code}
module code where
\end{code}

\begin{code}
module Explicit where
\end{code}

%<*id1>
\begin{code}
  id : (A : Set) → A → A
  id A x = x
\end{code}
%</id1>

\begin{code}
module Implicit where
\end{code}

%<*id2>
\begin{code}
  id : {A : Set} → A → A
  id x = x
\end{code}
%</id2>

%<*sigma>
\begin{code}
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B
\end{code}
%</sigma>

%<*pair>
\begin{code}
_×_ : (A B : Set) → Set
A × B = Σ A (λ _ → B)
\end{code}
%</pair>

%<*nat>
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}
%</nat>

%<*fin>
\begin{code}
data Fin : ℕ → Set where
  zero  : ∀ {n} → Fin (suc n)
  suc   : ∀ {n} → Fin n → Fin (suc n)
\end{code}
%</fin>

\begin{code}
module List where
\end{code}

%<*list>
\begin{code}
  data List (A : Set) : Set where
    nil   : List A
    cons  : A → List A → List A
\end{code}
%</list>

%<*list-head>
\begin{code}
  head : ∀ {A} → List A → A
  head nil          = ?
  head (cons x xs)  = x
\end{code}
%</list-head>

\begin{code}
module Vec where
\end{code}

%<*vec>
\begin{code}
  data Vec (A : Set) : ℕ → Set where
    nil   : Vec A zero
    cons  : ∀ {n} → A → Vec A n → Vec A (suc n)
\end{code}
%</vec>

%<*vec-head>
\begin{code}
  head : ∀ {A} {n} → Vec A (suc n) → A
  head (cons x xs) = x
\end{code}
%</vec-head>
