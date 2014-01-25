%include agda.fmt

\begin{code}
module code where
\end{code}

\begin{code}
open import Data.Nat using (ℕ; suc; zero)
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

%<*fin>
\begin{code}
data Fin : ℕ → Set where
  zero  : ∀ {n} → Fin (suc n)
  suc   : ∀ {n} → Fin n → Fin (suc n)
\end{code}
%</fin>
