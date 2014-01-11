\section{Lambek-Grishin Calculus}
%{
%include LambekGrishin.fmt

\subsection{Lambek Calculus}

\ifverbose
\begin{code}
module LambekCalculus where
\end{code}
\fi

\ifverbose
\begin{code}
  infix  5 _⊢_
  infixr 6 _~>_
  infixl 6 _<~_
  infix  7 _*_
\end{code}
\fi

\begin{code}
  data Type : Set where
    N      : Type
    NP     : Type
    S      : Type
    _~>_   : Type → Type → Type
    _<~_   : Type → Type → Type
    _*_    : Type → Type → Type

  data _⊢_ : {k : ℕ} → (Γ : Context k) → (X : Type) → Set where

    axiom  :  ∀ {A} → A ∷ [] ⊢ A



\end{code}

\subsection{Lambek-Grishin Calculus}

\ifverbose
\begin{code}
module LG where
\end{code}
\fi

\ifverbose
\begin{code}
  infix  5 _⊢_
  infixr 6 _~>_ _=>_
  infixl 6 _<~_ _<=_
  infix  7 _*_ _+_
\end{code}
\fi

\begin{code}
  data Type : Set where
    N      : Type
    NP     : Type
    S      : Type
    _~>_   : Type → Type → Type
    _<~_   : Type → Type → Type
    _*_    : Type → Type → Type
    _=>_   : Type → Type → Type
    _<=_   : Type → Type → Type
    _+_    : Type → Type → Type

  data _⊢_ : Type → Type → Set where

    axiom     :  ∀ {A} → A ⊢ A

    cut       :  ∀ {A B C} → A ⊢ B → B ⊢ C → A ⊢ C

    res₁      :  ∀ {A B C} →     A ⊢ C <~ B → A * B ⊢ C
    res₂      :  ∀ {A B C} → A * B ⊢ C      →     A ⊢ C <~ B
    res₃      :  ∀ {A B C} → A * B ⊢ C      →     B ⊢ A ~> C
    res₄      :  ∀ {A B C} →     B ⊢ A ~> C → A * B ⊢ C

    cores₁    :  ∀ {A B C} → C <= B ⊢ A      →      C ⊢ A + B
    cores₂    :  ∀ {A B C} →      C ⊢ A + B  → C <= B ⊢ A
    cores₃    :  ∀ {A B C} →      C ⊢ A + B  → A => C ⊢ B
    cores₄    :  ∀ {A B C} → A => C ⊢ B      →      C ⊢ A + B

    grish₁    :  ∀ {A B C D} → A => (B * C) ⊢ D → (A => B) * C ⊢ D
    grish₂    :  ∀ {A B C D} → B => (A * C) ⊢ D → A * (B => C) ⊢ D
    grish₃    :  ∀ {A B C D} → (A * B) <= C ⊢ D → A * (B <= C) ⊢ D
    grish₄    :  ∀ {A B C D} → (A * C) <= B ⊢ D → (A <= B) * C ⊢ D

    cogrish₁  :  ∀ {A B C D} → D ⊢ (C + B) <~ A → D ⊢ C + (B <~ A)
    cogrish₂  :  ∀ {A B C D} → D ⊢ (B + C) <~ A → D ⊢ (B <~ A) + C
    cogrish₃  :  ∀ {A B C D} → D ⊢ A ~> (B + C) → D ⊢ (A ~> B) + C
    cogrish₄  :  ∀ {A B C D} → D ⊢ A ~> (C + B) → D ⊢ C + (A ~> B)

  res₅ : ∀ {A B C} → A ⊢ C <~ B → B ⊢ A ~> C
  res₅ = res₃ ∘ res₁
  res₆ : ∀ {A B C} → B ⊢ A ~> C → A ⊢ C <~ B
  res₆ = res₂ ∘ res₄

  cores₅ : ∀ {A B C} → C <= B ⊢ A → A => C ⊢ B
  cores₅ = cores₃ ∘ cores₁
  cores₆ : ∀ {A B C} → A => C ⊢ B → C <= B ⊢ A
  cores₆ = cores₂ ∘ cores₄

  mon₁ : ∀ {A B C D} → A ⊢ B → C ⊢ D → A * C ⊢ B * D
  mon₁ f g = res₁ (cut f (res₆ (cut g (res₃ axiom))))
  mon₂ : ∀ {A B C D} → A ⊢ B → C ⊢ D → A <~ D ⊢ B <~ C
  mon₂ f g = res₂ (cut (res₄ (cut g (res₅ axiom))) f)
  mon₃ : ∀ {A B C D} → A ⊢ B → C ⊢ D → D ~> A ⊢ C ~> B
  mon₃ f g = res₃ (cut (res₁ (cut g (res₆ axiom))) f)

  comon₁ : ∀ {A B C D} → A ⊢ B → C ⊢ D → A + C ⊢ B + D
  comon₁ f g = cores₁ (cut (cores₆ (cut (cores₃ axiom) g)) f)
  comon₂ : ∀ {A B C D} → A ⊢ B → C ⊢ D → A <= D ⊢ B <= C
  comon₂ f g = cores₂ (cut f (cores₄ (cut (cores₅ axiom) g)))
  comon₃ : ∀ {A B C D} → A ⊢ B → C ⊢ D → D => A ⊢ C => B
  comon₃ f g = cores₃ (cut f (cores₁ (cut (cores₆ axiom) g)))

  distr₁ : ∀ {A B C D} → A * B ⊢ C + D → C => A ⊢ D <~ B
  distr₁ p = res₂ (grish₁ (cores₃ p))

  distr₂ : ∀ {A B C D} → A * B ⊢ C + D → B <= D ⊢ A ~> C
  distr₂ p = res₃ (grish₃ (cores₂ p))

  distr₃ : ∀ {A B C D} → A * B ⊢ C + D → A <= D ⊢ C <~ B
  distr₃ p = res₂ (grish₄ (cores₂ p))

  distr₄ : ∀ {A B C D} → A * B ⊢ C + D → C => B ⊢ A ~> D
  distr₄ p = res₃ (grish₂ (cores₃ p))
\end{code}

\subsection{Display Logic}

\ifverbose
\begin{code}
module sLG where
\end{code}
\fi

\ifverbose
\begin{code}
  open LG using (Type)
\end{code}
\fi

\begin{code}
  mutual
    data StructI : Set where
      ·_·    : Type → StructI
      _*_    : StructI → StructI → StructI
      _=>_   : StructO → StructI → StructI
      _<=_   : StructI → StructO → StructI

    data StructO : Set where
      ·_·    : Type → StructO
      _+_    : StructO → StructO → StructO
      _~>_   : StructI → StructO → StructO
      _<~_   : StructO → StructI → StructO
\end{code}
%}
