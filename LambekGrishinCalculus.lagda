%include agda.fmt

\ifverbose
\begin{code}
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)
\end{code}
\fi

\section{Lambek-Grishin Calculus (fLG)}
%{
%include LambekGrishinCalculus.fmt

\ifverbose
\begin{code}
module LambekGrishinCalculus (U : Set) (R : U) (⟦_⟧ᵁ : U → Set) where
\end{code}
\fi

\ifverbose
\begin{code}
  infix  30 _⊗_ _⊕_
  infixr 20 _⇒_ _⇛_
  infixl 20 _⇐_ _⇚_
  infix  5  _⊢_ [_]⊢_ _⊢[_]
\end{code}
\fi

\begin{code}
  data Polarity : Set where
    + : Polarity
    - : Polarity
\end{code}

\begin{code}
  _≟ᴾ_ : (p q : Polarity) → Dec (p ≡ q)
  + ≟ᴾ + = yes refl
  + ≟ᴾ - = no (λ ())
  - ≟ᴾ + = no (λ ())
  - ≟ᴾ - = yes refl
\end{code}

\begin{code}
  data Type : Set where
    el   : (A : U) → (p : Polarity) → Type
    _⊗_  : Type → Type → Type
    _⇒_  : Type → Type → Type
    _⇐_  : Type → Type → Type
    _⊕_  : Type → Type → Type
    _⇚_  : Type → Type → Type
    _⇛_  : Type → Type → Type
\end{code}

\begin{code}
  mutual
    data Struct+ : Set where
      ·_·  : Type → Struct+
      _⊗_  : Struct+ → Struct+ → Struct+
      _⇚_  : Struct+ → Struct- → Struct+
      _⇛_  : Struct- → Struct+ → Struct+

    data Struct- : Set where
      ·_·  : Type → Struct-
      _⊕_  : Struct- → Struct- → Struct-
      _⇒_  : Struct+ → Struct- → Struct-
      _⇐_  : Struct- → Struct+ → Struct-
\end{code}

\begin{code}
  mutual
    data _⊢_ : Struct+ → Struct- → Set where
      μ*     : ∀ {X A} → X ⊢[ A ] → X ⊢ · A ·
      μ̃*     : ∀ {X A} → [ A ]⊢ X → · A · ⊢ X
      ⊗L     : ∀ {X A B} → · A · ⊗ · B · ⊢ X → · A ⊗ B · ⊢ X
      ⇚L    : ∀ {X A B} → · A · ⇚ · B · ⊢ X → · A ⇚ B · ⊢ X
      ⇛L    : ∀ {X A B} → · B · ⇛ · A · ⊢ X → · B ⇛ A · ⊢ X
      ⊕R     : ∀ {X A B} → X ⊢ · A · ⊕ · B · → X ⊢ · A ⊕ B ·
      ⇒R    : ∀ {X A B} → X ⊢ · A · ⇒ · B · → X ⊢ · A ⇒ B ·
      ⇐R    : ∀ {X A B} → X ⊢ · B · ⇐ · A · → X ⊢ · B ⇐ A ·
      res₁   : ∀ {X Y Z} → Y ⊢ X ⇒ Z → X ⊗ Y ⊢ Z
      res₂   : ∀ {X Y Z} → X ⊗ Y ⊢ Z → Y ⊢ X ⇒ Z
      res₃   : ∀ {X Y Z} → X ⊢ Z ⇐ Y → X ⊗ Y ⊢ Z
      res₄   : ∀ {X Y Z} → X ⊗ Y ⊢ Z → X ⊢ Z ⇐ Y
      dres₁  : ∀ {X Y Z} → Z ⇚ X ⊢ Y → Z ⊢ Y ⊕ X
      dres₂  : ∀ {X Y Z} → Z ⊢ Y ⊕ X → Z ⇚ X ⊢ Y
      dres₃  : ∀ {X Y Z} → Y ⇛ Z ⊢ X → Z ⊢ Y ⊕ X
      dres₄  : ∀ {X Y Z} → Z ⊢ Y ⊕ X → Y ⇛ Z ⊢ X
      dist₁  : ∀ {X Y Z W} → X ⊗ Y ⊢ Z ⊕ W → X ⇚ W ⊢ Z ⇐ Y
      dist₂  : ∀ {X Y Z W} → X ⊗ Y ⊢ Z ⊕ W → Y ⇚ W ⊢ X ⇒ Z
      dist₃  : ∀ {X Y Z W} → X ⊗ Y ⊢ Z ⊕ W → Z ⇛ X ⊢ W ⇐ Y
      dist₄  : ∀ {X Y Z W} → X ⊗ Y ⊢ Z ⊕ W → Z ⇛ Y ⊢ X ⇒ W

    data _⊢[_] : Struct+ → Type → Set where
      var    : ∀ {A} → · A · ⊢[ A ]
      μ      : ∀ {X A} → X ⊢ · A · → X ⊢[ A ]
      ⊗R     : ∀ {X Y A B} → X ⊢[ A ] → Y ⊢[ B ] → X ⊗ Y ⊢[ A ⊗ B ]
      ⇚R    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → X ⇚ Y ⊢[ A ⇚ B ]
      ⇛R    : ∀ {X Y A B} → [ B ]⊢ Y → X ⊢[ A ] → Y ⇛ X ⊢[ B ⇛ A ]

    data [_]⊢_ : Type → Struct- → Set where
      covar  : ∀ {A} → [ A ]⊢ · A ·
      μ̃      : ∀ {X A} → · A · ⊢ X → [ A ]⊢ X
      ⊕L     : ∀ {X Y A B} → [ B ]⊢ Y → [ A ]⊢ X → [ B ⊕ A ]⊢ X ⊕ Y
      ⇒L    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → [ A ⇒ B ]⊢ X ⇒ Y
      ⇐L    : ∀ {X Y A B} → [ B ]⊢ Y → X ⊢[ A ] → [ B ⇐ A ]⊢ Y ⇐ X
\end{code}

\begin{code}
  raise : ∀ {A B} → · A · ⊢ · (B ⇐ A) ⇒ B ·
  raise = ⇒R (res₂ (res₃ (μ̃* (⇐L covar var))))

  lower : ∀ {A B} → · B ⇚ (A ⇛ B) · ⊢ · A ·
  lower = ⇚L (dres₂ (dres₃ (μ* (⇛R covar var))))
\end{code}

\ifverbose
\begin{code}
  open import LinearLogic U R ⟦_⟧ᵁ as LP hiding (reify) renaming (Type to TypeLP; _⊢_ to _⊢LP_; ⟦_⟧ to ⟦_⟧ᵀ)
\end{code}
\fi

\begin{code}
  pol : Type → Polarity
  pol (el A p)  = p
  pol (A ⊗ B)   = +
  pol (A ⇚ B)  = +
  pol (A ⇛ B)  = +
  pol (A ⊕ B)   = -
  pol (A ⇒ B)  = -
  pol (A ⇐ B)  = -
\end{code}

\begin{code}
  cps : Polarity → Type → TypeLP
  cps + (el A +)  = el A
  cps + (el A -)  = ¬ (¬ el A)
  cps + (A ⊗ B)   = cps + A ⊗ cps + B
  cps + (B ⇚ A)  = cps + B ⊗ cps - A
  cps + (A ⇛ B)  = cps - A ⊗ cps + B
  cps + (A ⊕ B)   = ¬ (cps - A ⊗ cps - B)
  cps + (A ⇒ B)  = ¬ (cps + A ⊗ cps - B)
  cps + (B ⇐ A)  = ¬ (cps - B ⊗ cps + A)
  cps - (el A +)  = ¬ el A
  cps - (el A -)  = ¬ el A
  cps - (A ⊗ B)   = ¬ (cps + A ⊗ cps + B)
  cps - (B ⇚ A)  = ¬ (cps + B ⊗ cps - A)
  cps - (A ⇛ B)  = ¬ (cps - A ⊗ cps + B)
  cps - (A ⊕ B)   = cps - A ⊗ cps - B
  cps - (A ⇒ B)  = cps + A ⊗ cps - B
  cps - (B ⇐ A)  = cps - B ⊗ cps + A
\end{code}

Co-variables only occur in negative contexts, and variables
only occur in positive contexts. So again, if the context and
the actual polarizations clash, we add a negation.

\begin{code}
  mutual
    str+ : (s : Struct+) → List TypeLP
    str+ (· A ·)   = cps + A , ∅
    str+ (A ⊗ B)   = str+ A ++ str+ B
    str+ (B ⇚ A)  = str+ B ++ str- A
    str+ (A ⇛ B)  = str- A ++ str+ B

    str- : (s : Struct-) → List TypeLP
    str- (· A ·)   = cps - A , ∅
    str- (A ⊕ B)   = str- A ++ str- B
    str- (A ⇒ B)  = str+ A ++ str- B
    str- (B ⇐ A)  = str- B ++ str+ A
\end{code}

\ifverbose
\begin{code}
  record CPS (A B : Set) : Set where
    field
      ⟦_⟧ : A → B
  open CPS {{...}} public using (⟦_⟧)

  Type+CPS : CPS Type TypeLP
  Type+CPS = record { ⟦_⟧ = λ A → cps + A }

  Struct+CPS : CPS Struct+ (List TypeLP)
  Struct+CPS = record { ⟦_⟧ = str+ }

  Struct-CPS : CPS Struct- (List TypeLP)
  Struct-CPS = record { ⟦_⟧ = str- }
\end{code}
\fi

\begin{code}
  lemma-cps : ∀ A → cps + A ≡ cps - A ⊸ ⊥ ⊎ cps - A ≡ cps + A ⊸ ⊥
  lemma-cps (el A +)  = inj₂ refl
  lemma-cps (el A -)  = inj₁ refl
  lemma-cps (A ⊗ B)   = inj₂ refl
  lemma-cps (B ⇚ A)  = inj₂ refl
  lemma-cps (A ⇛ B)  = inj₂ refl
  lemma-cps (A ⊕ B)   = inj₁ refl
  lemma-cps (A ⇒ B)  = inj₁ refl
  lemma-cps (B ⇐ A)  = inj₁ refl
\end{code}

\begin{code}
  lemma-var : ∀ A → cps + A , ∅ ⊢LP cps - A ⊸ ⊥
  lemma-var A with lemma-cps A
  ... | inj₁ p rewrite p = var
  ... | inj₂ p rewrite p = abs (app var var)
\end{code}

\begin{code}
  lemma-covar : ∀ A → cps - A , ∅ ⊢LP cps + A ⊸ ⊥
  lemma-covar A with lemma-cps A
  ... | inj₁ p rewrite p = abs (app var var)
  ... | inj₂ p rewrite p = var
\end{code}

\begin{code}
  lemma-μ : ∀ X A → X ,′ cps - A ⊢LP ⊥ → X ⊢LP cps - A ⊸ ⊥
  lemma-μ X A t with lemma-cps A
  ... | inj₁ p rewrite p = abs (to-back t)
  ... | inj₂ p rewrite p = abs (to-back t)
\end{code}

\begin{code}
  lemma-μ̃ : ∀ X A → cps + A , X ⊢LP ⊥ → X ⊢LP cps + A ⊸ ⊥
  lemma-μ̃ X A t with lemma-cps A
  ... | inj₁ p rewrite p = abs t
  ... | inj₂ p rewrite p = abs t
\end{code}

\begin{code}
  lemma-μ* : ∀ X A → X ⊢LP cps - A ⊸ ⊥ → X ,′ cps - A ⊢LP ⊥
  lemma-μ* X A t = app t var
\end{code}

\begin{code}
  lemma-μ̃* : ∀ X A → X ⊢LP cps + A ⊸ ⊥ → cps + A , X ⊢LP ⊥
  lemma-μ̃* X A t = to-back (app t var)
\end{code}

\begin{code}
{-
  mutual
    reify  : ∀ {X Y} → X ⊢ Y → ⟦ X ⟧ ++ ⟦ Y ⟧ ⊢LP ⊥
    reify (μ* {X} {A} t) = {!!} -- lemma-μ* ⟦ X ⟧ A (reifyʳ t)
    reify (μ̃* {X} {A} t) = {!!} -- lemma-μ̃* ⟦ X ⟧ A (reifyˡ t)
    reify (⊗L {X} {A} {B} t) = pair-left (reify t)
    reify (⇚L {X} {A} {B} t) = pair-left (reify t)
    reify (⇛L {X} {A} {B} t) = pair-left (reify t)
    reify (⊕R {X} {A} {B} t) = pair-leftʳ′ {⟦ X ⟧} {cps - A} {cps - B} (reify t)
    reify (⇒R {X} {A} {B} t) = pair-leftʳ′ {⟦ X ⟧} {cps + A} {cps - B} (reify t)
    reify (⇐R {X} {A} {B} t) = pair-leftʳ′ {⟦ X ⟧} {cps - B} {cps + A} (reify t)
    reify (res₁ {X} {Y} {Z} t)  rewrite sym (++-assoc ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧) = Y[XZ]↝X[YZ] ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify t)
    reify (res₂ {X} {Y} {Z} t)  rewrite      ++-assoc ⟦ Y ⟧ ⟦ X ⟧ ⟦ Z ⟧  = [YX]Z↝[XY]Z ⟦ Y ⟧ ⟦ X ⟧ ⟦ Z ⟧ (reify t)
    reify (res₃ {X} {Y} {Z} t)  rewrite sym (++-assoc ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧) = X[ZY]↝X[YZ] ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify t)
    reify (res₄ {X} {Y} {Z} t)  rewrite      ++-assoc ⟦ X ⟧ ⟦ Z ⟧ ⟦ Y ⟧  = [XZ]Y↝[XY]Z ⟦ X ⟧ ⟦ Z ⟧ ⟦ Y ⟧ (reify t)
    reify (dres₁ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧  = [XZ]Y↝[XY]Z ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧ (reify t)
    reify (dres₂ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ Z ⟧ ⟦ X ⟧ ⟦ Y ⟧) = X[ZY]↝X[YZ] ⟦ Z ⟧ ⟦ X ⟧ ⟦ Y ⟧ (reify t)
    reify (dres₃ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧  = [YX]Z↝[XY]Z ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧ (reify t)
    reify (dres₄ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ Y ⟧ ⟦ Z ⟧ ⟦ X ⟧) = Y[XZ]↝X[YZ] ⟦ Y ⟧ ⟦ Z ⟧ ⟦ X ⟧ (reify t)
    reify (dist₁ {X} {Y} {Z} {W} t) = {!(reify t)!} -- XYZW↝XWZY
    reify (dist₂ {X} {Y} {Z} {W} t) = {!(reify t)!} -- XYZW↝YWXZ
    reify (dist₃ {X} {Y} {Z} {W} t) = {!(reify t)!} -- XYZW↝ZXWY
    reify (dist₄ {X} {Y} {Z} {W} t) = {!(reify t)!} -- XYZW↝ZYXW

    reifyʳ : ∀ {X A} → X ⊢[ A ] → ⟦ X ⟧ ⊢LP ⟦ A ⟧
    reifyʳ var = var
    reifyʳ (μ {X} {A} t) = {!!}
    reifyʳ (⊗R {X} {Y} {A} {B} s t) = pair (reifyʳ s) (reifyʳ t)
    reifyʳ (⇚R {X} {Y} {A} {B} s t) = {!pair (reifyʳ s) (reifyˡ t)!}
    reifyʳ (⇛R {X} {Y} {A} {B} s t) = {!!}

    reifyˡ : ∀ {A Y} → [ A ]⊢ Y → ⟦ Y ⟧ ⊢LP ⟦ A ⟧ ⊸ ⊥
    reifyˡ (covar {A}) = lemma-covar A
    reifyˡ (μ̃ {X} {A} t) = lemma-μ̃ ⟦ X ⟧ A (reify t)
    reifyˡ (⊕L {X} {Y} {A} {B} s t) = {!!}
    reifyˡ (⇒L {X} {Y} {A} {B} s t) = {!!}
    reifyˡ (⇐L {X} {Y} {A} {B} s t) = {!!}
-}
\end{code}
%}
