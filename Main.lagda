\documentclass{article}

\usepackage{textgreek}
\usepackage{relsize}
\usepackage{stmaryrd}
\usepackage{natbib}

\usepackage{bussproofs}
\EnableBpAbbreviations
\def\fCenter{\ \vdash \ }
\def\limpl{\multimap}

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\DeclareUnicodeCharacter{7468}{$^A$}
\DeclareUnicodeCharacter{7486}{$^p$}
\DeclareUnicodeCharacter{7488}{$^T$}
\DeclareUnicodeCharacter{7489}{$^u$}

%include agda.fmt
%include main.fmt

% verbose:
%  set to true if *all* code should be rendered, including
%  import statements, module declarations, etc...
\newif\ifverbose
\verbosefalse

% complete:
%  set to true if the reader is familiar with Agda syntax
\newif\ifcomplete
\completetrue

\begin{document}

\ifverbose
\begin{code}
open import Function using (case_of_; flip)
open import Data.Nat using (ℕ; suc; zero) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Product using (∃; _×_; _,_; <_,_>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; False)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)
\end{code}
\fi

\ifverbose
\begin{code}
module Main where
\end{code}
\fi



\section{Linear Logic (LP)}

\ifverbose
\begin{code}
module LinearLogic (U : Set) (R : U) (⟦_⟧ᵁ : U → Set) where
\end{code}
\fi

\ifverbose
\begin{code}
  infixr 40 ¬_
  infix  30 _⊗_
  infixr 20 _⊸_
  infix  5  _⊢_
\end{code}
\fi

\begin{code}
  data Type : Set where
    el   : (A : U) → Type
    ⊥    : Type
    _⊗_  : Type → Type → Type
    _⊸_  : Type → Type → Type
\end{code}

\begin{code}
  ¬_ : Type → Type
  ¬ A = A ⊸ ⊥
\end{code}

\ifverbose
\begin{code}
  open import Context Type as Ctxt using (Ctxt; _,_; ∅; _++_)
  open Ctxt public using (Ctxt; _,_; ∅; _++_; _,′_)
\end{code}
\fi

\begin{code}
  data _⊢_ : ∀ {m} (Γ : Ctxt m) (A : Type) → Set where
    ax    : ∀ {A} → A , ∅ ⊢ A
    exch  : ∀ {A} {m} {Γ : Ctxt (suc m)} i → Ctxt.exch i Γ ⊢ A → Γ ⊢ A
    pair  : ∀ {A B} {m n} {Γ : Ctxt m} {Δ : Ctxt n} → Γ ⊢ A → Δ ⊢ B → Γ ++ Δ ⊢ A ⊗ B
    case  : ∀ {A B C} {m n} {Γ : Ctxt m} {Δ : Ctxt n} → Γ ⊢ A ⊗ B → A , B , Δ ⊢ C → Γ ++ Δ ⊢ C
    abs   : ∀ {A B} {m} {Γ : Ctxt m} → A , Γ ⊢ B → Γ ⊢ A ⊸ B
    app   : ∀ {A B} {m n} {Γ : Ctxt m} {Δ : Ctxt n} → Γ ⊢ A ⊸ B → Δ ⊢ A → Γ ++ Δ ⊢ B
\end{code}

\begin{code}
  exch₀ : ∀ {A B C} {m} {Γ : Ctxt m} → A , B , Γ ⊢ C → B , A , Γ ⊢ C
  exch₀ = exch zero
\end{code}

\begin{code}
  to-front     : ∀ {A B} {x} (X : Ctxt x)
               → A , X ⊢ B → X ,′ A ⊢ B
  to-front     s = {!!}
  to-back      : ∀ {A B} {x} (X : Ctxt x)
               → X ,′ A ⊢ B → A , X ⊢ B
  to-back      s = {!!}
  lemma-⊕L     : ∀ {A} {x y} (X : Ctxt x) (Y : Ctxt y)
               → Y ++ X ⊢ A → X ++ Y ⊢ A
  lemma-⊕L X Y t = {!!}
  lemma-⊗L     : ∀ {A B C} {x} (X : Ctxt x)
               → A , B , X ⊢ C → A ⊗ B , X ⊢ C
  lemma-⊗L     s = {!!}
  lemma-⇛L    : ∀ {A B C} {x} (X : Ctxt x)
               → B , A , X ⊢ C → B ⊗ A , X ⊢ C
  lemma-⇛L    s = {!!}
  lemma-⇚L    : ∀ {A B C} {x} (X : Ctxt x)
               → A , B , X ⊢ C → A ⊗ B , X ⊢ C
  lemma-⇚L    s = {!!}
  lemma-⊕R     : ∀ {A B C} {x} (X : Ctxt x)
               → X ++ (A , B , ∅) ⊢ C → X ++ (A ⊗ B , ∅) ⊢ C
  lemma-⊕R     s = {!!}
  lemma-⇒R    : ∀ {A B C} {x} (X : Ctxt x)
               → X ++ (A , B , ∅) ⊢ C → X ++ (A ⊗ B , ∅) ⊢ C
  lemma-⇒R    s = {!!}
  lemma-⇐R    : ∀ {A B C} {x} (X : Ctxt x)
               → X ++ (B , A , ∅) ⊢ C → X ++ (B ⊗ A , ∅) ⊢ C
  lemma-⇐R    s = {!!}
  lemma-res₁   : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → (Y ++ (X ++ Z)) ⊢ A → ((X ++ Y) ++ Z) ⊢ A
  lemma-res₁   s = {!!}
  lemma-res₂   : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → ((X ++ Y) ++ Z) ⊢ A → (Y ++ (X ++ Z)) ⊢ A
  lemma-res₂   s = {!!}
  lemma-res₃   : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → (X ++ (Z ++ Y)) ⊢ A → ((X ++ Y) ++ Z) ⊢ A
  lemma-res₃   s = {!!}
  lemma-res₄   : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → ((X ++ Y) ++ Z) ⊢ A → (X ++ (Z ++ Y)) ⊢ A
  lemma-res₄   s = {!!}
  lemma-dres₁  : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → ((Z ++ X) ++ Y) ⊢ A → (Z ++ (Y ++ X)) ⊢ A
  lemma-dres₁  s = {!!}
  lemma-dres₂  : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → (Z ++ (Y ++ X)) ⊢ A → ((Z ++ X) ++ Y) ⊢ A
  lemma-dres₂  s = {!!}
  lemma-dres₃  : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → ((Y ++ Z) ++ X) ⊢ A → (Z ++ (Y ++ X)) ⊢ A
  lemma-dres₃  s = {!!}
  lemma-dres₄  : ∀ {A} {x y z} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z)
               → (Z ++ (Y ++ X)) ⊢ A → ((Y ++ Z) ++ X) ⊢ A
  lemma-dres₄  s = {!!}
  lemma-dist₁  : ∀ {A} {x y z w} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z) (W : Ctxt w)
               → (X ++ Y) ++ (Z ++ W) ⊢ A → (X ++ W) ++ (Z ++ Y) ⊢ A
  lemma-dist₁  s = {!!}
  lemma-dist₂  : ∀ {A} {x y z w} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z) (W : Ctxt w)
               → (X ++ Y) ++ (Z ++ W) ⊢ A → (Y ++ W) ++ (X ++ Z) ⊢ A
  lemma-dist₂  s = {!!}
  lemma-dist₃  : ∀ {A} {x y z w} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z) (W : Ctxt w)
               → (X ++ Y) ++ (Z ++ W) ⊢ A → (Z ++ X) ++ (W ++ Y) ⊢ A
  lemma-dist₃  s = {!!}
  lemma-dist₄  : ∀ {A} {x y z w} (X : Ctxt x) (Y : Ctxt y) (Z : Ctxt z) (W : Ctxt w)
               → (X ++ Y) ++ (Z ++ W) ⊢ A → (Z ++ Y) ++ (X ++ W) ⊢ A
  lemma-dist₄  s = {!!}
\end{code}

\begin{code}
  raise : ∀ {A B} {m} {Γ : Ctxt m} → Γ ⊢ A → Γ ⊢ (A ⊸ B) ⊸ B
  raise t = abs (app ax t)
\end{code}

\begin{code}
  swap : ∀ {A B} {m} {Γ : Ctxt m} → A ⊗ B , ∅ ⊢ B ⊗ A
  swap {A} {B} = case ax (exch₀ (pair ax ax))
\end{code}

\begin{code}
  ⟦_⟧ : Type → Set
  ⟦ el A   ⟧ = ⟦ A ⟧ᵁ
  ⟦ ⊥      ⟧ = ⟦ R ⟧ᵁ
  ⟦ A ⊗ B  ⟧ = ⟦ A ⟧ × ⟦ B ⟧
  ⟦ A ⊸ B  ⟧ = ⟦ A ⟧ → ⟦ B ⟧
\end{code}

\ifverbose
\begin{code}
  open import Environment Type ⟦_⟧ as Env using (Env; _,_; ∅)
\end{code}
\fi

\begin{code}
  reify : ∀ {A} {n} {Γ : Ctxt n} → Env Γ → Γ ⊢ A → ⟦ A ⟧
  reify Γ (ax) = Env.first Γ
  reify Γ (exch i t) = reify (Env.exch i Γ) t
  reify Γ++Δ (pair s t) with Env.split Γ++Δ
  ... | Γ , Δ = (reify Γ s , reify Δ t)
  reify Γ++Δ (case s t) with Env.split Γ++Δ
  ... | Γ , Δ = case (reify Γ s) of λ { (x , y) → reify (x , (y , Δ)) t }
  reify Γ (abs t) = λ x → reify (x , Γ) t
  reify Γ++Δ (app s t) with Env.split Γ++Δ
  ... | Γ , Δ = (reify Γ s) (reify Δ t)
\end{code}

\begin{code}
  [_] : ∀ {A} → ∅ ⊢ A → ⟦ A ⟧
  [_] = reify ∅
\end{code}



\section{Lambek-Grishin Calculus (fLG)}

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

    data [_]⊢_ : Type → Struct- → Set where
      ax     : ∀ {A} → [ A ]⊢ · A ·
      μ̃      : ∀ {X A} → · A · ⊢ X → [ A ]⊢ X
      ⊕L     : ∀ {X Y A B} → [ B ]⊢ Y → [ A ]⊢ X → [ B ⊕ A ]⊢ X ⊕ Y
      ⇒L    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → [ A ⇒ B ]⊢ X ⇒ Y
      ⇐L    : ∀ {X Y A B} → [ B ]⊢ Y → X ⊢[ A ] → [ B ⇐ A ]⊢ Y ⇐ X

    data _⊢[_] : Struct+ → Type → Set where
      ax     : ∀ {A} → · A · ⊢[ A ]
      μ      : ∀ {X A} → X ⊢ · A · → X ⊢[ A ]
      ⊗R     : ∀ {X Y A B} → X ⊢[ A ] → Y ⊢[ B ] → X ⊗ Y ⊢[ A ⊗ B ]
      ⇚R    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → X ⇚ Y ⊢[ A ⇚ B ]
      ⇛R    : ∀ {X Y A B} → [ B ]⊢ Y → X ⊢[ A ] → Y ⇛ X ⊢[ B ⇛ A ]
\end{code}

\begin{code}
  raise : ∀ {A B} → · A · ⊢ · (B ⇐ A) ⇒ B ·
  raise = ⇒R (res₂ (res₃ (μ̃* (⇐L ax ax))))

  lower : ∀ {A B} → · B ⇚ (A ⇛ B) · ⊢ · A ·
  lower = ⇚L (dres₂ (dres₃ (μ* (⇛R ax ax))))
\end{code}

\ifverbose
\begin{code}
  module LP = LinearLogic U R ⟦_⟧ᵁ
  open LP hiding (reify) renaming (Type to TypeLP; _⊢_ to _⊢LP_; ⟦_⟧ to ⟦_⟧ᵀ)
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
  mutual
    cps+ : Type → TypeLP
    cps+ (el A +)   = el A
    cps+ (el A -)   = ¬ (¬ el A)
    cps+ (A ⊗ B)   = cps+ A ⊗ cps+ B
    cps+ (B ⇚ A)  = cps+ B ⊗ cps- A
    cps+ (A ⇛ B)  = cps- A ⊗ cps+ B
    cps+ (A ⊕ B)   = ¬ (cps- A ⊗ cps- B)
    cps+ (A ⇒ B)  = ¬ (cps+ A ⊗ cps- B)
    cps+ (B ⇐ A)  = ¬ (cps- B ⊗ cps+ A)

    cps- : Type → TypeLP
    cps- (el A +)  = ¬ el A
    cps- (el A -)  = ¬ el A
    cps- (A ⊗ B)   = ¬ (cps+ A ⊗ cps+ B)
    cps- (B ⇚ A)  = ¬ (cps+ B ⊗ cps- A)
    cps- (A ⇛ B)  = ¬ (cps- A ⊗ cps+ B)
    cps- (A ⊕ B)   = cps- A ⊗ cps- B
    cps- (A ⇒ B)  = cps+ A ⊗ cps- B
    cps- (B ⇐ A)  = cps- B ⊗ cps+ A
\end{code}

\ifverbose
\begin{code}
  mutual
    size+ : Struct+ → ℕ
    size+ · A ·     = 1
    size+ (A ⊗ B)   = size+ A +ℕ size+ B
    size+ (B ⇚ A)  = size+ B +ℕ size- A
    size+ (A ⇛ B)  = size- A +ℕ size+ B

    size- : Struct- → ℕ
    size- · A ·     = 1
    size- (A ⊕ B)   = size- A +ℕ size- B
    size- (A ⇒ B)  = size+ A +ℕ size- B
    size- (B ⇐ A)  = size- B +ℕ size+ A
\end{code}
\fi

\begin{code}
  mutual
    str+ : (s : Struct+) → Ctxt (size+ s)
    str+ (· A ·)   = cps+ A , ∅
    str+ (A ⊗ B)   = str+ A ++ str+ B
    str+ (B ⇚ A)  = str+ B ++ str- A
    str+ (A ⇛ B)  = str- A ++ str+ B

    str- : (s : Struct-) → Ctxt (size- s)
    str- (· A ·)   = cps- A , ∅
    str- (A ⊕ B)   = str- A ++ str- B
    str- (A ⇒ B)  = str+ A ++ str- B
    str- (B ⇐ A)  = str- B ++ str+ A
\end{code}

\begin{code}
  record CPS (A : Set) (B : A → Set) : Set where
    constructor cps
    field
      ⟦_⟧ : (x : A) → B x
  open CPS {{...}} public using (⟦_⟧)

  Struct+CPS : CPS Struct+ (λ x → Ctxt (size+ x))
  Struct+CPS = cps str+

  Struct-CPS : CPS Struct- (λ x → Ctxt (size- x))
  Struct-CPS = cps str-

  Type+CPS : CPS Type (λ _ → TypeLP)
  Type+CPS = cps cps+
\end{code}

\begin{code}
  cps+A≡¬cps-A∨cps-A≡¬cps+A : (A : Type) → cps+ A ≡ cps- A ⊸ ⊥ ⊎ cps- A ≡ cps+ A ⊸ ⊥
  cps+A≡¬cps-A∨cps-A≡¬cps+A (el A +)  = inj₂ refl
  cps+A≡¬cps-A∨cps-A≡¬cps+A (el A -)  = inj₁ refl
  cps+A≡¬cps-A∨cps-A≡¬cps+A (A ⊗ B)   = inj₂ refl
  cps+A≡¬cps-A∨cps-A≡¬cps+A (B ⇚ A)  = inj₂ refl
  cps+A≡¬cps-A∨cps-A≡¬cps+A (A ⇛ B)  = inj₂ refl
  cps+A≡¬cps-A∨cps-A≡¬cps+A (A ⊕ B)   = inj₁ refl
  cps+A≡¬cps-A∨cps-A≡¬cps+A (A ⇒ B)  = inj₁ refl
  cps+A≡¬cps-A∨cps-A≡¬cps+A (B ⇐ A)  = inj₁ refl
\end{code}

\begin{code}
  lemma-μ* : ∀ A {x} (X : Ctxt x) → X ⊢LP cps+ A → X ,′ cps- A ⊢LP ⊥
  lemma-μ* A X t with cps+A≡¬cps-A∨cps-A≡¬cps+A A
  lemma-μ* A X t | inj₂ p rewrite p = to-front X (app ax t)
  lemma-μ* A X t | inj₁ p = app lem ax
    where
      lem : X ⊢LP cps- A ⊸ ⊥
      lem rewrite sym p = t

  lemma-μ̃* : ∀ A {x} (X : Ctxt x) → X ⊢LP cps- A → cps+ A , X ⊢LP ⊥
  lemma-μ̃* A X t with cps+A≡¬cps-A∨cps-A≡¬cps+A A
  lemma-μ̃* A X t | inj₁ p rewrite p = app ax t
  lemma-μ̃* A X t | inj₂ p = to-back X (app lem ax)
    where
      lem : X ⊢LP cps+ A ⊸ ⊥
      lem rewrite sym p = t

  -- These are the really worrying cases, as I don't know whether or
  -- not "A ⊸ ⊥ , X ⊢ ⊥ → X ⊢ A" is even a derivable inference rule
  -- in linear logic.

  lemma-μ̃  : ∀ A {x} (X : Ctxt x) → (cps+ A , X) ⊢LP ⊥ → X ⊢LP cps- A
  lemma-μ̃  A X t with cps+A≡¬cps-A∨cps-A≡¬cps+A A
  lemma-μ̃  A X t | inj₂ p rewrite p = abs t
  lemma-μ̃  A X t | inj₁ p = prf
    where
      lem : cps- A ⊸ ⊥ , X ⊢LP ⊥
      lem rewrite sym p = t
      prf : X ⊢LP cps- A
      prf = {!!}

  lemma-μ  : ∀ A {x} (X : Ctxt x) → X ,′ cps- A ⊢LP ⊥ → X ⊢LP cps+ A
  lemma-μ  A X t with cps+A≡¬cps-A∨cps-A≡¬cps+A A
  lemma-μ  A X t | inj₁ p rewrite p = abs (to-back X t)
  lemma-μ  A X t | inj₂ p = prf
    where
      lem : cps+ A ⊸ ⊥ , X ⊢LP ⊥
      lem rewrite sym p = to-back X t
      prf : X ⊢LP cps+ A
      prf = {!!}
\end{code}

\begin{code}
  mutual
    reify  : ∀ {X Y} → X ⊢ Y → ⟦ X ⟧ ++ ⟦ Y ⟧ ⊢LP ⊥
    reify (μ* {X} {A} s) = lemma-μ* A ⟦ X ⟧ (reifyʳ s)
    reify (μ̃* {X} {A} s) = lemma-μ̃* A ⟦ X ⟧ (reifyˡ s)
    reify (⊗L {X} s) = lemma-⊗L ⟦ X ⟧ (reify s)
    reify (⇚L {X} s) = lemma-⇚L ⟦ X ⟧ (reify s)
    reify (⇛L {X} s) = lemma-⇛L ⟦ X ⟧ (reify s)
    reify (⊕R {X} s) = lemma-⊕R ⟦ X ⟧ (reify s)
    reify (⇒R {X} s) = lemma-⇒R ⟦ X ⟧ (reify s)
    reify (⇐R {X} s) = lemma-⇐R ⟦ X ⟧ (reify s)
    reify (res₁ {X} {Y} {Z} s) = lemma-res₁ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (res₂ {X} {Y} {Z} s) = lemma-res₂ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (res₃ {X} {Y} {Z} s) = lemma-res₃ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (res₄ {X} {Y} {Z} s) = lemma-res₄ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (dres₁ {X} {Y} {Z} s) = lemma-dres₁ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (dres₂ {X} {Y} {Z} s) = lemma-dres₂ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (dres₃ {X} {Y} {Z} s) = lemma-dres₃ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (dres₄ {X} {Y} {Z} s) = lemma-dres₄ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify s)
    reify (dist₁ {X} {Y} {Z} {W} s) = lemma-dist₁ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify s)
    reify (dist₂ {X} {Y} {Z} {W} s) = lemma-dist₂ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify s)
    reify (dist₃ {X} {Y} {Z} {W} s) = lemma-dist₃ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify s)
    reify (dist₄ {X} {Y} {Z} {W} s) = lemma-dist₄ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify s)

    reifyˡ : ∀ {A Y} → [ A ]⊢ Y → ⟦ Y ⟧ ⊢LP cps- A
    reifyˡ ax = ax
    reifyˡ (μ̃ {X} {A} s) = lemma-μ̃ A ⟦ X ⟧ (reify s)
    reifyˡ (⊕L {X} {Y} s t) = lemma-⊕L ⟦ X ⟧ ⟦ Y ⟧ (pair (reifyˡ s) (reifyˡ t))
    reifyˡ (⇒L {X} {Y} s t) = pair (reifyʳ s) (reifyˡ t)
    reifyˡ (⇐L {X} {Y} s t) = pair (reifyˡ s) (reifyʳ t)

    reifyʳ : ∀ {X A} → X ⊢[ A ] → ⟦ X ⟧ ⊢LP cps+ A
    reifyʳ ax = ax
    reifyʳ (μ {X} {A} s) = lemma-μ A ⟦ X ⟧ (reify s)
    reifyʳ (⊗R s t) = pair (reifyʳ s) (reifyʳ t)
    reifyʳ (⇚R s t) = pair (reifyʳ s) (reifyˡ t)
    reifyʳ (⇛R s t) = pair (reifyˡ s) (reifyʳ t)
\end{code}

\begin{code}
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)

data Univ : Set where
  S  : Univ
  N  : Univ
  NP : Univ

Entity : Set
Entity = Fin 2

⟦_⟧ᵁ : Univ → Set
⟦ S   ⟧ᵁ = Bool
⟦ NP  ⟧ᵁ = Entity
⟦ N   ⟧ᵁ = Entity → Bool

module LP = LinearLogic Univ S ⟦_⟧ᵁ
open LP renaming (Type to LP; ⟦_⟧ to ⟦_⟧LP)
module LG = LambekGrishinCalculus Univ S ⟦_⟧ᵁ
open LG renaming (Type to LG)

testTV : ⟦ (el NP + ⇒ el S -) ⇐ el NP + ⟧ ≡ ((el NP ⊗ (el S ⊸ ⊥)) ⊗ el NP) ⊸ ⊥
testTV = refl

testGQ : ⟦ el NP + ⇐ el N + ⟧ ≡ ((el NP ⊸ ⊥) ⊗ el N) ⊸ ⊥
testGQ = refl
\end{code}

\end{document}
