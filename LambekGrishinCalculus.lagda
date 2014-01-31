%include paper.fmt
%include LambekGrishinCalculus.fmt

\hidden{
\begin{code}
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)
\end{code}
}

\hidden{
\begin{code}
module LambekGrishinCalculus (U : Set) (R : U) (⟦_⟧ᵁ : U → Set) where
\end{code}
}


The Lambek-Grishin calculus is a symmetric version of the Lambek
calculus. This means that in addition to left and right implication
and conjunction, we add left and right difference (the operator dual
to implication) and disjunction.
From a linguistic perspective, the basic inference rules for these
connectives, together with a set of interaction principles, allows for
the treatment of patterns beyond the context-free, which cannot be
satisfactorily handled in the Lambek calculus \citep{moortgat2013}.

The formulation of the Lambek-Grishin calculus that we will formalize
is the formulation developed in \citet{moortgat2013}, which uses the
mechanisms of polarity and focusing \citep{andreoli1992} together with
concepts from display logics \citep{belnap1982} to ensure, amongst
others, that all proofs are in normal form.
Below we will discuss the roles the influences play in our model of
the Lambek-Grishin calculus in turn.

Since this paper is not by far a complete discussion of the
Lambek-Grishin calculus, we must refer the interested reader to
\citet{moortgat2013} and \citet{bastenhof2010}.

\subsection{Modeling a polarized logic}

The Lambek-Grishin calculus as developed in \citet{moortgat2013} is a
polarized logic. Therefore, we will have to define a notion of polarity.

\hidden{
\begin{code}
infix  30 _⊗_ _⊕_
infixr 20 _⇒_ _⇛_
infixl 20 _⇐_ _⇚_
infix  5  _⊢_ [_]⊢_ _⊢[_]
\end{code}
}

%<*polarity>
\begin{code}
data Polarity : Set where
  + : Polarity
  - : Polarity
\end{code}
%</polarity>

\hidden{
\begin{code}
_≟ᴾ_ : (p q : Polarity) → Dec (p ≡ q)
+ ≟ᴾ + = yes refl
+ ≟ᴾ - = no (λ ())
- ≟ᴾ + = no (λ ())
- ≟ᴾ - = yes refl
\end{code}
}

\noindent
Using this definition, we can define our types, assigning a polarity
to atomic type.

%<*type>
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
%</type>

\noindent
While the atomic types are assigned a polarity, the polarity of
complex types is implicit in the connectives. We shall therefore
define a pair of predicates that have inhabitants only if their
argument is a positive or negative type.

%<*pos>
\begin{code}
data Pos : Type → Set where
  el : ∀ A → Pos (el A +)
  _⊗_ : ∀ A B → Pos (A ⊗ B)
  _⇚_ : ∀ B A → Pos (B ⇚ A)
  _⇛_ : ∀ A B → Pos (A ⇛ B)
\end{code}
%</pos>

\hidden{
\begin{code}
Pos? : ∀ A → Dec (Pos A)
Pos? (el A +) = yes (el A)
Pos? (el A -) = no (λ ())
Pos? (A ⊗ B) = yes (A ⊗ B)
Pos? (A ⇒ B) = no (λ ())
Pos? (A ⇐ B) = no (λ ())
Pos? (A ⊕ B) = no (λ ())
Pos? (A ⇚ B) = yes (A ⇚ B)
Pos? (A ⇛ B) = yes (A ⇛ B)
\end{code}
}

%<*pos>
\begin{code}
data Neg : Type → Set where
  el : ∀ A → Neg (el A -)
  _⊕_ : ∀ A B → Neg (A ⊕ B)
  _⇒_ : ∀ A B → Neg (A ⇒ B)
  _⇐_ : ∀ B A → Neg (B ⇐ A)
\end{code}
%</pos>

\hidden{
\begin{code}
Neg? : ∀ A → Dec (Neg A)
Neg? (el A +) = no (λ ())
Neg? (el A -) = yes (el A)
Neg? (A ⊗ B) = no (λ ())
Neg? (A ⇒ B) = yes (A ⇒ B)
Neg? (A ⇐ B) = yes (A ⇐ B)
Neg? (A ⊕ B) = yes (A ⊕ B)
Neg? (A ⇚ B) = no (λ ())
Neg? (A ⇛ B) = no (λ ())
\end{code}
}

\noindent
We can trivially show that polarity is a decidable property, and that
every type is either positive or negative.

\begin{code}
Pol? : ∀ A → Pos A ⊎ Neg A
Pol? (el A +)  = inj₁ (el A)
Pol? (el A -)  = inj₂ (el A)
Pol? (A ⊗ B)   = inj₁ (A ⊗ B)
Pol? (A ⇚ B)  = inj₁ (A ⇚ B)
Pol? (A ⇛ B)  = inj₁ (A ⇛ B)
Pol? (A ⊕ B)   = inj₂ (A ⊕ B)
Pol? (A ⇒ B)  = inj₂ (A ⇒ B)
Pol? (A ⇐ B)  = inj₂ (A ⇐ B)
\end{code}



\subsection{Modeling a display calculus}

Since the Lambek-Grishin calculus is a display calculus, we will also
have to model polarized structures (positive/input structures for the
antacedent, negative/output structures for the succedent).
In this case, the formulas that can appear as arguments to a
connective are actually limited by their polarity, so we can encode
the polarities at the type-level.

%<*struct>
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
%</struct>

\noindent
As a consequence of this, we do not have to bother with predicates for
polarity in the case of structures, as a structure's polarity is
immediately obvious from its type.


\subsection{Modeling a focused logic}

\begin{code}
mutual
  data _⊢[_] : Struct+ → Type → Set where
    var    : ∀ {A} → · A · ⊢[ A ]
    μ      : ∀ {X A} {p : True (Neg? A)} → X ⊢ · A · → X ⊢[ A ]
    ⊗R     : ∀ {X Y A B} → X ⊢[ A ] → Y ⊢[ B ] → X ⊗ Y ⊢[ A ⊗ B ]
    ⇚R    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → X ⇚ Y ⊢[ A ⇚ B ]
    ⇛R    : ∀ {X Y A B} → [ A ]⊢ X → Y ⊢[ B ] → X ⇛ Y ⊢[ A ⇛ B ]

  data [_]⊢_ : Type → Struct- → Set where
    covar  : ∀ {A} → [ A ]⊢ · A ·
    μ̃      : ∀ {X A} {p : True (Pos? A)} → · A · ⊢ X → [ A ]⊢ X
    ⊕L     : ∀ {X Y A B} → [ A ]⊢ Y → [ B ]⊢ X → [ A ⊕ B ]⊢ X ⊕ Y
    ⇒L    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → [ A ⇒ B ]⊢ X ⇒ Y
    ⇐L    : ∀ {X Y A B} → [ A ]⊢ Y → X ⊢[ B ] → [ A ⇐ B ]⊢ Y ⇐ X

  data _⊢_ : Struct+ → Struct- → Set where
    μ*     : ∀ {X A} {p : True (Pos? A)} → X ⊢[ A ] → X ⊢ · A ·
    μ̃*     : ∀ {X A} {p : True (Neg? A)}→ [ A ]⊢ X → · A · ⊢ X
    ⊗L     : ∀ {X A B} → · A · ⊗ · B · ⊢ X → · A ⊗ B · ⊢ X
    ⇚L    : ∀ {X A B} → · A · ⇚ · B · ⊢ X → · A ⇚ B · ⊢ X
    ⇛L    : ∀ {X A B} → · A · ⇛ · B · ⊢ X → · A ⇛ B · ⊢ X
    ⊕R     : ∀ {X A B} → X ⊢ · A · ⊕ · B · → X ⊢ · A ⊕ B ·
    ⇒R    : ∀ {X A B} → X ⊢ · A · ⇒ · B · → X ⊢ · A ⇒ B ·
    ⇐R    : ∀ {X A B} → X ⊢ · A · ⇐ · B · → X ⊢ · A ⇐ B ·
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
\end{code}

\begin{code}
raise : ∀ {A B} → · A · ⊢ · (B ⇐ A) ⇒ B ·
raise = ⇒R (res₂ (res₃ (μ̃* (⇐L covar var))))

lower : ∀ {A B} → · B ⇚ (A ⇛ B) · ⊢ · A ·
lower = ⇚L (dres₂ (dres₃ (μ* (⇛R covar var))))
\end{code}


\subsection{Reification into LP}

\hidden{
\begin{code}
import IntuitionisticLogic U ⟦_⟧ᵁ as IL
open IL.Explicit hiding (_⊢_; reify)
import LinearLogic U R ⟦_⟧ᵁ as LP
open LP renaming (Type to TypeLP; _⊢_ to _⊢LP_)
\end{code}
}

\begin{code}
mutual
  ⟦_⟧+ : Type → TypeLP
  ⟦ el A +  ⟧+ = el A
  ⟦ el A -  ⟧+ = ¬ (¬ el A)
  ⟦ A ⊗ B   ⟧+ = ⟦ A ⟧+ ⊗ ⟦ B ⟧+
  ⟦ A ⇚ B  ⟧+ = ⟦ A ⟧+ ⊗ ⟦ B ⟧-
  ⟦ A ⇛ B  ⟧+ = ⟦ A ⟧- ⊗ ⟦ B ⟧+
  ⟦ A ⊕ B   ⟧+ = ¬ (⟦ A ⟧- ⊗ ⟦ B ⟧-)
  ⟦ A ⇒ B  ⟧+ = ¬ (⟦ A ⟧+ ⊗ ⟦ B ⟧-)
  ⟦ A ⇐ B  ⟧+ = ¬ (⟦ A ⟧- ⊗ ⟦ B ⟧+)

  ⟦_⟧- : Type → TypeLP
  ⟦ el A +  ⟧- = ¬ el A
  ⟦ el A -  ⟧- = ¬ el A
  ⟦ A ⊗ B   ⟧- = ¬ (⟦ A ⟧+ ⊗ ⟦ B ⟧+)
  ⟦ A ⇚ B  ⟧- = ¬ (⟦ A ⟧+ ⊗ ⟦ B ⟧-)
  ⟦ A ⇛ B  ⟧- = ¬ (⟦ A ⟧- ⊗ ⟦ B ⟧+)
  ⟦ A ⊕ B   ⟧- = ⟦ A ⟧- ⊗ ⟦ B ⟧-
  ⟦ A ⇒ B  ⟧- = ⟦ A ⟧+ ⊗ ⟦ B ⟧-
  ⟦ A ⇐ B  ⟧- = ⟦ A ⟧- ⊗ ⟦ B ⟧+
\end{code}

\hidden{
\begin{code}
mutual
  str+ : Struct+ → List TypeLP
  str+ (· A ·)   = ⟦ A ⟧+ , ∅
  str+ (A ⊗ B)   = str+ A ++ str+ B
  str+ (A ⇚ B)  = str+ A ++ str- B
  str+ (A ⇛ B)  = str- A ++ str+ B

  str- : Struct- → List TypeLP
  str- (· A ·)   = ⟦ A ⟧- , ∅
  str- (A ⊕ B)   = str- A ++ str- B
  str- (A ⇒ B)  = str+ A ++ str- B
  str- (A ⇐ B)  = str- A ++ str+ B
\end{code}
}

\hidden{
\begin{code}

private
  open Reify {{...}} using (⟦_⟧)

Struct+Reify : Reify Struct+ (List TypeLP)
Struct+Reify = record { ⟦_⟧ = str+ }

Struct-Reify : Reify Struct- (List TypeLP)
Struct-Reify = record { ⟦_⟧ = str- }
\end{code}
}

\hidden{
\begin{code}
Neg-≡ : ∀ {A} → Neg A → ⟦ A ⟧+ ≡ ⟦ A ⟧- ⊸ ⊥
Neg-≡ {.(el A -)} (el A) = refl
Neg-≡ {.(A ⊕ B)} (A ⊕ B) = refl
Neg-≡ {.(A ⇒ B)} (A ⇒ B) = refl
Neg-≡ {.(A ⇐ B)} (A ⇐ B) = refl

Pos-≡ : ∀ {A} → Pos A → ⟦ A ⟧- ≡ ⟦ A ⟧+ ⊸ ⊥
Pos-≡ {.(el A +)} (el A) = refl
Pos-≡ {.(A ⊗ B)} (A ⊗ B) = refl
Pos-≡ {.(A ⇚ B)} (A ⇚ B) = refl
Pos-≡ {.(A ⇛ B)} (A ⇛ B) = refl
\end{code}
}

\begin{spec}
mutual
  reify : ∀ {X Y} → X ⊢ Y → ⟦ X ⟧ ++ ⟦ Y ⟧ ⊢LP ⊥
  reify (μ* t)     = to-front (app var (reifyʳ t))
  reify (μ̃* t)     = app var (reifyˡ t)
  reify (⊗L t)     = pair-left (reify t)
  reify (⇚L t)    = pair-left (reify t)
  reify (⇛L t)    = pair-left (reify t)
  reify (⊕R t)     = pair-left′ (reify t)
  reify (⇒R t)    = pair-left′ (reify t)
  reify (⇐R t)    = pair-left′ (reify t)
  reify (res₁ t)   = Y[XZ]↝X[YZ] (reify t)
  reify (res₂ t)   = [YX]Z↝[XY]Z (reify t)
  reify (res₃ t)   = X[ZY]↝X[YZ] (reify t)
  reify (res₄ t)   = [XZ]Y↝[XY]Z (reify t)
  reify (dres₁ t)  = [XZ]Y↝[XY]Z (reify t)
  reify (dres₂ t)  = X[ZY]↝X[YZ] (reify t)
  reify (dres₃ t)  = [YX]Z↝[XY]Z (reify t)
  reify (dres₄ t)  = Y[XZ]↝X[YZ] (reify t)
  reify (dist₁ t)  = XYZW↝XWZY (reify t)
  reify (dist₂ t)  = XYZW↝YWXZ (reify t)
  reify (dist₃ t)  = XYZW↝ZXWY (reify t)
  reify (dist₄ t)  = XYZW↝ZYXW (reify t)

  reifyʳ : ∀ {X A} → X ⊢[ A ] → ⟦ X ⟧ ⊢LP ⟦ A ⟧+
  reifyʳ var        = var
  reifyʳ (μ t)      = abs (to-back (reify t))
  reifyʳ (⊗R s t)   = pair (reifyʳ s) (reifyʳ t)
  reifyʳ (⇚R s t)  = pair (reifyʳ s) (reifyˡ t)
  reifyʳ (⇛R s t)  = pair (reifyˡ s) (reifyʳ t)

  reifyˡ : ∀ {A Y} → [ A ]⊢ Y → ⟦ Y ⟧ ⊢LP ⟦ A ⟧-
  reifyˡ covar      = var
  reifyˡ (μ̃ t)      = abs (reify t)
  reifyˡ (⊕L s t)   = YX↝XY (pair (reifyˡ s) (reifyˡ t))
  reifyˡ (⇒L s t)  = pair (reifyʳ s) (reifyˡ t)
  reifyˡ (⇐L s t)  = pair (reifyˡ s) (reifyʳ t)
\end{spec}

\hidden{
\begin{code}
mutual
  reify  : ∀ {X Y} → X ⊢ Y → ⟦ X ⟧ ++ ⟦ Y ⟧ ⊢LP ⊥
  reify (μ* {X} {A} {p} t) rewrite Pos-≡ (toWitness p) = to-front (app var (reifyʳ t))
  reify (μ̃* {X} {A} {q} t) rewrite Neg-≡ (toWitness q) = app var (reifyˡ t)
  reify (⊗L {X} {A} {B} t) = pair-left (reify t)
  reify (⇚L {X} {A} {B} t) = pair-left (reify t)
  reify (⇛L {X} {A} {B} t) = pair-left (reify t)
  reify (⊕R {X} {A} {B} t) = pair-left′ {⟦ X ⟧} {⟦ A ⟧-} {⟦ B ⟧-} (reify t)
  reify (⇒R {X} {A} {B} t) = pair-left′ {⟦ X ⟧} {⟦ A ⟧+} {⟦ B ⟧-} (reify t)
  reify (⇐R {X} {A} {B} t) = pair-left′ {⟦ X ⟧} {⟦ A ⟧-} {⟦ B ⟧+} (reify t)
  reify (res₁ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧) = Y[XZ]↝X[YZ] ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify t)
  reify (res₂ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ Y ⟧ ⟦ X ⟧ ⟦ Z ⟧  = [YX]Z↝[XY]Z ⟦ Y ⟧ ⟦ X ⟧ ⟦ Z ⟧ (reify t)
  reify (res₃ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧) = X[ZY]↝X[YZ] ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify t)
  reify (res₄ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ X ⟧ ⟦ Z ⟧ ⟦ Y ⟧  = [XZ]Y↝[XY]Z ⟦ X ⟧ ⟦ Z ⟧ ⟦ Y ⟧ (reify t)
  reify (dres₁ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧  = [XZ]Y↝[XY]Z ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧ (reify t)
  reify (dres₂ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ Z ⟧ ⟦ X ⟧ ⟦ Y ⟧) = X[ZY]↝X[YZ] ⟦ Z ⟧ ⟦ X ⟧ ⟦ Y ⟧ (reify t)
  reify (dres₃ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧  = [YX]Z↝[XY]Z ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧ (reify t)
  reify (dres₄ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ Y ⟧ ⟦ Z ⟧ ⟦ X ⟧) = Y[XZ]↝X[YZ] ⟦ Y ⟧ ⟦ Z ⟧ ⟦ X ⟧ (reify t)
  reify (dist₁ {X} {Y} {Z} {W} t) = XYZW↝XWZY ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)
  reify (dist₂ {X} {Y} {Z} {W} t) = XYZW↝YWXZ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)
  reify (dist₃ {X} {Y} {Z} {W} t) = XYZW↝ZXWY ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)
  reify (dist₄ {X} {Y} {Z} {W} t) = XYZW↝ZYXW ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)

  reifyʳ : ∀ {X A} → X ⊢[ A ] → ⟦ X ⟧ ⊢LP ⟦ A ⟧+
  reifyʳ var = var
  reifyʳ (μ {X} {A} {q} t) rewrite Neg-≡ (toWitness q) = abs (to-back (reify t))
  reifyʳ (⊗R {X} {Y} {A} {B} s t) = pair (reifyʳ s) (reifyʳ t)
  reifyʳ (⇚R {X} {Y} {A} {B} s t) = pair (reifyʳ s) (reifyˡ t)
  reifyʳ (⇛R {X} {Y} {A} {B} s t) = pair (reifyˡ s) (reifyʳ t)

  reifyˡ : ∀ {A Y} → [ A ]⊢ Y → ⟦ Y ⟧ ⊢LP ⟦ A ⟧-
  reifyˡ covar = var
  reifyˡ (μ̃ {X} {A} {p} t) rewrite Pos-≡ (toWitness p) = abs (reify t)
  reifyˡ (⊕L {X} {Y} {A} {B} s t) = YX↝XY ⟦ X ⟧ ⟦ Y ⟧ (pair (reifyˡ s) (reifyˡ t))
  reifyˡ (⇒L {X} {Y} {A} {B} s t) = pair (reifyʳ s) (reifyˡ t)
  reifyˡ (⇐L {X} {Y} {A} {B} s t) = pair (reifyˡ s) (reifyʳ t)
\end{code}
}

\begin{code}

\end{code}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
