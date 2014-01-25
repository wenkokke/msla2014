%include agda.fmt

\ifverbose
\begin{code}
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
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
data Pos : Type → Set where
  el : ∀ A → Pos (el A +)
  _⊗_ : ∀ A B → Pos (A ⊗ B)
  _⇚_ : ∀ B A → Pos (B ⇚ A)
  _⇛_ : ∀ A B → Pos (A ⇛ B)

Pos? : ∀ A → Dec (Pos A)
Pos? (el A +) = yes (el A)
Pos? (el A -) = no (λ ())
Pos? (A ⊗ B) = yes (A ⊗ B)
Pos? (A ⇒ B) = no (λ ())
Pos? (A ⇐ B) = no (λ ())
Pos? (A ⊕ B) = no (λ ())
Pos? (A ⇚ B) = yes (A ⇚ B)
Pos? (A ⇛ B) = yes (A ⇛ B)

data Neg : Type → Set where
  el : ∀ A → Neg (el A -)
  _⊕_ : ∀ A B → Neg (A ⊕ B)
  _⇒_ : ∀ A B → Neg (A ⇒ B)
  _⇐_ : ∀ B A → Neg (B ⇐ A)

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

  data _⊢[_] : Struct+ → Type → Set where
    var    : ∀ {A} {{p : True (Pos? A)}} → · A · ⊢[ A ]
    μ      : ∀ {X A} {p : True (Neg? A)} → X ⊢ · A · → X ⊢[ A ]
    ⊗R     : ∀ {X Y A B} → X ⊢[ A ] → Y ⊢[ B ] → X ⊗ Y ⊢[ A ⊗ B ]
    ⇚R    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → X ⇚ Y ⊢[ A ⇚ B ]
    ⇛R    : ∀ {X Y A B} → [ A ]⊢ X → Y ⊢[ B ] → X ⇛ Y ⊢[ A ⇛ B ]

  data [_]⊢_ : Type → Struct- → Set where
    covar  : ∀ {A} {{p : True (Neg? A)}} → [ A ]⊢ · A ·
    μ̃      : ∀ {X A} {p : True (Pos? A)} → · A · ⊢ X → [ A ]⊢ X
    ⊕L     : ∀ {X Y A B} → [ A ]⊢ Y → [ B ]⊢ X → [ A ⊕ B ]⊢ X ⊕ Y
    ⇒L    : ∀ {X Y A B} → X ⊢[ A ] → [ B ]⊢ Y → [ A ⇒ B ]⊢ X ⇒ Y
    ⇐L    : ∀ {X Y A B} → [ A ]⊢ Y → X ⊢[ B ] → [ A ⇐ B ]⊢ Y ⇐ X
\end{code}

\begin{code}
raise : ∀ {A B} {p : True (Pos? A)} {q : True (Neg? B)} → · A · ⊢ · (B ⇐ A) ⇒ B ·
raise = ⇒R (res₂ (res₃ (μ̃* (⇐L covar var))))

lower : ∀ {A B} {p : True (Neg? A)} {q : True (Pos? B)} → · B ⇚ (A ⇛ B) · ⊢ · A ·
lower = ⇚L (dres₂ (dres₃ (μ* (⇛R covar var))))
\end{code}

\ifverbose
\begin{code}
open import LinearLogic U R ⟦_⟧ᵁ as LP hiding (reify) renaming (Type to TypeLP; _⊢_ to _⊢LP_; ⟦_⟧ to ⟦_⟧ᵀ)
\end{code}
\fi

\begin{code}
cps : Polarity → Type → TypeLP
cps + (el A +)  = el A
cps + (el A -)  = ¬ (¬ el A)
cps + (A ⊗ B)   = cps + A ⊗ cps + B
cps + (A ⇚ B)  = cps + A ⊗ cps - B
cps + (A ⇛ B)  = cps - A ⊗ cps + B
cps + (A ⊕ B)   = ¬ (cps - A ⊗ cps - B)
cps + (A ⇒ B)  = ¬ (cps + A ⊗ cps - B)
cps + (A ⇐ B)  = ¬ (cps - A ⊗ cps + B)
cps - (el A +)  = ¬ el A
cps - (el A -)  = ¬ el A
cps - (A ⊗ B)   = ¬ (cps + A ⊗ cps + B)
cps - (A ⇚ B)  = ¬ (cps + A ⊗ cps - B)
cps - (A ⇛ B)  = ¬ (cps - A ⊗ cps + B)
cps - (A ⊕ B)   = cps - A ⊗ cps - B
cps - (A ⇒ B)  = cps + A ⊗ cps - B
cps - (A ⇐ B)  = cps - A ⊗ cps + B
\end{code}

Co-variables only occur in negative contexts, and variables
only occur in positive contexts. So again, if the context and
the actual polarizations clash, we add a negation.

\begin{code}
mutual
  str+ : (s : Struct+) → List TypeLP
  str+ (· A ·)   = cps + A , ∅
  str+ (A ⊗ B)   = str+ A ++ str+ B
  str+ (A ⇚ B)  = str+ A ++ str- B
  str+ (A ⇛ B)  = str- A ++ str+ B

  str- : (s : Struct-) → List TypeLP
  str- (· A ·)   = cps - A , ∅
  str- (A ⊕ B)   = str- A ++ str- B
  str- (A ⇒ B)  = str+ A ++ str- B
  str- (A ⇐ B)  = str- A ++ str+ B
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
Neg-≡ : ∀ {A} → Neg A → cps + A ≡ cps - A ⊸ ⊥
Neg-≡ {.(el A -)} (el A) = refl
Neg-≡ {.(A ⊕ B)} (A ⊕ B) = refl
Neg-≡ {.(A ⇒ B)} (A ⇒ B) = refl
Neg-≡ {.(A ⇐ B)} (A ⇐ B) = refl

Pos-≡ : ∀ {A} → Pos A → cps - A ≡ cps + A ⊸ ⊥
Pos-≡ {.(el A +)} (el A) = refl
Pos-≡ {.(A ⊗ B)} (A ⊗ B) = refl
Pos-≡ {.(A ⇚ B)} (A ⇚ B) = refl
Pos-≡ {.(A ⇛ B)} (A ⇛ B) = refl
\end{code}

\begin{code}
mutual
  reify  : ∀ {X Y} → X ⊢ Y → ⟦ X ⟧ ++ ⟦ Y ⟧ ⊢LP ⊥
  reify (μ* {X} {A} {p} t) rewrite Pos-≡ (toWitness p) = to-front (app var (reifyʳ t))
  reify (μ̃* {X} {A} {q} t) rewrite sym (Neg-≡ (toWitness q)) = to-back (app (reifyˡ t) var)
  reify (⊗L {X} {A} {B} t) = pair-left (reify t)
  reify (⇚L {X} {A} {B} t) = pair-left (reify t)
  reify (⇛L {X} {A} {B} t) = pair-left (reify t)
  reify (⊕R {X} {A} {B} t) = pair-leftʳ {⟦ X ⟧} {cps - A} {cps - B} (reify t)
  reify (⇒R {X} {A} {B} t) = pair-leftʳ {⟦ X ⟧} {cps + A} {cps - B} (reify t)
  reify (⇐R {X} {A} {B} t) = pair-leftʳ {⟦ X ⟧} {cps - A} {cps + B} (reify t)
  reify (res₁ {X} {Y} {Z} t)  rewrite sym (++-assoc ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧) = Y[XZ]↝X[YZ] ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify t)
  reify (res₂ {X} {Y} {Z} t)  rewrite      ++-assoc ⟦ Y ⟧ ⟦ X ⟧ ⟦ Z ⟧  = [YX]Z↝[XY]Z ⟦ Y ⟧ ⟦ X ⟧ ⟦ Z ⟧ (reify t)
  reify (res₃ {X} {Y} {Z} t)  rewrite sym (++-assoc ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧) = X[ZY]↝X[YZ] ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ (reify t)
  reify (res₄ {X} {Y} {Z} t)  rewrite      ++-assoc ⟦ X ⟧ ⟦ Z ⟧ ⟦ Y ⟧  = [XZ]Y↝[XY]Z ⟦ X ⟧ ⟦ Z ⟧ ⟦ Y ⟧ (reify t)
  reify (dres₁ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧  = [XZ]Y↝[XY]Z ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧ (reify t)
  reify (dres₂ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ Z ⟧ ⟦ X ⟧ ⟦ Y ⟧) = X[ZY]↝X[YZ] ⟦ Z ⟧ ⟦ X ⟧ ⟦ Y ⟧ (reify t)
  reify (dres₃ {X} {Y} {Z} t) rewrite      ++-assoc ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧  = [YX]Z↝[XY]Z ⟦ Z ⟧ ⟦ Y ⟧ ⟦ X ⟧ (reify t)
  reify (dres₄ {X} {Y} {Z} t) rewrite sym (++-assoc ⟦ Y ⟧ ⟦ Z ⟧ ⟦ X ⟧) = Y[XZ]↝X[YZ] ⟦ Y ⟧ ⟦ Z ⟧ ⟦ X ⟧ (reify t)
  reify (dist₁ {X} {Y} {Z} {W} t) = XYZW↝XWZY ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)
  reify (dist₂ {X} {Y} {Z} {W} t) = XYZW↝YWXZ ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)
  reify (dist₃ {X} {Y} {Z} {W} t) = XYZW↝ZXWY ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)
  reify (dist₄ {X} {Y} {Z} {W} t) = XYZW↝ZYXW ⟦ X ⟧ ⟦ Y ⟧ ⟦ Z ⟧ ⟦ W ⟧ (reify t)

  reifyʳ : ∀ {X A} → X ⊢[ A ] → ⟦ X ⟧ ⊢LP ⟦ A ⟧
  reifyʳ var = var
  reifyʳ (μ {X} {A} {q} t) rewrite Neg-≡ (toWitness q) = abs (to-back (reify t))
  reifyʳ (⊗R {X} {Y} {A} {B} s t) = pair (reifyʳ s) (reifyʳ t)
  reifyʳ (⇚R {X} {Y} {A} {B} s t) = {!!}
  reifyʳ (⇛R {X} {Y} {A} {B} s t) = {!!}

  reifyˡ : ∀ {A Y} → [ A ]⊢ Y → ⟦ Y ⟧ ⊢LP ¬ ⟦ A ⟧
  reifyˡ (covar {{q}}) rewrite Neg-≡ (toWitness q) = abs (app var var)
  reifyˡ (μ̃ {X} {A} {_} t) = abs (reify t)
  reifyˡ (⊕L {X} {Y} {A} {B} s t) = {!!}
  reifyˡ (⇒L {X} {Y} {A} {B} s t) = {!!}
  reifyˡ (⇐L {X} {Y} {A} {B} s t) = {!!}
\end{code}
%}
