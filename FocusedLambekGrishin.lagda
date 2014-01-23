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
module FocusedLambekGrishin (U : Set) (R : U) (⟦_⟧ᵁ : U → Set) where
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
data Type : Set where
  el   : (A : U) → Type
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
raise {A} {B} = ⇒R (res₂ (res₃ (μ̃* (⇐L covar var))))

lower : ∀ {A B} → · B ⇚ (A ⇛ B) · ⊢ · A ·
lower {A} {B} = ⇚L (dres₂ (dres₃ (μ* (⇛R covar var))))
\end{code}

\ifverbose
\begin{code}
open import LinearLogic U R ⟦_⟧ᵁ as LP hiding (reify) renaming (Type to TypeLP; _⊢_ to _⊢LP_; ⟦_⟧ to ⟦_⟧ᵀ)
\end{code}
\fi

\begin{code}
record CBV (A B : Set) : Set where
  field
    ⌈_⌉ : A → B
open CBV {{...}} using (⌈_⌉)
\end{code}

\begin{code}
CBVType : CBV Type TypeLP
CBVType = record { ⌈_⌉ = cbv }
  where
    cbv : Type → TypeLP
    cbv (el A)    = el A
    cbv (A ⊗ B)   = {!!}
    cbv (A ⇒ B)  = ¬ cbv B ⊸ ¬ cbv A
    cbv (B ⇐ A)  = ¬ cbv B ⊸ ¬ cbv A
    cbv (A ⊕ B)   = {!!}
    cbv (A ⇚ B)  = ¬ (¬ cbv B ⊸ ¬ cbv A)
    cbv (B ⇛ A)  = ¬ (¬ cbv B ⊸ ¬ cbv A)

private
  mutual
    cbv+ : Struct+ → List TypeLP
    cbv+ · A · = ⌈ A ⌉ , ∅
    cbv+ (X ⊗ Y) = cbv+ X ++ cbv+ Y
    cbv+ (Y ⇚ X) = cbv+ Y ++ cbv- X
    cbv+ (X ⇛ Y) = cbv- X ++ cbv+ Y

    cbv- : Struct- → List TypeLP
    cbv- · A · = ¬ ⌈ A ⌉ , ∅
    cbv- (X ⊕ Y) = cbv- X ++ cbv- Y
    cbv- (X ⇒ Y) = cbv+ X ++ cbv- Y
    cbv- (Y ⇐ X) = cbv- Y ++ cbv+ X

CBVStruct+ : CBV Struct+ (List TypeLP)
CBVStruct+ = record { ⌈_⌉ = cbv+ }

CBVStruct- : CBV Struct- (List TypeLP)
CBVStruct- = record { ⌈_⌉ = cbv- }
\end{code}

\begin{code}
mutual
  reify  : ∀ {X Y} → X ⊢ Y → ⌈ X ⌉ ++ ⌈ Y ⌉ ⊢LP ⊥
  reify (μ* x) = {!!}
  reify (μ̃* x) = {!!}
  reify (⊗L t) = {!!}
  reify (⇚L t) = {!!}
  reify (⇛L t) = {!!}
  reify (⊕R t) = {!!}
  reify (⇒R t) = {!!}
  reify (⇐R t) = {!!}
  reify (res₁ t) = {!!}
  reify (res₂ t) = {!!}
  reify (res₃ t) = {!!}
  reify (res₄ t) = {!!}
  reify (dres₁ t) = {!!}
  reify (dres₂ t) = {!!}
  reify (dres₃ t) = {!!}
  reify (dres₄ t) = {!!}
  reify (dist₁ t) = {!!}
  reify (dist₂ t) = {!!}
  reify (dist₃ t) = {!!}
  reify (dist₄ t) = {!!}

  reifyʳ : ∀ {X B} → X ⊢[ B ] → ⌈ X ⌉ ⊢LP (⌈ B ⌉ ⊸ ⊥) ⊸ ⊥
  reifyʳ var = abs (app var var)
  reifyʳ (μ t) = abs (to-back (reify t))
  reifyʳ (⊗R s t) = {!!}
  reifyʳ (⇚R s t) = {!!}
  reifyʳ (⇛R s t) = {!!}

  reifyˡ : ∀ {A Y} → [ A ]⊢ Y → ⌈ Y ⌉ ⊢LP ⌈ A ⌉ ⊸ ⊥
  reifyˡ covar = var
  reifyˡ (μ̃ t) = abs (reify t)
  reifyˡ (⊕L s t) = {!!}
  reifyˡ (⇒L s t) = abs {!!}
  reifyˡ (⇐L s t) = abs {!!}
\end{code}
%}
