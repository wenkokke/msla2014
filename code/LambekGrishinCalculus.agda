open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)

module LambekGrishinCalculus (U : Set) (R : U) (⟦_⟧ᵁ : U → Set) where

infix  30 _⊗_ _⊕_
infixr 20 _⇒_ _⇛_
infixl 20 _⇐_ _⇚_
infix  5  _⊢_ [_]⊢_ _⊢[_]

data Polarity : Set where
  + : Polarity
  - : Polarity

_≟ᴾ_ : (p q : Polarity) → Dec (p ≡ q)
+ ≟ᴾ + = yes refl
+ ≟ᴾ - = no (λ ())
- ≟ᴾ + = no (λ ())
- ≟ᴾ - = yes refl

data Type : Set where
  el   : (A : U) → (p : Polarity) → Type
  _⊗_  : Type → Type → Type
  _⇒_  : Type → Type → Type
  _⇐_  : Type → Type → Type
  _⊕_  : Type → Type → Type
  _⇚_  : Type → Type → Type
  _⇛_  : Type → Type → Type

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

Pol? : ∀ A → Pos A ⊎ Neg A
Pol? (el A +)  = inj₁ (el A)
Pol? (el A -)  = inj₂ (el A)
Pol? (A ⊗ B)   = inj₁ (A ⊗ B)
Pol? (A ⇚ B)  = inj₁ (A ⇚ B)
Pol? (A ⇛ B)  = inj₁ (A ⇛ B)
Pol? (A ⊕ B)   = inj₂ (A ⊕ B)
Pol? (A ⇒ B)  = inj₂ (A ⇒ B)
Pol? (A ⇐ B)  = inj₂ (A ⇐ B)

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

raise : ∀ {A B} → · A · ⊢ · (B ⇐ A) ⇒ B ·
raise = ⇒R (res₂ (res₃ (μ̃* (⇐L covar var))))

lower : ∀ {A B} → · B ⇚ (A ⇛ B) · ⊢ · A ·
lower = ⇚L (dres₂ (dres₃ (μ* (⇛R covar var))))

import IntuitionisticLogic U ⟦_⟧ᵁ as IL
open IL.Explicit hiding (_⊢_; reify)
import LinearLogic U R ⟦_⟧ᵁ as LP
open LP renaming (Type to TypeLP; _⊢_ to _⊢LP_)

mutual
  ⟦_⟧+ : Type → TypeLP
  ⟦ el A +  ⟧+ = el A
  ⟦ el A -  ⟧+ = ¬ (¬ el A)
  ⟦ A ⊗ B   ⟧+ =      ⟦ A ⟧+ ⊗ ⟦ B ⟧+
  ⟦ A ⇚ B  ⟧+ =      ⟦ A ⟧+ ⊗ ⟦ B ⟧-
  ⟦ A ⇛ B  ⟧+ =      ⟦ A ⟧- ⊗ ⟦ B ⟧+
  ⟦ A ⊕ B   ⟧+ = ¬ (  ⟦ A ⟧- ⊗ ⟦ B ⟧-)
  ⟦ A ⇒ B  ⟧+ = ¬ (  ⟦ A ⟧+ ⊗ ⟦ B ⟧-)
  ⟦ A ⇐ B  ⟧+ = ¬ (  ⟦ A ⟧- ⊗ ⟦ B ⟧+)

  ⟦_⟧- : Type → TypeLP
  ⟦ el A +  ⟧- = ¬ el A
  ⟦ el A -  ⟧- = ¬ el A
  ⟦ A ⊗ B   ⟧- = ¬ (  ⟦ A ⟧+ ⊗ ⟦ B ⟧+)
  ⟦ A ⇚ B  ⟧- = ¬ (  ⟦ A ⟧+ ⊗ ⟦ B ⟧-)
  ⟦ A ⇛ B  ⟧- = ¬ (  ⟦ A ⟧- ⊗ ⟦ B ⟧+)
  ⟦ A ⊕ B   ⟧- =      ⟦ A ⟧- ⊗ ⟦ B ⟧-
  ⟦ A ⇒ B  ⟧- =      ⟦ A ⟧+ ⊗ ⟦ B ⟧-
  ⟦ A ⇐ B  ⟧- =      ⟦ A ⟧- ⊗ ⟦ B ⟧+

mutual
  ⟦_⟧+ : Struct+ → List TypeLP
  ⟦ · A ·   ⟧+ = ⟦ A ⟧+ , ∅
  ⟦ X ⊗ Y   ⟧+ = ⟦ X ⟧+ ⊗ ⟦ Y ⟧+
  ⟦ X ⇚ Y  ⟧+ = ⟦ X ⟧+ ⊗ ⟦ Y ⟧-
  ⟦ X ⇛ Y  ⟧+ = ⟦ X ⟧- ⊗ ⟦ Y ⟧+

  ⟦_⟧- : Struct- → List TypeLP
  ⟦ · A ·   ⟧- = ⟦ A ⟧- , ∅
  ⟦ X ⊕ Y   ⟧- = ⟦ X ⟧- ⊗ ⟦ Y ⟧-
  ⟦ X ⇒ Y  ⟧- = ⟦ X ⟧+ ⊗ ⟦ Y ⟧-
  ⟦ X ⇐ Y  ⟧- = ⟦ X ⟧- ⊗ ⟦ Y ⟧+

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


private
  open Reify {{...}} using (⟦_⟧)

Struct+Reify : Reify Struct+ (List TypeLP)
Struct+Reify = record { ⟦_⟧ = str+ }

Struct-Reify : Reify Struct- (List TypeLP)
Struct-Reify = record { ⟦_⟧ = str- }

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

mutual
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



