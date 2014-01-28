open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)

module example2 where

data U : Set where S N NP : U

R = S

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


raise : ∀ {A B} {p : True (Pos? A)} {q : True (Neg? B)} → · A · ⊢ · (B ⇐ A) ⇒ B ·
raise = ⇒R (res₂ (res₃ (μ̃* (⇐L covar var))))


lower : ∀ {A B} {p : True (Neg? A)} {q : True (Pos? B)} → · B ⇚ (A ⇛ B) · ⊢ · A ·
lower = ⇚L (dres₂ (dres₃ (μ* (⇛R covar var))))
