open import Level using (Level; _⊔_)
open import Function using (id; case_of_)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec as Vec using (Vec) renaming (_∷_ to _,_; [] to ∅)
open import Data.List using (_∷_; [])
open import Data.List as List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.Product as Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong)

module IntuitionisticLogic (U : Set) (⟦_⟧ᵁ : U → Set) where

infix  30 _⊗_
infixr 20 _⇒_

data Type : Set where
  el    : (A : U) → Type
  _⊗_   : Type → Type → Type
  _⇒_  : Type → Type → Type

module Implicit where

  infix  4  _⊢_

  data _⊢_ : ∀ {k} (Γ : Vec Type k) (A : Type) → Set where
    var   : ∀ {k} {Γ : Vec Type k} (x : Fin k) → Γ ⊢ Vec.lookup x Γ
    abs   : ∀ {A B} {k} {Γ : Vec Type k} → A , Γ ⊢ B → Γ ⊢ A ⇒ B
    app   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    pair  : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⊗ B
    case  : ∀ {A B C} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B → A , B , Γ ⊢ C → Γ ⊢ C

  swap : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B ⇒ B ⊗ A
  swap = abs (case (var zero) (pair (var (suc zero)) (var zero)))

  Vec-exch : ∀ {k} (i : Fin k) → Vec Type (suc k) → Vec Type (suc k)
  Vec-exch  zero    (A , B , Γ)  = B , A , Γ
  Vec-exch (suc i)  (A , Γ)      = A , (Vec-exch i Γ)

  lemma-var : ∀ {k} {Γ : Vec Type (suc k)} → ∀ i x → ∃ λ y → Vec.lookup x Γ ≡ Vec.lookup y (Vec-exch i Γ)
  lemma-var {Γ = A , B , Γ} zero     zero           = suc zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc zero)     = zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc (suc x))  = suc (suc x) , refl
  lemma-var {Γ = A , Γ} (suc i)  zero           = zero , refl
  lemma-var {Γ = A , Γ} (suc i)  (suc x)        = Product.map suc id (lemma-var {Γ = Γ} i x)

  exch : ∀ {k} {Γ : Vec Type (suc k)} {A} → ∀ i → Γ ⊢ A → Vec-exch i Γ ⊢ A
  exch {Γ = Γ} i (var x) with lemma-var {Γ = Γ} i x
  exch {Γ = Γ} i (var x) | y , p rewrite p  = var y
  exch i (abs t)     = abs (exch (suc i) t)
  exch i (app s t)   = app (exch i s) (exch i t)
  exch i (pair s t)  = pair (exch i s) (exch i t)
  exch i (case s t)  = case (exch i s) (exch (suc (suc i)) t)

module Explicit where

  infix  4  _⊢_

  data _⊢_ : ∀ (X : List Type) (A : Type) → Set where
    var   : ∀ {A} → A , ∅ ⊢ A
    abs   : ∀ {X A B} → A , X ⊢ B → X ⊢ A ⇒ B
    app   : ∀ {X Y A B} → X ⊢ A ⇒ B → Y ⊢ A → X ++ Y ⊢ B
    pair  : ∀ {X Y A B} → X ⊢ A → Y ⊢ B → X ++ Y ⊢ A ⊗ B
    case  : ∀ {X Y A B C} → X ⊢ A ⊗ B → A , B , Y ⊢ C → X ++ Y ⊢ C
    weak  : ∀ {X Y A} → X ⊢ A → X ++ Y ⊢ A
    cont  : ∀ {X A B} → A , A , X ⊢ B → A , X ⊢ B
    exch  : ∀ {X Y Z W A} →  (X ++ Z) ++ (Y ++ W) ⊢ A
          →  (X ++ Y) ++ (Z ++ W) ⊢ A

  exch₀ : ∀ {X A B C} → B , A , X ⊢ C → A , B , X ⊢ C
  exch₀ {X} {A} {B} = exch {∅} {A , ∅} {B , ∅} {X}

  swap : ∀ {X A B} → X ⊢ A ⊗ B ⇒ B ⊗ A
  swap {X} {A} {B} = abs (case var (exch₀ (pair var (weak {A , ∅} {X} var))))

  record Reify {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field
      ⟦_⟧ : A → B

  ReifyType : Reify Type Set
  ReifyType = record { ⟦_⟧ = ⟦_⟧ }
    where

    ⟦_⟧ : Type → Set
    ⟦ el A    ⟧ = ⟦ A ⟧ᵁ
    ⟦ A ⊗ B   ⟧ = ⟦ A ⟧ × ⟦ B ⟧
    ⟦ A ⇒ B  ⟧ = ⟦ A ⟧ → ⟦ B ⟧

  data Ctxt : ∀ (X : List Set) → Set₁ where
    ∅ : Ctxt ∅
    _,_ : ∀ {A X} → A → Ctxt X → Ctxt (A , X)

  private
    open Reify {{...}} using (⟦_⟧)

  ReifyCtxt : Reify (List Type) (List Set)
  ReifyCtxt = record { ⟦_⟧ = List.map ⟦_⟧ }

  Ctxt-insert : {A : Type} {X Y : List Type} → ⟦ A ⟧ → Ctxt ⟦ X ++ Y ⟧ → Ctxt ⟦ X ++ (A , Y) ⟧
  Ctxt-insert {A} {∅} {Y} A′ E = A′ , E
  Ctxt-insert {A} {B , X} {Y} A′ (B′ , E) = B′ , Ctxt-insert {A} {X} {Y} A′ E

  Ctxt-exch : {X Y Z W : List Type} → Ctxt ⟦ (X ++ Y) ++ (Z ++ W) ⟧ → Ctxt ⟦ (X ++ Z) ++ (Y ++ W) ⟧
  Ctxt-exch {X = ∅} {Y = ∅} {Z} {W} E = E
  Ctxt-exch {X = ∅} {Y = A , Y} {Z} {W} (A′ , E) = Ctxt-insert {A} {Z} {Y ++ W} A′ (Ctxt-exch {∅} {Y} {Z} {W} E)
  Ctxt-exch {X = A , X} {Y} {Z} {W} (A′ , E) = A′ , Ctxt-exch {X} {Y} {Z} {W} E

  Ctxt-split : {X Y : List Type} → Ctxt ⟦ X ++ Y ⟧ → Ctxt ⟦ X ⟧ × Ctxt ⟦ Y ⟧
  Ctxt-split {∅} {Y} E = ∅ , E
  Ctxt-split {A , X} {Y} (A′ , E) with Ctxt-split {X} {Y} E
  ... | Eˣ , Eʸ = ((A′ , Eˣ) , Eʸ)

  reify : {A : Type} {X : List Type} → X ⊢ A → (Ctxt ⟦ X ⟧ → ⟦ A ⟧)
  reify var         (A′ , ∅)  = A′
  reify (abs t)     E         = λ A′ → reify t (A′ , E)
  reify (app s t)   E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = (reify s Eˢ) (reify t Eᵗ)
  reify (pair s t)  E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = (reify s Eˢ , reify t Eᵗ)
  reify (case s t)  E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = case reify s Eˢ of λ{ (A′ , B′) → reify t (A′ , B′ , Eᵗ)}
  reify (weak {X} s)    E         with Ctxt-split {X} E
  ... | Eˢ , Eᵗ               = reify s Eˢ
  reify (cont t)    (A′ , E)  = reify t (A′ , A′ , E)
  reify (exch {X} {Y} {Z} {W} t)    E         = reify t (Ctxt-exch {X} {Y} {Z} {W} E)

  [_] : {A : Type} {X : List Type} → X ⊢ A → (Ctxt ⟦ X ⟧ → ⟦ A ⟧)
  [_] = reify

  swap′ : ∀ {A B} → ⟦ A ⟧ × ⟦ B ⟧ → ⟦ B ⟧ × ⟦ A ⟧
  swap′ {A} {B} = [ swap {∅} {A} {B} ] ∅

