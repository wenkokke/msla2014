open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit as Unit using (tt) renaming (⊤ to 1')
open import Data.Empty as Empty using () renaming (⊥ to 0')
open import Data.String as Str using (String) renaming (_++_ to _⊕_)

module IntuitionisticLogic (U : Set) where

  private
    open import Connectives U as Conn using (Type; el; _⇒_; _∧_; _∨_; ⊤; ⊥; ¬_)
    open import Context Type as Ctxt using (Ctxt; _,_; ∅; _++_)


  -- define the basic inference rules of our (intuitionistic) logic
  -- note how contexts are shared across premises and conclusion, which has the
  -- effect of encoding exchange, weakening and contraction implicitly
  -- there is an equivalent encoding which explicates these rules, but does not
  -- share contexts across inferences---however, since this is slightly more
  -- difficult to work with, we shall only move to this representation when
  -- we start encoding substructural logics

  infix 3 _⊢_

  data _⊢_ {n : ℕ} : (Γ : Ctxt n) (A : Type) → Set where
    var    : ∀ {Γ}
             i → Γ ⊢ (Ctxt.lookup i Γ)
    abs    : ∀ {Γ} {A B} →
             A , Γ ⊢ B → Γ ⊢ A ⇒ B
    app    : ∀ {Γ} {A B} →
             Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    pair   : ∀ {Γ} {A B} →
             Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
    fst    : ∀ {Γ} {A B} →
             Γ ⊢ A ∧ B → Γ ⊢ A
    snd    : ∀ {Γ} {A B} →
             Γ ⊢ A ∧ B → Γ ⊢ B
    inl    : ∀ {Γ} {A B} →
             Γ ⊢ A → Γ ⊢ A ∨ B
    inr    : ∀ {Γ} {A B} →
             Γ ⊢ B → Γ ⊢ A ∨ B
    case   : ∀ {Γ} {A B C} →
             Γ ⊢ A ∨ B → A , Γ ⊢ C → B , Γ ⊢ C → Γ ⊢ C
    unit   : ∀ {Γ} →
             Γ ⊢ ⊤
    empty  : ∀ {Γ} {A} →
             Γ ⊢ ⊥ → Γ ⊢ A



  -- defines some explicit inference rule for exchange and weakening
  -- to show that as these are implicit in the above rules

  exchᵢ : ∀ {n} {Γ : Ctxt (suc n)} {A} (i : Fin n) →
        Γ ⊢ A →  Ctxt.exch i Γ ⊢ A
  exchᵢ {Γ = Γ} i (var x) with Ctxt.exch-var Γ i x
  ... | y , p rewrite p = var y
  exchᵢ i (abs t)      = abs (exchᵢ (suc i) t)
  exchᵢ i (app s t)    = app (exchᵢ i s) (exchᵢ i t)
  exchᵢ i (pair s t)   = pair (exchᵢ i s) (exchᵢ i t)
  exchᵢ i (fst t)      = fst (exchᵢ i t)
  exchᵢ i (snd t)      = snd (exchᵢ i t)
  exchᵢ i (inl t)      = inl (exchᵢ i t)
  exchᵢ i (inr t)      = inr (exchᵢ i t)
  exchᵢ i (case s t u) = case (exchᵢ i s) (exchᵢ (suc i) t) (exchᵢ (suc i) u)
  exchᵢ i unit         = unit
  exchᵢ i (empty t)    = empty (exchᵢ i t)

  exch₀ : ∀ {A B C} {n} {Γ : Ctxt n} → A , B , Γ ⊢ C → B , A , Γ ⊢ C
  exch₀ = exchᵢ zero

  exch₁ : ∀ {A B C D} {n} {Γ : Ctxt n} → A , B , C , Γ ⊢ D → A , C , B , Γ ⊢ D
  exch₁ = exchᵢ (suc zero)

  weak : ∀ {n} {Γ : Ctxt n} {A B} → Γ ⊢ B → A , Γ ⊢ B
  weak (var i)      = var (Fin.raise 1 i)
  weak (abs t)      = abs (exch₀ (weak t))
  weak (app s t)    = app (weak s) (weak t)
  weak (pair s t)   = pair (weak s) (weak t)
  weak (fst t)      = fst (weak t)
  weak (snd t)      = snd (weak t)
  weak (inl t)      = inl (weak t)
  weak (inr t)      = inr (weak t)
  weak (case s t u) = case (weak s) (exch₀ (weak t)) (exch₀ (weak u))
  weak unit         = unit
  weak (empty t)    = empty (weak t)



  -- define some rules from intuitionistic natural deduction and sequent calculus
  -- to show that these are implicit in the system (and because I found them useful)

  ⇒-intro : ∀ {n} {Γ : Ctxt n} {A B} → Γ ⊢ A ⇒ B → A , Γ ⊢ B
  ⇒-intro t = app (weak t) (var zero)

  ∧-intro-right : ∀ {n} {Γ : Ctxt n} {A B C} → Γ ⊢ A ∧ B → A , B , Γ ⊢ C → Γ ⊢ C
  ∧-intro-right s t = app (app (abs (abs t)) (snd s)) (fst s)

  ∧-intro-left : ∀ {n} {Γ : Ctxt n} {A B C} → A ∧ B , Γ ⊢ C → A , B , Γ ⊢ C
  ∧-intro-left t = app (weak (weak (abs t))) (pair (var zero) (var (suc zero)))

  ∧-elim-left : ∀ {n} {Γ : Ctxt n} {A B C} → A , B , Γ ⊢ C → A ∧ B , Γ ⊢ C
  ∧-elim-left t = ∧-intro-right (var zero) (exch₁ (exch₀ (weak t)))

  ⊤-elim : ∀ {n} {Γ : Ctxt n} {A} → ⊤ , Γ ⊢ A → Γ ⊢ A
  ⊤-elim t = app (abs t) unit



  -- define a specific instance of exchange which is useful when we start to define
  -- the reification of classical logic into intuitionistic logic

  mutual
    move-left : ∀ {m} (Γ : Ctxt m) {n} {Δ : Ctxt n} {A B} → Γ ++ (A , Δ) ⊢ B → A , Γ ++ Δ ⊢ B
    move-left Γ {Δ = Δ} {A = A} (var i) with Ctxt.move-left Γ A Δ i
    ... | j , p rewrite p = var j
    move-left Γ (abs {A = C} t)     = abs (move-left₁ Γ C t)
    move-left Γ (app s t)           = app (move-left Γ s) (move-left Γ t)
    move-left Γ (pair s t)          = pair (move-left Γ s) (move-left Γ t)
    move-left Γ (fst t)             = fst (move-left Γ t)
    move-left Γ (snd t)             = snd (move-left Γ t)
    move-left Γ (inl t)             = inl (move-left Γ t)
    move-left Γ (inr t)             = inr (move-left Γ t)
    move-left Γ (case {A = C} {B = D} s t u) = case (move-left Γ s) (move-left₁ Γ C t) (move-left₁ Γ D u)
    move-left Γ unit                = unit
    move-left Γ (empty t)           = empty (move-left Γ t)

    move-left₁ : ∀ {m} (Γ : Ctxt m) {n} {Δ : Ctxt n} A {B C} → A , Γ ++ (B , Δ) ⊢ C → A , B , Γ ++ Δ ⊢ C
    move-left₁ Γ A t = exch₀ (move-left (A , Γ) t)



  -- defines standart reification of intuitionistic logic into agda's
  -- term representation (needs an interpretation for the universe)

  module Reify (⟦_⟧ᵁ : U → Set) where

    private
      open Conn.Reify ⟦_⟧ᵁ public using (⟦_⟧)
      open import Environment Type ⟦_⟧ as Env hiding (exch)

    reify : ∀ {n} {Γ : Ctxt n} {A} → Env Γ → Γ ⊢ A → ⟦ A ⟧
    reify ∅ (var ())
    reify (x , Γ) (var zero) = x
    reify (x , Γ) (var (suc i)) = reify Γ (var i)
    reify Γ (abs p) = λ x → reify (x , Γ) p
    reify Γ (app p q) = (reify Γ p) (reify Γ q)
    reify Γ (pair p q) = (reify Γ p , reify Γ q)
    reify Γ (fst p) = proj₁ (reify Γ p)
    reify Γ (snd p) = proj₂ (reify Γ p)
    reify Γ (inl p) = inj₁ (reify Γ p)
    reify Γ (inr p) = inj₂ (reify Γ p)
    reify Γ (case p q r) = elim (reify Γ p) (λ x → reify (x , Γ) q) (λ y → reify (y , Γ) r)
      where
        elim : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
        elim (inj₁ x) f g = f x
        elim (inj₂ y) f g = g y
    reify Γ unit = tt
    reify Γ (empty p) = elim (reify Γ p)
      where
        elim : ∀ {A : Set} → 0' → A
        elim ()

    [_] : ∀ {A} → ∅ ⊢ A → ⟦ A ⟧
    [_] = reify ∅


  -- defines a simple show function that can print proof terms in
  -- de Bruijn notation

  show : ∀ {A} {n} {Γ : Ctxt n} → Γ ⊢ A → String
  show (var i)      = showℕ (Fin.toℕ i)
  show (abs t)      = "λ " ⊕ (show t)
  show (app s t)    = "(" ⊕ show s ⊕ ") (" ⊕ show t ⊕")"
  show (pair s t)   = "⟨" ⊕ show s ⊕ " , " ⊕ show t ⊕ "⟩"
  show (fst t)      = "proj₁ (" ⊕ show t ⊕")"
  show (snd t)      = "proj₂ (" ⊕ show t ⊕")"
  show (inl t)      = "inj₁ (" ⊕ show t ⊕ ")"
  show (inr t)      = "inj₂ (" ⊕ show t ⊕ ")"
  show (case s t u) = "case " ⊕ show s ⊕ " of {" ⊕ show t ⊕ " ; " ⊕ show u ⊕ "}"
  show unit         = "*"
  show (empty t)    = "exfalso (" ⊕ show t ⊕ ")"


  -- defines a few simple example proofs and demonstraties their
  -- reification into agda

  module Example (⟦_⟧ᵁ : U → Set) where

    private
      open Reify ⟦_⟧ᵁ using (⟦_⟧; [_])

    identity : ∀ {A} → ∅ ⊢ A ⇒ A
    identity = abs (var zero)

    const : ∀ {A B} → ∅ ⊢ A ⇒ B ⇒ A
    const = abs (abs (weak (var zero)))

    swap : ∀ {A B} → ∅ ⊢ (A ∧ B) ⇒ (B ∧ A)
    swap = abs (pair (snd (var zero)) (fst (var zero)))

    IDENTITY : ∀ {A} → ⟦ A ⟧ → ⟦ A ⟧
    IDENTITY {A} = [ identity {A} ]
    -- > λ x → x

    CONST : ∀ {A B} → ⟦ A ⟧ → ⟦ B ⟧ → ⟦ A ⟧
    CONST {A} {B} = [ const {A} {B} ]
    -- > λ x y → x

    SWAP : ∀ {A B} → ⟦ A ⟧ × ⟦ B ⟧ → ⟦ B ⟧ × ⟦ A ⟧
    SWAP {A} {B} = [ swap {A} {B} ]
    -- > λ x → ( proj₂ x , proj₁ x )
