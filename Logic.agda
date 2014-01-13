open import Function using (id; _$_; _∘_)
open import Category.Applicative.Indexed
open import Category.Monad
open import Data.String renaming (_++_ to _⊕_)
open import Data.Nat as Nat using (ℕ; suc; zero; pred; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties as NatProps using ()
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Fin as Fin using (Fin; suc; zero; #_)
open import Data.Fin.Props as FinProps using () renaming (_≟_ to _≟-Fin_)
open import Data.Unit using (tt) renaming (⊤ to 1')
open import Data.Empty using () renaming (⊥ to 0'; ⊥-elim to exfalso)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _×_; _,_; map; proj₁; proj₂)
open import Data.Sum using ([_,_]) renaming (_⊎_ to _+_; inj₁ to inl; inj₂ to inr)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; trans; cong)



module Logic (U : Set) (⟦_⟧ᵁ : U → Set) (_≟-U_ : (x y : U) → Dec (x ≡ y)) (showU : U → String) where

private
  open RawMonad {{...}}
  MaybeMonad = Maybe.monad

infixr 20 _⇒_
infixr 30 _∧_ _∨_

data Type : Set where
  el   : (A : U) → Type
  _⇒_ : Type → Type → Type
  _∧_  : Type → Type → Type
  _∨_  : Type → Type → Type
  ⊤    : Type
  ⊥    : Type

¬_ : Type → Type
¬_ A = A ⇒ ⊥

⟦_⟧ : Type → Set
⟦ el A ⟧ = ⟦ A ⟧ᵁ
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ A ∧ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ∨ B ⟧ = ⟦ A ⟧ + ⟦ B ⟧
⟦ ⊤ ⟧ = 1'
⟦ ⊥ ⟧ = 0'

el-inj : ∀ {A B} → el A ≡ el B → A ≡ B
el-inj refl = refl

arr-injl : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → A ≡ C
arr-injl refl = refl

arr-injr : ∀ {A B C D} → A ⇒ B ≡ C ⇒ D → B ≡ D
arr-injr refl = refl

conj-injl : ∀ {A B C D} → A ∧ B ≡ C ∧ D → A ≡ C
conj-injl refl = refl

conj-injr : ∀ {A B C D} → A ∧ B ≡ C ∧ D → B ≡ D
conj-injr refl = refl

disj-injl : ∀ {A B C D} → A ∨ B ≡ C ∨ D → A ≡ C
disj-injl refl = refl

disj-injr : ∀ {A B C D} → A ∨ B ≡ C ∨ D → B ≡ D
disj-injr refl = refl

_≟ᵀ_ : (x y : Type) → Dec (x ≡ y)
el A ≟ᵀ el  B with A ≟-U B
el A ≟ᵀ el .A | yes refl = yes refl
el A ≟ᵀ el  B | no  A≢B  = no (A≢B ∘ el-inj)
el _ ≟ᵀ (_ ⇒ _) = no (λ ())
el _ ≟ᵀ _ ∧ _ = no (λ ())
el _ ≟ᵀ _ ∨ _ = no (λ ())
el _ ≟ᵀ ⊤ = no (λ ())
el _ ≟ᵀ ⊥ = no (λ ())
(_ ⇒ _) ≟ᵀ el _ = no (λ ())
(x ⇒ y) ≟ᵀ (x′ ⇒ y′) with x ≟ᵀ x′
(x ⇒ y) ≟ᵀ (x′ ⇒ y′) | no x≢x′ = no (x≢x′ ∘ arr-injl)
(x ⇒ y) ≟ᵀ (.x ⇒ y′) | yes refl with y ≟ᵀ y′
(x ⇒ y) ≟ᵀ (.x ⇒ y′) | yes refl | no y≢y′ = no (y≢y′ ∘ arr-injr)
(x ⇒ y) ≟ᵀ (.x ⇒ .y) | yes refl | yes refl = yes refl
(_ ⇒ _) ≟ᵀ _ ∧ _ = no (λ ())
(_ ⇒ _) ≟ᵀ _ ∨ _ = no (λ ())
(_ ⇒ _) ≟ᵀ ⊤ = no (λ ())
(_ ⇒ _) ≟ᵀ ⊥ = no (λ ())
_ ∧ _ ≟ᵀ el _ = no (λ ())
_ ∧ _ ≟ᵀ (_ ⇒ _) = no (λ ())
x ∧ y ≟ᵀ x′ ∧ y′ with x ≟ᵀ x′
(x ∧ y) ≟ᵀ (x′ ∧ y′) | no x≢x′ = no (x≢x′ ∘ conj-injl)
(x ∧ y) ≟ᵀ (.x ∧ y′) | yes refl with y ≟ᵀ y′
(x ∧ y) ≟ᵀ (.x ∧ y′) | yes refl | no y≢y′ = no (y≢y′ ∘ conj-injr)
(x ∧ y) ≟ᵀ (.x ∧ .y) | yes refl | yes refl = yes refl
_ ∧ _ ≟ᵀ _ ∨ _ = no (λ ())
_ ∧ _ ≟ᵀ ⊤ = no (λ ())
_ ∧ _ ≟ᵀ ⊥ = no (λ ())
_ ∨ _ ≟ᵀ el _ = no (λ ())
_ ∨ _ ≟ᵀ (_ ⇒ _) = no (λ ())
_ ∨ _ ≟ᵀ _ ∧ _ = no (λ ())
x ∨ y ≟ᵀ x′ ∨ y′ with x ≟ᵀ x′
(x ∨ y) ≟ᵀ (x′ ∨ y′) | no x≢x′ = no (x≢x′ ∘ disj-injl)
(x ∨ y) ≟ᵀ (.x ∨ y′) | yes refl with y ≟ᵀ y′
(x ∨ y) ≟ᵀ (.x ∨ y′) | yes refl | no y≢y′ = no (y≢y′ ∘ disj-injr)
(x ∨ y) ≟ᵀ (.x ∨ .y) | yes refl | yes refl = yes refl
_ ∨ _ ≟ᵀ ⊤ = no (λ ())
_ ∨ _ ≟ᵀ ⊥ = no (λ ())
⊤ ≟ᵀ el _ = no (λ ())
⊤ ≟ᵀ (_ ⇒ _) = no (λ ())
⊤ ≟ᵀ _ ∧ _ = no (λ ())
⊤ ≟ᵀ _ ∨ _ = no (λ ())
⊤ ≟ᵀ ⊤ = yes refl
⊤ ≟ᵀ ⊥ = no (λ ())
⊥ ≟ᵀ el _ = no (λ ())
⊥ ≟ᵀ (_ ⇒ _) = no (λ ())
⊥ ≟ᵀ _ ∧ _ = no (λ ())
⊥ ≟ᵀ _ ∨ _ = no (λ ())
⊥ ≟ᵀ ⊤ = no (λ ())
⊥ ≟ᵀ ⊥ = yes refl



module Context (Type : Set) where

  private
    open import Data.Vec using (Vec; _∷_; [])
    open import Data.Vec as Vec public renaming (_∷_ to _,_; [] to ∅)
    open import Data.Vec.Properties public
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

  Ctxt = Vec.Vec Type

  exch : ∀ {n} (i : Fin n) → Ctxt (suc n) → Ctxt (suc n)
  exch  zero    (A , B , Γ)  = B , (A , Γ)
  exch (suc i)  (A , Γ)      = A , (exch i Γ)

  exch-inv : ∀ {n} Γ → (i : Fin n) → exch i (exch i Γ) ≡ Γ
  exch-inv {._} (x , y , Γ)  (zero {γ})    = refl
  exch-inv {._} (x , Γ)      (suc  {γ} i)  = cong (λ Γ → x , Γ) (exch-inv Γ i)

  delete : ∀ {n} (Γ : Ctxt (suc n)) (x : Fin (suc n)) → Ctxt n
  delete (_ , Γ) zero = Γ
  delete (A , ∅) (suc ())
  delete (A , B , Γ) (suc i) = A , delete (B , Γ) i

  lookup-++-raise : ∀ {a} {A : Set a} {m n} (xs : Vec A m) (ys : Vec A n) i → lookup i ys ≡ lookup (Fin.raise m i) (xs ++ ys)
  lookup-++-raise {m = zero}  []       ys i = refl
  lookup-++-raise {m = suc m} (x ∷ xs) ys i = lookup-++-raise {m = m} xs ys i



module Environment (Type : Set) (⟦_⟧ : Type → Set) where

  private
    open module Ctxt = Context Type using (Ctxt; _,_; ∅; _++_)

  data Env : ∀ {n} (Γ : Ctxt n) → Set₁ where
    ∅ : Env ∅
    _,_ : ∀ {A} {n} {Γ} → ⟦ A ⟧ → Env {n} Γ → Env (A , Γ)

  only : ∀ {A} {Γ : Ctxt 0} → Env (A , Γ) → ⟦ A ⟧
  only (x , ∅) = x

  split : ∀ {n₁} {Γ₁ : Ctxt n₁} {n₂} {Γ₂ : Ctxt n₂} → Env (Γ₁ ++ Γ₂) → Env Γ₁ × Env Γ₂
  split {._} {∅} env = ∅ , env
  split {._} {A , Γ} (x , env) = map (_,_ x) id (split env)

  exch : ∀ {n} {Γ} (i : Fin n) → Env (Ctxt.exch i Γ) → Env Γ
  exch {n} {Γ} i env = rewr (exch′ i env)
    where
      exch′ : ∀ {n} {Γ} (i : Fin n) → Env Γ → Env (Ctxt.exch i Γ)
      exch′  zero   (x , y , Γ) = y , x , Γ
      exch′ (suc i) (x , Γ)     = x , exch′ i Γ
      rewr : Env (Ctxt.exch i (Ctxt.exch i Γ)) → Env Γ
      rewr env rewrite Ctxt.exch-inv Γ i = env



module IL where

  private
    open module Ctxt = Context Type using (Ctxt; _,_; ∅; _++_; _∷ʳ_)

  infix 3 _⊢_

  data _⊢_ {n : ℕ} : (Γ : Ctxt n) (A : Type) → Set where
    var    : ∀ {Γ}
             i → Γ ⊢ (Ctxt.lookup i Γ)
    lam    : ∀ {Γ} {A B} →
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

  {-# NO_TERMINATION_CHECK #-}
  mutual
    exch : ∀ {n} {Γ : Ctxt (suc n)} {A} (i : Fin n) →
           Γ ⊢ A →  Ctxt.exch i Γ ⊢ A
    exch {Γ = A , B , Γ} zero (var zero) = var (suc zero)
    exch {Γ = A , B , Γ} zero (var (suc zero)) = var zero
    exch {Γ = A , B , Γ} zero (var (suc (suc j))) = var (suc (suc j))
    exch {Γ = A , Γ} (suc i) (var zero) = var zero
    exch {Γ = A , Γ} (suc i) (var (suc j)) = weak (exch i (var j))
    exch i (lam t)      = lam (exch (suc i) t)
    exch i (app s t)    = app (exch i s) (exch i t)
    exch i (pair s t)   = pair (exch i s) (exch i t)
    exch i (fst t)      = fst (exch i t)
    exch i (snd t)      = snd (exch i t)
    exch i (inl t)      = inl (exch i t)
    exch i (inr t)      = inr (exch i t)
    exch i (case s t u) = case (exch i s) (exch (suc i) t) (exch (suc i) u)
    exch i unit         = unit
    exch i (empty t)    = empty (exch i t)

    weak : ∀ {n} {Γ : Ctxt n} {A B} → Γ ⊢ B → A , Γ ⊢ B
    weak (var i)      = var (Fin.raise 1 i)
    weak (lam t)      = lam (exch zero (weak t))
    weak (app s t)    = app (weak s) (weak t)
    weak (pair s t)   = pair (weak s) (weak t)
    weak (fst t)      = fst (weak t)
    weak (snd t)      = snd (weak t)
    weak (inl t)      = inl (weak t)
    weak (inr t)      = inr (weak t)
    weak (case s t u) = case (weak s) (exch zero (weak t)) (exch zero (weak u))
    weak unit         = unit
    weak (empty t)    = empty (weak t)

  {-# NO_TERMINATION_CHECK #-}
  mutual
    cont : ∀ {n} {Γ : Ctxt n} {A B} → A , A , Γ ⊢ B → A , Γ ⊢ B
    cont (var zero)          = var zero
    cont (var (suc zero))    = var zero
    cont (var (suc (suc i))) = var (suc i)
    cont (lam t)             = lam (cont₁ t)
    cont (app s t)           = app (cont s) (cont t)
    cont (pair s t)          = pair (cont s) (cont t)
    cont (fst t)             = fst (cont t)
    cont (snd t)             = snd (cont t)
    cont (inl t)             = inl (cont t)
    cont (inr t)             = inr (cont t)
    cont (case s t u)        = case (cont s) (cont₁ t) (cont₁ u)
    cont unit                = unit
    cont (empty t)           = empty (cont t)

    cont₁ : ∀ {n} {Γ : Ctxt n} {A B C} → A , B , B , Γ ⊢ C → A , B , Γ ⊢ C
    cont₁ t = exch zero (cont (exch (suc zero) (exch zero t)))

  impl-elim : ∀ {n} {Γ : Ctxt n} {A B} → Γ ⊢ A ⇒ B → A , Γ ⊢ B
  impl-elim t = app (weak t) (var zero)

  pair-elim : ∀ {n} {Γ : Ctxt n} {A B C} → Γ ⊢ A ∧ B → Γ ⊢ A ⇒ B ⇒ C → Γ ⊢ C
  pair-elim s t = app (app t (fst s)) (snd s)

  pair-elim-left : ∀ {n} {Γ : Ctxt n} {A B C} → A ∧ B , Γ ⊢ C → A , B , Γ ⊢ C
  pair-elim-left t = app (weak (weak (lam t))) (pair (var zero) (var (suc zero)))

  pair-intro-left : ∀ {n} {Γ : Ctxt n} {A B C} → A , B , Γ ⊢ C → A ∧ B , Γ ⊢ C
  pair-intro-left t = pair-elim (pair (fst (var zero)) (snd (var zero))) (weak (lam (lam (exch zero t))))

  unit-elim : ∀ {n} {Γ : Ctxt n} {A} → ⊤ , Γ ⊢ A → Γ ⊢ A
  unit-elim t = app (lam t) unit

  {-# NO_TERMINATION_CHECK #-}
  mutual
    bring-to-front : ∀ {m} (Γ : Ctxt m) {n} {Δ : Ctxt n} {A B} → Γ ++ (A , Δ) ⊢ B → A , Γ ++ Δ ⊢ B
    bring-to-front ∅ (var i)             = var i
    bring-to-front (_ , Γ) (var zero)    = var (suc zero)
    bring-to-front (_ , Γ) (var (suc i)) = exch zero (weak (bring-to-front Γ (var i)))
    bring-to-front Γ (lam {A = C} t)     = lam (bring-to-front₁ Γ C t)
    bring-to-front Γ (app s t)           = app (bring-to-front Γ s) (bring-to-front Γ t)
    bring-to-front Γ (pair s t)          = pair (bring-to-front Γ s) (bring-to-front Γ t)
    bring-to-front Γ (fst t)             = fst (bring-to-front Γ t)
    bring-to-front Γ (snd t)             = snd (bring-to-front Γ t)
    bring-to-front Γ (inl t)             = inl (bring-to-front Γ t)
    bring-to-front Γ (inr t)             = inr (bring-to-front Γ t)
    bring-to-front Γ (case {A = C} {B = D} s t u) = case (bring-to-front Γ s) (bring-to-front₁ Γ C t) (bring-to-front₁ Γ D u)
    bring-to-front Γ unit                = unit
    bring-to-front Γ (empty t)           = empty (bring-to-front Γ t)

    bring-to-front₁ : ∀ {m} (Γ : Ctxt m) {n} {Δ : Ctxt n} A {B C} → A , Γ ++ (B , Δ) ⊢ C → A , B , Γ ++ Δ ⊢ C
    bring-to-front₁ Γ A t = exch zero (bring-to-front (A , Γ) t)



  open module Env = Environment Type ⟦_⟧ hiding (exch)

  reify : ∀ {n} {Γ : Ctxt n} {A} → Env Γ → Γ ⊢ A → ⟦ A ⟧
  reify ∅ (var ())
  reify (x , Γ) (var zero) = x
  reify (x , Γ) (var (suc i)) = reify Γ (var i)
  reify Γ (lam p) = λ x → reify (x , Γ) p
  reify Γ (app p q) = (reify Γ p) (reify Γ q)
  reify Γ (pair p q) = (reify Γ p , reify Γ q)
  reify Γ (fst p) = proj₁ (reify Γ p)
  reify Γ (snd p) = proj₂ (reify Γ p)
  reify Γ (inl p) = inl (reify Γ p)
  reify Γ (inr p) = inr (reify Γ p)
  reify Γ (case p q r) = elim (reify Γ p) (λ x → reify (x , Γ) q) (λ y → reify (y , Γ) r)
    where
      elim : {A B C : Set} → A + B → (A → C) → (B → C) → C
      elim (inl x) f g = f x
      elim (inr y) f g = g y
  reify Γ unit = tt
  reify Γ (empty p) = elim (reify Γ p)
    where
      elim : ∀ {A : Set} → 0' → A
      elim ()

  [_] : ∀ {A} → ∅ ⊢ A → ⟦ A ⟧
  [_] = reify ∅

  show : ∀ {A} {n} {Γ : Ctxt n} → Γ ⊢ A → String
  show (var i)      = showℕ (Fin.toℕ i)
  show (lam t)      = "λ " ⊕ (show t)
  show (app s t)    = "(" ⊕ show s ⊕ ") (" ⊕ show t ⊕")"
  show (pair s t)   = "⟨" ⊕ show s ⊕ " , " ⊕ show t ⊕ "⟩"
  show (fst t)      = "proj₁ (" ⊕ show t ⊕")"
  show (snd t)      = "proj₂ (" ⊕ show t ⊕")"
  show (inl t)      = "inj₁ (" ⊕ show t ⊕ ")"
  show (inr t)      = "inj₂ (" ⊕ show t ⊕ ")"
  show (case s t u) = "case " ⊕ show s ⊕ " of {" ⊕ show t ⊕ " ; " ⊕ show u ⊕ "}"
  show unit         = "*"
  show (empty t)    = "exfalso (" ⊕ show t ⊕ ")"


  -- some examples

  identity : ∀ {A} → ∅ ⊢ A ⇒ A
  identity = lam (var zero)

  const : ∀ {A B} → ∅ ⊢ A ⇒ B ⇒ A
  const = lam (lam (weak (var zero)))


module CL (R : U) where

  private
    open module Ctxt = Context Type using (Ctxt; _,_; ∅; _++_)
    open IL using (_⊢_; var; lam; app; pair; fst; snd; inl; inr; case; unit; empty;
                        exch; weak; cont; pair-intro-left; impl-elim; unit-elim; bring-to-front)

  infix 3 _⊢_↝_

  mutual
    data _⊢_↝_ : ∀ {m} (Γ : Ctxt m) {n} (Δ : Ctxt n)  (A : Type) → Set where

      var     : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                (x : Fin m) → Γ ⊢ Δ ↝ Ctxt.lookup x Γ

      lam-abs : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                A , Γ ⊢ Δ ↝ B → Γ ⊢ Δ ↝ A ⇒ B

      lam-app : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                Γ ⊢ Δ ↝ A ⇒ B → Γ ⊢ Δ ↝ A → Γ ⊢ Δ ↝ B

      mu-abs  : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                Γ ⊢ A , Δ ↝ ⊥ → Γ ⊢ Δ ↝ A
      mu-app  : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                (α : Fin n) → Γ ⊢ Δ ↝ Ctxt.lookup α Δ → Γ ⊢ Δ ↝ ⊥

      pair    : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                Γ ⊢ Δ ↝ A → Γ ⊢ Δ ↝ B → Γ ⊢ Δ ↝ A ∧ B
      fst     : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                Γ ⊢ Δ ↝ A ∧ B → Γ ⊢ Δ ↝ A
      snd     : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                Γ ⊢ Δ ↝ A ∧ B → Γ ⊢ Δ ↝ B

      nu-abs  : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                Γ ⊢ A , Δ ↝ B → Γ ⊢ Δ ↝ A ∨ B
      nu-app  : ∀ {B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                (α : Fin n) → Γ ⊢ Δ ↝ B → Γ ⊢ Δ ↝ Ctxt.lookup α Δ ∨ B

  mutual
    K : Type → Type
    K (el A) = el A
    K ⊤ = ⊥
    K ⊥ = ⊤
    K (A ⇒ B) = C A ∧ K B
    K (A ∧ B) = K A ∨ K B
    K (A ∨ B) = K A ∧ K B

    C : Type → Type
    C A = K A ⇒ el R

  reify : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ Δ ↝ A → Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C A
  reify {.(Ctxt.lookup x Γ)} {m} {Γ} {n} {Δ} (var x) = prf
    where
      open Morphism (Ctxt.lookup-morphism x) renaming (op-<$> to lookup-map)
      lem : C (Ctxt.lookup x Γ) ≡ Ctxt.lookup (Fin.inject+ n x) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      lem = trans (sym (lookup-map C Γ)) (sym (Ctxt.lookup-++-inject+ (Ctxt.map C Γ) (Ctxt.map K Δ) x))
      prf : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C (Ctxt.lookup x Γ)
      prf rewrite lem = var (Fin.inject+ n x)
  reify (lam-abs t) = lam (pair-intro-left (app (exch zero (weak (reify t))) (var (suc zero))))
  reify (lam-app s t) = lam (app (weak (reify s)) (pair (weak (reify t)) (var zero)))
  reify {Γ = Γ} (mu-abs t) = lam (unit-elim (impl-elim (bring-to-front (Ctxt.map C Γ) (reify t))))
  reify {.⊥} {m} {Γ} {n} {Δ} (mu-app α t) = prf
    where
      open Morphism (Ctxt.lookup-morphism α) renaming (op-<$> to lookup-map)
      lem : K (Ctxt.lookup α Δ) ≡ Ctxt.lookup (Fin.raise m α) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      lem = trans (sym (lookup-map K Δ)) (Ctxt.lookup-++-raise (Ctxt.map C Γ) (Ctxt.map K Δ) α)
      lkp : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ K (Ctxt.lookup α Δ)
      lkp rewrite lem = var (Fin.raise m α)
      prf : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ ⊤ ⇒ el R
      prf = lam (weak (app (reify t) lkp))
  reify (pair s t) = lam (case (var zero) (app (weak (weak (reify s))) (var zero)) (app (weak (weak (reify t))) (var zero)))
  reify (fst t) = lam (app (weak (reify t)) (inl (var zero)))
  reify (snd t) = lam (app (weak (reify t)) (inr (var zero)))
  reify {Γ = Γ} (nu-abs {A} {B} t) = lam (pair-intro-left (exch zero (impl-elim (bring-to-front (Ctxt.map C Γ) (reify t)))))
  reify {._} {m} {Γ} {n} {Δ} (nu-app {B} α t) = prf
    where
      open Morphism (Ctxt.lookup-morphism α) renaming (op-<$> to lookup-map)
      lem : K (Ctxt.lookup α Δ) ≡ Ctxt.lookup (Fin.raise m α) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      lem = trans (sym (lookup-map K Δ)) (Ctxt.lookup-++-raise (Ctxt.map C Γ) (Ctxt.map K Δ) α)
      lkp : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ K (Ctxt.lookup α Δ)
      lkp rewrite lem = var (Fin.raise m α)
      prf : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ K (Ctxt.lookup α Δ) ∧ K B ⇒ el R
      prf = lam (pair-intro-left (weak (impl-elim (reify t))))



  [_] : ∀ {A} → ∅ ⊢ ∅ ↝ A → ⟦ C A ⟧
  [_] t = IL.[ reify t ]



  {-# NO_TERMINATION_CHECK #-}
  mutual
    exchl : ∀ {A} {m} {Γ : Ctxt (suc m)} {n} {Δ : Ctxt n} (i : Fin m) →
            Γ ⊢ Δ ↝ A → Ctxt.exch i Γ ⊢ Δ ↝ A
    exchl {Γ = A , B , Γ} zero (var zero) = var (suc zero)
    exchl {Γ = A , B , Γ} zero (var (suc zero)) = var zero
    exchl {Γ = A , B , Γ} zero (var (suc (suc x))) = var (suc (suc x))
    exchl {Γ = A , Γ} (suc i) (var zero) = var zero
    exchl {Γ = A , Γ} (suc i) (var (suc x)) = weakl (exchl i (var x))
    exchl i (lam-abs t)   = lam-abs (exchl (suc i) t)
    exchl i (lam-app s t) = lam-app (exchl i s) (exchl i t)
    exchl i (mu-abs t)    = mu-abs (exchl i t)
    exchl i (mu-app α t)  = mu-app α (exchl i t)
    exchl i (pair s t)    = pair (exchl i s) (exchl i t)
    exchl i (fst t)       = fst (exchl i t)
    exchl i (snd t)       = snd (exchl i t)
    exchl i (nu-abs t)    = nu-abs (exchl i t)
    exchl i (nu-app α t)  = nu-app α (exchl i t)

    weakl : ∀ {A B} {m} {Γ : Ctxt (suc m)} {n} {Δ : Ctxt n} →
            Γ ⊢ Δ ↝ B → A , Γ ⊢ Δ ↝ B
    weakl (var x)       = var (suc x)
    weakl (lam-abs t)   = lam-abs (exchl zero (weakl t))
    weakl (lam-app s t) = lam-app (weakl s) (weakl t)
    weakl (mu-abs t)    = mu-abs (weakl t)
    weakl (mu-app α t)  = mu-app α (weakl t)
    weakl (pair s t)    = pair (weakl s) (weakl t)
    weakl (fst t)       = fst (weakl t)
    weakl (snd t)       = snd (weakl t)
    weakl (nu-abs t)    = nu-abs (weakl t)
    weakl (nu-app α t)  = nu-app α (weakl t)

  mutual
    exchr : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt (suc n)} (i : Fin n) →
            Γ ⊢ Δ ↝ A → Γ ⊢ Ctxt.exch i Δ ↝ A
    exchr i (var x)       = var x
    exchr i (lam-abs t)   = lam-abs (exchr i t)
    exchr i (lam-app s t) = lam-app (exchr i s) (exchr i t)
    exchr i (mu-abs t)    = mu-abs (exchr (suc i) t)
    exchr i (mu-app α t)  = {!!}
    exchr i (pair s t)    = pair (exchr i s) (exchr i t)
    exchr i (fst t)       = fst (exchr i t)
    exchr i (snd t)       = snd (exchr i t)
    exchr i (nu-abs t)    = nu-abs (exchr (suc i) t)
    exchr i (nu-app α t)  = {!!}

    weakr : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt (suc n)} →
            Γ ⊢ Δ ↝ B → Γ ⊢ A , Δ ↝ B
    weakr (var x)        = var x
    weakr (lam-abs t)    = lam-abs (weakr t)
    weakr (lam-app s t)  = lam-app (weakr s) (weakr t)
    weakr (mu-abs t)     = mu-abs (exchr zero (weakr t))
    weakr (mu-app α t)   = mu-app (suc α) (weakr t)
    weakr (pair s t)     = pair (weakr s) (weakr t)
    weakr (fst t)        = fst (weakr t)
    weakr (snd t)        = snd (weakr t)
    weakr (nu-abs t)     = nu-abs (exchr zero (weakr t))
    weakr (nu-app α t)   = nu-app (suc α) (weakr t)



  show : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ Δ ↝ A → String
  show (var x)        = showℕ (Fin.toℕ x)
  show (lam-abs t)    = "λ " ⊕ show t
  show (lam-app s t)  = "(" ⊕ show s ⊕ ") (" ⊕ show t ⊕  ")"
  show (mu-abs t)     = "μ " ⊕ show t
  show (mu-app α t)   = "[" ⊕ showℕ (Fin.toℕ α) ⊕ "]" ⊕ show t
  show (pair s t)     = "⟨" ⊕ show s ⊕ " , " ⊕ show t ⊕ "⟩"
  show (fst t)        = "proj₁ (" ⊕ show t ⊕ ")"
  show (snd t)        = "proj₂ (" ⊕ show t ⊕ ")"
  show (nu-abs t)     = "ν " ⊕ show t
  show (nu-app α t)   = "⟨" ⊕ showℕ (Fin.toℕ α) ⊕ "⟩" ⊕ show t



  -- some examples


  identity : ∀ {A} → ∅ ⊢ ∅ ↝ (el A ⇒ el A)
  identity = lam-abs (var zero)

  swap : ∀ {A} {B} → ∅ ⊢ ∅ ↝ (A ∧ B ⇒ B ∧ A)
  swap = lam-abs (pair (snd (var zero)) (fst (var zero)))
