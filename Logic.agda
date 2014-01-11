open import Function using (id; const; _$_; _∘_)
open import Category.Applicative.Indexed
open import Category.Monad
open import Data.Nat as Nat using (ℕ; suc; zero; pred; _≤_; z≤n; s≤s) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties as NatProps using ()
open import Data.Fin as Fin using (Fin; suc; zero; #_)
open import Data.Fin.Props as FinProps using () renaming (_≟_ to _≟-Fin_)
open import Data.Unit using (tt) renaming (⊤ to 1')
open import Data.Empty using () renaming (⊥ to 0'; ⊥-elim to exfalso)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product using (∃; _×_; _,_; map; proj₁; proj₂)
open import Data.Sum using ([_,_]) renaming (_⊎_ to _+_; inj₁ to inl; inj₂ to inr)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; False; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; cong)



module Logic (U : Set) (⟦_⟧ᵁ : U → Set) (_≟-U_ : (x y : U) → Dec (x ≡ y)) where

private
  open RawMonad {{...}}
  MaybeMonad = Maybe.monad

thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
thin  zero    y      = suc y
thin (suc x)  zero   = zero
thin (suc x) (suc y) = suc (thin x y)

thick : {n : ℕ} → (x y : Fin (suc n)) → Maybe (Fin n)
thick          zero    zero   = nothing
thick          zero   (suc y) = just y
thick {zero}  (suc ()) _
thick {suc n} (suc x)  zero   = just zero
thick {suc n} (suc x) (suc y) = suc <$> thick x y

thick′ : {n : ℕ} (x y : Fin (suc n)) → x ≢ y → Fin n
thick′          zero    zero   p = exfalso (p refl)
thick′          zero   (suc y) _ = y
thick′ {zero}  (suc ()) _      _
thick′ {suc _} (suc _)  zero   _ = zero
thick′ {suc _} (suc x) (suc y) p = suc (thick′ x y (p ∘ cong suc))

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
    open import Data.Vec as Vec public renaming (_∷_ to _,_; [] to ∅)
    open import Data.Vec.Properties public
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
    import Data.Vec.Equality
    open module VecEq = Data.Vec.Equality.Equality (PropEq.setoid Type)
      using (_≈_; []-cong; _∷-cong_)

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

  lam-elim : ∀ {n} {Γ : Ctxt n} {A B} → Γ ⊢ A ⇒ B → A , Γ ⊢ B
  lam-elim t = app (weak t) (var zero)

  pair-elim : ∀ {n} {Γ : Ctxt n} {A B C} → Γ ⊢ A ∧ B → Γ ⊢ A ⇒ B ⇒ C → Γ ⊢ C
  pair-elim s t = app (app t (fst s)) (snd s)

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

  fromℕ : ∀ m n → Fin (m +ℕ suc n)
  fromℕ  zero   n = zero
  fromℕ (suc m) n = suc (fromℕ m n)

  lookup-cong : ∀ {m} {Γ : Ctxt m} {A} B {i} → Ctxt.lookup i Γ ≡ A → Ctxt.lookup (suc i) (B , Γ) ≡ A
  lookup-cong B p = p

  lookup-fromℕ : ∀ m (Γ : Ctxt m) n (Δ : Ctxt n) A → Ctxt.lookup (fromℕ m n) (Γ ++ (A , Δ)) ≡ A
  lookup-fromℕ 0 ∅ n Δ A = refl
  lookup-fromℕ (suc m) (B , Γ) n Δ A = lookup-fromℕ m Γ n Δ A

  {-# NO_TERMINATION_CHECK #-}
  mutual
    move-to-middle : ∀ m (Γ : Ctxt m) n (Δ : Ctxt n) A B → A , Γ ++ Δ ⊢ B → Γ ++ (A , Δ) ⊢ B
    move-to-middle .0 ∅ n Δ A .(Ctxt.lookup i (A , Δ)) (var i) = var i
    move-to-middle .(suc m) (_,_ {m} B Γ) n Δ A .A (var zero) = weak prf₂
      where
        prf₁ : Γ ++ A , Δ ⊢ Ctxt.lookup (fromℕ m n) (Γ ++ (A , Δ))
        prf₁ = var (fromℕ m n)
        lem₁ : A ≡ Ctxt.lookup (fromℕ m n) (Γ ++ (A , Δ))
        lem₁ = sym (lookup-fromℕ m Γ n Δ A)
        lem₂ : (Γ ++ A , Δ ⊢ Ctxt.lookup (fromℕ m n) (Γ ++ (A , Δ))) ≡ (Γ ++ A , Δ ⊢ A)
        lem₂ rewrite sym lem₁ = refl
        prf₂ : Γ ++ A , Δ ⊢ A
        prf₂ rewrite sym lem₂ = prf₁
    move-to-middle .(suc n) (_,_ {n} B Γ) n₁ Δ A .B (var (suc zero)) = var zero
    move-to-middle .(suc n) (_,_ {n} B Γ) n₁ Δ A .(Context.lookup i (Γ ++ Δ)) (var (suc (suc i))) = weak {!!}
    move-to-middle m Γ n Δ A .(B ⇒ C) (lam {.(A , Γ ++ Δ)} {B} {C} t) = lam {!!}
  move-to-middle m Γ n Δ A B (app s t) = {!!}
    move-to-middle m Γ n Δ A .(B ∧ C) (pair {.(A , Γ ++ Δ)} {B} {C} s t) = {!!}
    move-to-middle m Γ n Δ A B (fst t) = {!!}
    move-to-middle m Γ n Δ A B (snd t) = {!!}
    move-to-middle m Γ n Δ A .(B ∨ C) (inl {.(A , Γ ++ Δ)} {B} {C} t) = {!!}
    move-to-middle m Γ n Δ A .(B ∨ C) (inr {.(A , Γ ++ Δ)} {B} {C} t) = {!!}
    move-to-middle m Γ n Δ A B (case s t u) = {!!}
    move-to-middle m Γ n Δ A .⊤ unit = {!!}
    move-to-middle m Γ n Δ A B (empty t) = {!!}

  [_] : ∀ {A} → ∅ ⊢ A → ⟦ A ⟧
  [_] = reify ∅
    where
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


module CL (R : U) where

  private
    open module Ctxt = Context Type using (Ctxt; _,_; ∅; _++_)
    open IL

  infix 3 _⊢_↝_ _⊢_↝′_

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
      mu-app  : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                Γ ⊢ Δ ↝′ A → Γ ⊢ Δ ↝ A → Γ ⊢ A , Δ ↝ ⊥

    data _⊢_↝′_ : ∀ {m} (Γ : Ctxt m) {n} (Δ : Ctxt n) (A : Type) → Set where

      covar   : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                (α : Fin n) → Γ ⊢ Δ ↝′ Ctxt.lookup α Δ

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

  reify : ∀ A m (Γ : Ctxt m) n (Δ : Ctxt n) → Γ ⊢ Δ ↝ A → Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C A
  reify .(Context.lookup x Γ) m Γ n Δ (var x) = prf₂
    where
      open Morphism (Ctxt.lookup-morphism x) renaming (op-<$> to lookup-map)
      lem₁ : C (Ctxt.lookup x Γ) ≡ Ctxt.lookup x (Ctxt.map C Γ)
      lem₁ rewrite lookup-map C Γ = refl
      lem₂ : Ctxt.lookup x (Ctxt.map C Γ) ≡ Ctxt.lookup (Fin.inject+ n x) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      lem₂ = sym (Ctxt.lookup-++-inject+ (Ctxt.map C Γ) (Ctxt.map K Δ) x)
      prf₁ : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ Ctxt.lookup (Fin.inject+ n x) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      prf₁ = var (Fin.inject+ n x)
      prf₂ : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C (Ctxt.lookup x Γ)
      prf₂ rewrite lem₁ | lem₂ = prf₁
  reify .(A ⇒ B) m Γ n Δ (lam-abs {A} {B} t) = prf₂
    where
      prf₁ : C A , K B , Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C B
      prf₁ = exch zero (weak (reify _ _ _ _ _ t))
      prf₂ : (Ctxt.map C Γ ++ Ctxt.map K Δ) ⊢ C A ∧ K B ⇒ el R
      prf₂ = lam (pair-intro-left (app prf₁ (var (suc zero))))
  reify B m Γ n Δ (lam-app s t) = prf
    where
      prf : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C B
      prf = lam (app (weak (reify _ _ _ _ _ s)) (pair (weak (reify _ _ _ _ _ t)) (var zero)))
  reify A m Γ n Δ (mu-abs t) = lam prf₂
    where
      prf₁ : K A , Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ ⊤ ⇒ el R
      prf₁ = bring-to-front (Ctxt.map C Γ) (reify _ _ _ _ _ t)
      prf₂ : K A , Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ el R
      prf₂ = unit-elim (lam-elim prf₁)
  reify .⊥ m Γ .(suc n) .(Ctxt.lookup α Δ , Δ) (mu-app {.(Ctxt.lookup α Δ)} {.m} {.Γ} {n} {Δ} (covar α) t) = prf₂
    where
      prf₁ : Ctxt.map C Γ ++  Ctxt.map K Δ ⊢ K (Context.lookup α Δ) ⇒ el R
      prf₁ = reify _ _ _ _ _ t
      prf₂ : Ctxt.map C Γ ++ K (Ctxt.lookup α Δ) , Ctxt.map K Δ ⊢ ⊤ ⇒ el R
      prf₂ = {!!} -- lam (weak (move-to-middle (Ctxt.map C Γ) (lam-elim prf₁)))
