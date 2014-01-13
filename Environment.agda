open import Function using (id; _$_; _∘_)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Fin.Props as FinProps using () renaming (_≟_ to _≟-Fin_)
open import Data.Product using (∃; _×_; _,_; map; proj₁; proj₂)

module Environment (Type : Set) (⟦_⟧ : Type → Set) where

private
  open import Context Type as Ctxt using (Ctxt; _,_; ∅; _++_)

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
