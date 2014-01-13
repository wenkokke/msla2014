open import Category.Applicative.Indexed as App
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product as Prod using (∃; _,_)
open import Data.String as Str using (String) renaming (_++_ to _⊕_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; _≢_; refl; sym; trans; cong)

module ClassicalLogic (U : Set) (R : U) where

  private
    open import Connectives U as Conn using (Type; el; _⇒_; _∧_; _∨_; ⊤; ⊥; ¬_)
    open import Context Type as Ctxt using (Ctxt; _,_; ∅; _++_)
    open import IntuitionisticLogic U as IL using (_⊢_; var; abs; app; pair; fst; snd; case; inl; inr; unit; empty; exch₀; exch₁; weak)

  infix 3 _⊢_∣_

  mutual
    data _⊢_∣_ : ∀ {m} (Γ : Ctxt m) (A : Type)  {n} (Δ : Ctxt n) → Set where


      var      : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 (x : Fin m) → Γ ⊢ Ctxt.lookup x Γ ∣ Δ
      lam-abs  : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 A , Γ ⊢ B ∣ Δ → Γ ⊢ A ⇒ B ∣ Δ
      lam-app  : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 Γ ⊢ A ⇒ B ∣ Δ → Γ ⊢ A ∣ Δ → Γ ⊢ B ∣ Δ
      mu-abs   : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 Γ ⊢ ⊥ ∣ A , Δ → Γ ⊢ A ∣ Δ
      mu-app   : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 (α : Fin n) → Γ ⊢ Ctxt.lookup α Δ ∣ Δ → Γ ⊢ ⊥ ∣ Δ
      pair     : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 Γ ⊢ A ∣ Δ → Γ ⊢ B ∣ Δ → Γ ⊢ A ∧ B ∣ Δ
      fst      : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 Γ ⊢ A ∧ B ∣ Δ → Γ ⊢ A ∣ Δ
      snd      : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 Γ ⊢ A ∧ B ∣ Δ → Γ ⊢ B ∣ Δ
      nu-abs  : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 Γ ⊢ B ∣ A , Δ → Γ ⊢ A ∨ B ∣ Δ
      nu-app   : ∀ {B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
                 (α : Fin n) → Γ ⊢ Ctxt.lookup α Δ ∨ B ∣ Δ → Γ ⊢ B ∣ Δ



  -- defines some explicit inference rule for exchange and weakening
  -- to show that as these are implicit in the above rules

  exchˡ : ∀ {A} {m} {Γ : Ctxt (suc m)} {n} {Δ : Ctxt n} (i : Fin m) →
          Γ ⊢ A ∣ Δ → Ctxt.exch i Γ ⊢ A ∣ Δ
  exchˡ {Γ = Γ} i (var x) with Ctxt.exch-var Γ i x
  ... | y , p rewrite p = var y
  exchˡ i (lam-abs t)   = lam-abs (exchˡ (suc i) t)
  exchˡ i (lam-app s t) = lam-app (exchˡ i s) (exchˡ i t)
  exchˡ i (mu-abs t)    = mu-abs (exchˡ i t)
  exchˡ i (mu-app α t)  = mu-app α (exchˡ i t)
  exchˡ i (pair s t)    = pair (exchˡ i s) (exchˡ i t)
  exchˡ i (fst t)       = fst (exchˡ i t)
  exchˡ i (snd t)       = snd (exchˡ i t)
  exchˡ i (nu-abs t)    = nu-abs (exchˡ i t)
  exchˡ i (nu-app α t)  = nu-app α (exchˡ i t)

  exchˡ₀ : ∀ {A B C} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
           A , B , Γ ⊢ C ∣ Δ  → B , A , Γ ⊢ C ∣ Δ
  exchˡ₀ = exchˡ zero

  exchˡ₁ : ∀ {A B C D} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
           A , B , C , Γ ⊢ D ∣ Δ  → A , C , B , Γ ⊢ D ∣ Δ
  exchˡ₁ = exchˡ (suc zero)

  weakˡ : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
          Γ ⊢ B ∣ Δ → A , Γ ⊢ B ∣ Δ
  weakˡ (var x)       = var (suc x)
  weakˡ (lam-abs t)   = lam-abs (exchˡ₀ (weakˡ t))
  weakˡ (lam-app s t) = lam-app (weakˡ s) (weakˡ t)
  weakˡ (mu-abs t)    = mu-abs (weakˡ t)
  weakˡ (mu-app α t)  = mu-app α (weakˡ t)
  weakˡ (pair s t)    = pair (weakˡ s) (weakˡ t)
  weakˡ (fst t)       = fst (weakˡ t)
  weakˡ (snd t)       = snd (weakˡ t)
  weakˡ (nu-abs t)    = nu-abs (weakˡ t)
  weakˡ (nu-app α t)  = nu-app α (weakˡ t)

  exchʳ : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt (suc n)} (i : Fin n) →
          Γ ⊢ A ∣ Δ → Γ ⊢ A ∣ Ctxt.exch i Δ
  exchʳ i (var x)       = var x
  exchʳ i (lam-abs t)   = lam-abs (exchʳ i t)
  exchʳ i (lam-app s t) = lam-app (exchʳ i s) (exchʳ i t)
  exchʳ i (mu-abs t)    = mu-abs (exchʳ (suc i) t)
  exchʳ {Δ = Δ} i (mu-app α t) with Ctxt.exch-var Δ i α
  ... | β , p rewrite p = mu-app β (exchʳ i t)
  exchʳ i (pair s t)    = pair (exchʳ i s) (exchʳ i t)
  exchʳ i (fst t)       = fst (exchʳ i t)
  exchʳ i (snd t)       = snd (exchʳ i t)
  exchʳ i (nu-abs t)    = nu-abs (exchʳ (suc i) t)
  exchʳ {Δ = Δ} i (nu-app α t) with Ctxt.exch-var Δ i α
  ... | β , p rewrite p = nu-app β (exchʳ i t)

  exchʳ₀ : ∀ {A B C} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
           Γ ⊢ A ∣ B , C , Δ → Γ ⊢ A ∣ C , B , Δ
  exchʳ₀ = exchʳ zero

  exchʳ₁ : ∀ {A B C D} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
           Γ ⊢ A ∣ B , C , D , Δ → Γ ⊢ A ∣ B , D , C , Δ
  exchʳ₁ = exchʳ (suc zero)

  weakʳ : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} →
          Γ ⊢ B ∣ Δ → Γ ⊢ B ∣ A , Δ
  weakʳ (var x)       = var x
  weakʳ (lam-abs t)   = lam-abs (weakʳ t)
  weakʳ (lam-app s t) = lam-app (weakʳ s) (weakʳ t)
  weakʳ (mu-abs t)    = mu-abs (exchʳ₀ (weakʳ t))
  weakʳ (mu-app α t)  = mu-app (suc α) (weakʳ t)
  weakʳ (pair s t)    = pair (weakʳ s) (weakʳ t)
  weakʳ (fst t)       = fst (weakʳ t)
  weakʳ (snd t)       = snd (weakʳ t)
  weakʳ (nu-abs t)    = nu-abs (exchʳ₀ (weakʳ t))
  weakʳ (nu-app α t)  = nu-app (suc α) (weakʳ t)



  -- defines a call-by-name cps transformation that reifies classical logic
  -- into intuitionistic logic

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

  cps : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ A ∣ Δ → Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C A
  cps {.(Ctxt.lookup x Γ)} {m} {Γ} {n} {Δ} (var x) = prf
    where
      open App.Morphism (Ctxt.lookup-morphism x) renaming (op-<$> to lookup-map)
      lem : C (Ctxt.lookup x Γ) ≡ Ctxt.lookup (Fin.inject+ n x) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      lem = trans (sym (lookup-map C Γ)) (sym (Ctxt.lookup-++-inject+ (Ctxt.map C Γ) (Ctxt.map K Δ) x))
      prf : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C (Ctxt.lookup x Γ)
      prf rewrite lem = var (Fin.inject+ n x)
  cps (lam-abs t) = abs (IL.∧-elim-left (app (exch₀ (weak (cps t))) (var (suc zero))))
  cps (lam-app s t) = abs (app (weak (cps s)) (pair (weak (cps t)) (var zero)))
  cps {Γ = Γ} (mu-abs t) = abs (IL.⊤-elim (IL.⇒-intro (IL.move-left (Ctxt.map C Γ) (cps t))))
  cps {.⊥} {m} {Γ} {n} {Δ} (mu-app α t) = prf
    where
      open App.Morphism (Ctxt.lookup-morphism α) renaming (op-<$> to lookup-map)
      lem : K (Ctxt.lookup α Δ) ≡ Ctxt.lookup (Fin.raise m α) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      lem = trans (sym (lookup-map K Δ)) (Ctxt.lookup-++-raise (Ctxt.map C Γ) (Ctxt.map K Δ) α)
      lkp : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ K (Ctxt.lookup α Δ)
      lkp rewrite lem = var (Fin.raise m α)
      prf : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ ⊤ ⇒ el R
      prf = abs (weak (app (cps t) lkp))
  cps (pair s t) = abs (case (var zero) (app (weak (weak (cps s))) (var zero)) (app (weak (weak (cps t))) (var zero)))
  cps (fst t) = abs (app (weak (cps t)) (inl (var zero)))
  cps (snd t) = abs (app (weak (cps t)) (inr (var zero)))
  cps {Γ = Γ} (nu-abs {A} {B} t) = abs (IL.∧-elim-left (exch₀ (IL.⇒-intro (IL.move-left (Ctxt.map C Γ) (cps t)))))
  cps {._} {m} {Γ} {n} {Δ} (nu-app {B} α t) = prf
    where
      open App.Morphism (Ctxt.lookup-morphism α) renaming (op-<$> to lookup-map)
      lem : K (Ctxt.lookup α Δ) ≡ Ctxt.lookup (Fin.raise m α) (Ctxt.map C Γ ++ Ctxt.map K Δ)
      lem = trans (sym (lookup-map K Δ)) (Ctxt.lookup-++-raise (Ctxt.map C Γ) (Ctxt.map K Δ) α)
      lkp : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ K (Ctxt.lookup α Δ)
      lkp rewrite lem = var (Fin.raise m α)
      prf : Ctxt.map C Γ ++ Ctxt.map K Δ ⊢ C B
      prf = abs (app (weak (cps t)) (pair (weak lkp) (var zero)))


  -- defines a reification of classical logic into agda in two ways: through the
  -- cps transformation above (and then via the reification for intuitionistic logic)
  -- and directly (also performing a cps transformation)

  module Reify (⟦_⟧ᵁ : U → Set) where

    private
      open IL.Reify ⟦_⟧ᵁ using (⟦_⟧) renaming ([_] to IL[_])

    [_] : ∀ {A} → ∅ ⊢ A ∣ ∅ → ⟦ C A ⟧
    [_] t = IL[ cps t ]



  -- defines a simple show function that can print proof terms in
  -- an extended version of the de Bruijn notation

  show : ∀ {A} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ A ∣ Δ → String
  show (var x)        = showℕ (Fin.toℕ x)
  show (lam-abs t)    = "λ " ⊕ show t
  show (lam-app s t)  = "(" ⊕ show s ⊕ ") (" ⊕ show t ⊕  ")"
  show (mu-abs t)     = "μ " ⊕ show t
  show (mu-app α t)   = "[" ⊕ showℕ (Fin.toℕ α) ⊕ "](" ⊕ show t ⊕ ")"
  show (pair s t)     = "⟨" ⊕ show s ⊕ " , " ⊕ show t ⊕ "⟩"
  show (fst t)        = "proj₁ (" ⊕ show t ⊕ ")"
  show (snd t)        = "proj₂ (" ⊕ show t ⊕ ")"
  show (nu-abs t)     = "ν " ⊕ show t
  show (nu-app α t)   = "⟨" ⊕ showℕ (Fin.toℕ α) ⊕ "⟩(" ⊕ show t ⊕ ")"



  -- defines some rules taken from classical natural deduction and
  -- classical sequent calculus (LK) that I found particularily useful

  ⇒-intro : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ A ⇒ B ∣ Δ → A , Γ ⊢ B ∣ Δ
  ⇒-intro t = lam-app (weakˡ t) (var zero)

  ∧-intro : ∀ {A B C} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ A ∧ B ∣ Δ → A , B , Γ ⊢ C ∣ Δ → Γ ⊢ C ∣ Δ
  ∧-intro s t = lam-app (lam-app (lam-abs (lam-abs t)) (snd s)) (fst s)

  ∧-elim : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ A ∣ Δ → Γ ⊢ B ∣ Δ → Γ ⊢ A ∧ B ∣ Δ
  ∧-elim = pair

  ∧-intro-left : ∀ {A B C} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A ∧ B , Γ ⊢ C ∣ Δ → A , B , Γ ⊢ C ∣ Δ
  ∧-intro-left t = lam-app (lam-abs (exchˡ₀ (weakˡ (exchˡ₀ (weakˡ t))))) (pair (var zero) (var (suc zero)))

  ∧-elim-left : ∀ {A B C} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A , B , Γ ⊢ C ∣ Δ → A ∧ B , Γ ⊢ C ∣ Δ
  ∧-elim-left t = ∧-intro (var zero) (exchˡ₁ (exchˡ₀ (weakˡ t)))

  ¬¬-elim : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A , Γ ⊢ B ∣ Δ → ¬ ¬ A , Γ ⊢ B ∣ Δ
  ¬¬-elim t = mu-abs (lam-app (var zero) (lam-abs (mu-app zero (exchˡ₀ (weakˡ (weakʳ t))))))

  ¬-right : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A , Γ ⊢ B ∣ Δ → Γ ⊢ B ∣ ¬ A , Δ
  ¬-right t = mu-abs (mu-app (suc zero) (lam-abs (mu-app zero (weakʳ (weakʳ t)))))

  ¬-left : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → Γ ⊢ B ∣ A , Δ → ¬ A , Γ ⊢ B ∣ Δ
  ¬-left t = mu-abs (lam-app (var zero) (mu-abs (mu-app (suc zero) (weakˡ (exchʳ₀ (weakʳ t))))))



  -- defines the notion of mutual derivability (i.e. double-line inference rules)
  -- and shows that using the rules defined above for classical logic the operators
  -- ∧, ∨, ⊤, ⊥ and ¬ form a boolean algebra

  record _⊣⊢_ (A : Type) (B : Type) : Set where
    field
      to   : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A , Γ ⊢ B ∣ Δ
      from : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → B , Γ ⊢ A ∣ Δ

  open _⊣⊢_ using (to; from)

  ∧-comm : ∀ {A B} → A ∧ B ⊣⊢ B ∧ A
  ∧-comm = record { to = iso ; from = iso }
    where
      iso : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A ∧ B , Γ ⊢ B ∧ A ∣ Δ
      iso = pair (snd (var zero)) (fst (var zero))

  ∧-assoc : ∀ {A B C} → A ∧ (B ∧ C) ⊣⊢ (A ∧ B) ∧ C
  ∧-assoc {A} {B} {C} = record { to = to' ; from = from' }
    where
      to'   : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A ∧ (B ∧ C) , Γ ⊢ (A ∧ B) ∧ C ∣ Δ
      to'   = ∧-elim-left (exchˡ₀ (∧-elim-left (exchˡ₁ (exchˡ₀ (∧-intro-left (∧-intro-left (var zero)))))))
      from' : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → (A ∧ B) ∧ C , Γ ⊢ A ∧ (B ∧ C) ∣ Δ
      from' = ∧-elim-left (∧-elim-left (exchˡ₀ (exchˡ₁ (∧-intro-left (exchˡ₀ (∧-intro-left (var zero)))))))

  ∧-absorb : ∀ {A B} → A ∧ (A ∨ B) ⊣⊢ A
  ∧-absorb {A} {B} = record { to = to' ; from = from' }
    where
      to'   : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A ∧ A ∨ B , Γ ⊢ A ∣ Δ
      to'   = ∧-elim-left (var zero)
      from' : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A , Γ ⊢ A ∧ A ∨ B ∣ Δ
      from' = pair (var zero) (nu-abs (mu-abs (mu-app (suc zero) (var zero))))

  ∧-identity : ∀ {A} → A ∧ ⊤ ⊣⊢ A
  ∧-identity = {!!}

  ∨-comm : ∀ {A B} → A ∨ B ⊣⊢ B ∨ A
  ∨-comm = record { to = iso ; from = iso }
    where
      iso : ∀ {A B} {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A ∨ B , Γ ⊢ B ∨ A ∣ Δ
      iso = nu-abs (mu-abs (mu-app (suc zero) (nu-app zero (var zero))))

  ∨-assoc : ∀ {A B C} → A ∨ (B ∨ C) ⊣⊢ (A ∨ B) ∨ C
  ∨-assoc {A} {B} {C} = record { to = to' ; from = from' }
    where
      to'   : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A ∨ (B ∨ C) , Γ ⊢ (A ∨ B) ∨ C ∣ Δ
      to'   = nu-abs (mu-abs (mu-app (suc zero) (nu-abs (mu-abs (mu-app (suc (suc zero)) (nu-app zero (nu-app (suc zero) (var zero))))))))
      from' : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → (A ∨ B) ∨ C , Γ ⊢ A ∨ (B ∨ C) ∣ Δ
      from' = nu-abs (nu-abs (mu-abs (mu-app (suc zero) (nu-app (suc (suc zero)) (mu-abs (mu-app (suc zero) (nu-app zero (var zero))))))))

  ∨-absorb : ∀ {A B} → A ∨ (A ∧ B) ⊣⊢ A
  ∨-absorb {A} {B} = record { to = to' ; from = from' }
    where
      to'   : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A ∨ (A ∧ B) , Γ ⊢ A ∣ Δ
      to'   = {!!}
      from' : ∀ {m} {Γ : Ctxt m} {n} {Δ : Ctxt n} → A , Γ ⊢ A ∨ (A ∧ B) ∣ Δ
      from' = nu-abs (mu-abs (mu-app (suc zero) (var zero)))

  ∨-identity : ∀ {A} → A ∨ ⊥ ⊣⊢ A
  ∨-identity = {!!}
