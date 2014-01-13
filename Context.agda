open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Vec.Properties as VecProps using ()
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module Context (Type : Set) where

  open Vec public renaming (_∷_ to _,_; [] to ∅)
  open VecProps public

  Ctxt = Vec.Vec Type

  exch : ∀ {n} (i : Fin n) → Ctxt (suc n) → Ctxt (suc n)
  exch  zero    (A , B , Γ)  = B , (A , Γ)
  exch (suc i)  (A , Γ)      = A , (exch i Γ)

  exch-var : ∀ {n} (Γ : Ctxt (suc n)) i x → ∃ λ y → lookup x Γ ≡ lookup y (exch i Γ)
  exch-var (A , B , Γ) zero zero = suc zero , refl
  exch-var (A , B , Γ) zero (suc zero) = zero , refl
  exch-var (A , B , Γ) zero (suc (suc x)) = suc (suc x) , refl
  exch-var (A , Γ) (suc i) zero = zero , refl
  exch-var (A , Γ) (suc i) (suc x) with exch-var Γ i x
  ... | y , p = suc y , p

  cont-var : ∀ {n} {Γ : Ctxt n} {A} x → ∃ λ y → lookup x (A , A , Γ) ≡ lookup y (A , Γ)
  cont-var zero = zero , refl
  cont-var (suc zero) = zero , refl
  cont-var (suc (suc x)) = suc x , refl

  exch-inv : ∀ {n} Γ → (i : Fin n) → exch i (exch i Γ) ≡ Γ
  exch-inv {._} (x , y , Γ)  (zero {γ})    = refl
  exch-inv {._} (x , Γ)      (suc  {γ} i)  = cong (λ Γ → x , Γ) (exch-inv Γ i)

  lookup-++-raise : ∀ {a} {A : Set a} {m n} (xs : Vec A m) (ys : Vec A n) i →
                    lookup i ys ≡ lookup (Fin.raise m i) (xs ++ ys)
  lookup-++-raise {m = zero}  []       ys i = refl
  lookup-++-raise {m = suc m} (x ∷ xs) ys i = lookup-++-raise {m = m} xs ys i

  move-left : ∀ {a} {A : Set a} {m n} (xs : Vec A m) y (ys : Vec A n) i →
              ∃ λ j → lookup i (xs ++ y ∷ ys) ≡ lookup j (y ∷ xs ++ ys)
  move-left [] y ys i = i , refl
  move-left (x , xs) y ys zero = suc zero , refl
  move-left (x , xs) y ys (suc i) with move-left xs y ys i
  move-left (x , xs) y ys (suc i) | zero  , p = zero , p
  move-left (x , xs) y ys (suc i) | suc j , p = suc (suc j) , p
