%include paper.fmt
%include LinearLogic.fmt

\hidden{
\begin{code}
open import Function using (case_of_)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)
\end{code}
}

\hidden{
\begin{code}
module LinearLogic (U : Set) (R : U) (⟦_⟧ᵁ : U → Set) where
\end{code}
}

\hidden{
\begin{code}
infixr 40 ¬_
infix  30 _⊗_
infixr 20 _⊸_
infix  4  _⊢_
\end{code}
}

\begin{code}
data Type : Set where
  el   : (A : U) → Type
  ⊥    : Type
  _⊗_  : Type → Type → Type
  _⊸_  : Type → Type → Type
\end{code}

\begin{code}
¬_ : Type → Type
¬ A = A ⊸ ⊥
\end{code}

%<*ill>
\begin{code}
data _⊢_ : ∀ (Γ : List Type) (A : Type) → Set where
  var   : ∀ {A} → A , ∅ ⊢ A
  abs   : ∀ {A B Γ} → A , Γ ⊢ B → Γ ⊢ A ⊸ B
  app   : ∀ {A B Γ Δ} → Γ ⊢ A ⊸ B → Δ ⊢ A → Γ ++ Δ ⊢ B
  pair  : ∀ {A B Γ Δ} → Γ ⊢ A → Δ ⊢ B → Γ ++ Δ ⊢ A ⊗ B
  case  : ∀ {A B C Γ Δ} → Γ ⊢ A ⊗ B → A , B , Δ ⊢ C → Γ ++ Δ ⊢ C
  exch  : ∀ {Γ Δ Σ Π A} →  (Γ ++ Σ) ++ (Δ ++ Π) ⊢ A
        →  (Γ ++ Δ) ++ (Σ ++ Π) ⊢ A
\end{code}
%</ill>

\hidden{
\begin{code}
exch₀ : ∀ {A B C X} → A , B , X ⊢ C → B , A , X ⊢ C
exch₀ {A} {B} {X = X} t = exch {∅} {B , ∅} {A , ∅} {X} t
\end{code}
}


\begin{code}
raise : ∀ {A B X} → X ⊢ A → X ⊢ (A ⊸ B) ⊸ B
raise t = abs (app var t)
\end{code}

\begin{code}
swap : ∀ {A B} → A ⊗ B , ∅ ⊢ B ⊗ A
swap {A} {B} = case var (exch₀ (pair var var))
\end{code}


\hidden{
\begin{code}
++-assoc : ∀ {a} {A : Set a} (X Y Z : List A) → X ++ (Y ++ Z) ≡ (X ++ Y) ++ Z
++-assoc ∅ Y Z = refl
++-assoc (x , X) Y Z = cong (_,_ x) (++-assoc X Y Z)
\end{code}

\begin{code}
xs++[]=xs : ∀ {a} {A : Set a} (xs : List A) → xs ++ ∅ ≡ xs
xs++[]=xs ∅ = refl
xs++[]=xs (x , xs) = cong (_,_ x) (xs++[]=xs xs)
\end{code}
}

\hidden{
\begin{code}
to-front : ∀ {X A B} → A , X ⊢ B → X ,′ A ⊢ B
to-front {X} {A} {B} t = lem1 lem2
  where
    lem1 : A , (X ++ ∅) ⊢ B → X ,′ A ⊢ B
    lem1 = exch {∅} {X} {A , ∅} {∅}
    lem2 : A , (X ++ ∅) ⊢ B
    lem2 rewrite xs++[]=xs X = t
\end{code}

\begin{code}
to-back : ∀ {X A B} → X ,′ A ⊢ B → A , X ⊢ B
to-back {X} {A} {B} t = lem2
  where
    lem1 : A , X ++ ∅ ⊢ B
    lem1 = exch {∅} {A , ∅} {X} {∅} t
    lem2 : A , X ⊢ B
    lem2 rewrite sym (xs++[]=xs (A , X)) = lem1
\end{code}
}

\hidden{
\begin{code}
YX↝XY : ∀ {A} X Y → Y ++ X ⊢ A → X ++ Y ⊢ A
YX↝XY {A} X Y t = lem₃
  where
    lem₁ : Y ++ X ++ ∅ ⊢ A
    lem₁ rewrite xs++[]=xs X = t
    lem₂ : X ++ Y ++ ∅ ⊢ A
    lem₂ = exch {∅} {X} {Y} {∅} lem₁
    lem₃ : X ++ Y ⊢ A
    lem₃ = PropEq.subst (λ Y → X ++ Y ⊢ A) (xs++[]=xs Y) lem₂
\end{code}

\begin{code}
Y[XZ]↝X[YZ] : ∀ {A} X Y Z → Y ++ (X ++ Z) ⊢ A → X ++ (Y ++ Z) ⊢ A
Y[XZ]↝X[YZ] {A} X Y Z t = exch {∅} {X} {Y} {Z} t

[YX]Z↝[XY]Z : ∀ {A} X Y Z → (Y ++ X) ++ Z ⊢ A → (X ++ Y) ++ Z ⊢ A
[YX]Z↝[XY]Z {A} X Y Z t = lem₃
  where
    lem₁ : Y ++ (X ++ Z) ⊢ A
    lem₁ rewrite ++-assoc Y X Z = t
    lem₂ : X ++ (Y ++ Z) ⊢ A
    lem₂ = Y[XZ]↝X[YZ] X Y Z lem₁
    lem₃ : (X ++ Y) ++ Z ⊢ A
    lem₃ rewrite sym (++-assoc X Y Z) = lem₂

[XZ]Y↝[XY]Z : ∀ {A} X Y Z → (X ++ Z) ++ Y ⊢ A → (X ++ Y) ++ Z ⊢ A
[XZ]Y↝[XY]Z {A} X Y Z t = lem₃
  where
    lem₁ : (X ++ Z) ++ Y ++ ∅ ⊢ A
    lem₁ rewrite xs++[]=xs Y = t
    lem₂ : (X ++ Y) ++ Z ++ ∅ ⊢ A
    lem₂ = exch {X} {Y} {Z} {∅} lem₁
    lem₃ : (X ++ Y) ++ Z ⊢ A
    lem₃ = PropEq.subst (λ Z → (X ++ Y) ++ Z ⊢ A) (xs++[]=xs Z) lem₂

X[ZY]↝X[YZ] : ∀ {A} X Y Z → X ++ (Z ++ Y) ⊢ A → X ++ (Y ++ Z) ⊢ A
X[ZY]↝X[YZ] {A} X Y Z t = lem₃
  where
    lem₁ : (X ++ Z) ++ Y ⊢ A
    lem₁ rewrite sym (++-assoc X Z Y) = t
    lem₂ : (X ++ Y) ++ Z ⊢ A
    lem₂ = [XZ]Y↝[XY]Z X Y Z lem₁
    lem₃ : X ++ Y ++ Z ⊢ A
    lem₃ rewrite ++-assoc X Y Z = lem₂
\end{code}

\begin{code}
XYZW↝XWZY : ∀ {A} X Y Z W → (X ++ Y) ++ (Z ++ W) ⊢ A → (X ++ W) ++ (Z ++ Y) ⊢ A
XYZW↝XWZY {A} X Y Z W t = lem₃
  where
    lem₁ : (X ++ Y) ++ (W ++ Z) ⊢ A
    lem₁ = X[ZY]↝X[YZ] (X ++ Y) W Z t
    lem₂ : (X ++ W) ++ (Y ++ Z) ⊢ A
    lem₂ = exch {X} {W} {Y} {Z} lem₁
    lem₃ : (X ++ W) ++ (Z ++ Y) ⊢ A
    lem₃ = X[ZY]↝X[YZ] (X ++ W) Z Y lem₂

XYZW↝YWXZ : ∀ {A} X Y Z W → (X ++ Y) ++ (Z ++ W) ⊢ A → (Y ++ W) ++ (X ++ Z) ⊢ A
XYZW↝YWXZ {A} X Y Z W t = lem₃
  where
    lem₁ : (Y ++ X) ++ (Z ++ W) ⊢ A
    lem₁ = [YX]Z↝[XY]Z Y X (Z ++ W) t
    lem₂ : (Y ++ X) ++ (W ++ Z) ⊢ A
    lem₂ = X[ZY]↝X[YZ] (Y ++ X) W Z lem₁
    lem₃ : (Y ++ W) ++ (X ++ Z) ⊢ A
    lem₃ = exch {Y} {W} {X} {Z} lem₂

XYZW↝ZXWY : ∀ {A} X Y Z W → (X ++ Y) ++ (Z ++ W) ⊢ A → (Z ++ X) ++ (W ++ Y) ⊢ A
XYZW↝ZXWY {A} X Y Z W t = lem₃
  where
    lem₁ : (X ++ Z) ++ (Y ++ W) ⊢ A
    lem₁ = exch {X} {Z} {Y} {W} t
    lem₂ : (Z ++ X) ++ (Y ++ W) ⊢ A
    lem₂ = [YX]Z↝[XY]Z Z X (Y ++ W) lem₁
    lem₃ : (Z ++ X) ++ (W ++ Y) ⊢ A
    lem₃ = X[ZY]↝X[YZ] (Z ++ X) W Y lem₂

XYZW↝ZYXW : ∀ {A} X Y Z W → (X ++ Y) ++ (Z ++ W) ⊢ A → (Z ++ Y) ++ (X ++ W) ⊢ A
XYZW↝ZYXW {A} X Y Z W t = lem₃
  where
    lem₁ : (Y ++ X) ++ (Z ++ W) ⊢ A
    lem₁ = [YX]Z↝[XY]Z Y X (Z ++ W) t
    lem₂ : (Y ++ Z) ++ (X ++ W) ⊢ A
    lem₂ = exch {Y} {Z} {X} {W} lem₁
    lem₃ : (Z ++ Y) ++ (X ++ W) ⊢ A
    lem₃ = [YX]Z↝[XY]Z Z Y (X ++ W) lem₂
\end{code}
}

\hidden{
\begin{code}
pair-left : ∀ {X A B C} → A , B , X ⊢ C → A ⊗ B , X ⊢ C
pair-left t = case var t
\end{code}

\begin{code}
pair-left′ : ∀ {X A B C} → X ++ (A , B , ∅) ⊢ C → X ,′ A ⊗ B ⊢ C
pair-left′ {X} {A} {B} {C} = lem₃
  where
    lem₁ : X ,′ A ,′ B ⊢ C → X ,′ A ⊗ B ⊢ C
    lem₁ t = to-front (pair-left (to-back {B , X} {A} (to-back {X ,′ A} {B} t)))
    lem₂ : ∀ {a} {A : Set a} xs (y z : A) → xs ,′ y ,′ z  ≡ xs ++ (y , z , ∅)
    lem₂ ∅ y z = refl
    lem₂ (x , xs) y z = cong (_,_ x) (lem₂ xs y z)
    lem₃ : X ++ (A , B , ∅) ⊢ C → X ,′ A ⊗ B ⊢ C
    lem₃ rewrite sym (lem₂ X A B) = lem₁
\end{code}
}

\begin{code}
⟦_⟧ : Type → Set
⟦ el A   ⟧ = ⟦ A ⟧ᵁ
⟦ ⊥      ⟧ = ⟦ R ⟧ᵁ
⟦ A ⊗ B  ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⊸ B  ⟧ = ⟦ A ⟧ → ⟦ B ⟧
\end{code}

\todo{mention heteogenous lists}

\begin{code}
data Env : ∀ (X : List Type) → Set where
  ∅ : Env ∅
  _,_ : ∀ {A X} → ⟦ A ⟧ → Env X → Env (A , X)
\end{code}

\hidden{
\begin{code}
Env-first : ∀ {A} → Env (A , ∅) → ⟦ A ⟧
Env-first (t , ∅) = t

Env-insert : ∀ A X Y → ⟦ A ⟧ → Env (X ++ Y) → Env (X ++ (A , Y))
Env-insert A ∅ Y A′ E = A′ , E
Env-insert A (B , X) Y A′ (B′ , E) = B′ , Env-insert A X Y A′ E

Env-exch : ∀ {X Y Z W} → Env ((X ++ Y) ++ (Z ++ W)) → Env ((X ++ Z) ++ (Y ++ W))
Env-exch {∅} {∅} {Z} {W} E = E
Env-exch {∅} {A , Y} {Z} {W} (A′ , E) = Env-insert A Z (Y ++ W) A′ (Env-exch {∅} {Y} {Z} {W} E)
Env-exch {A , X} {Y} {Z} {W} (A′ , E) = A′ , Env-exch {X} {Y} {Z} {W} E

Env-split : ∀ {X Y} → Env (X ++ Y) → (Env X) × (Env Y)
Env-split {∅} {Y} E = ∅ , E
Env-split {A , X} {Y} (A′ , E) with Env-split {X} {Y} E
... | Eˣ , Eʸ = ((A′ , Eˣ) , Eʸ)
\end{code}
}

\begin{spec}
Env-first  : Env (A , ∅) → ⟦ A ⟧
Env-exch   : Env ((X ++ Y) ++ (Z ++ W)) → Env ((X ++ Z) ++ (Y ++ W))
Env-split  : Env (X ++ Y) → (Env X) × (Env Y)
\end{spec}

\begin{code}
reify : ∀ {A X} → Env X → X ⊢ A → ⟦ A ⟧
reify E var       = Env-first E
reify E (exch {X} {Y} {Z} {W} t)  = reify (Env-exch {X} {Y} {Z} {W} E) t
reify E (abs t)   = λ A′ → reify (A′ , E) t
reify E (app s t) with Env-split E
... | Eˣ , Eʸ     = (reify Eˣ s) (reify Eʸ t)
reify E (pair s t) with Env-split E
... | Eˣ , Eʸ     = (reify Eˣ s , reify Eʸ t)
reify E (case s t) with Env-split E
... | Eˣ , Eʸ     = case reify Eˣ s of λ { (A′ , B′) → reify (A′ , B′ , Eʸ) t }
\end{code}

\begin{code}
[_] : ∀ {A} → ∅ ⊢ A → ⟦ A ⟧
[_] = reify ∅
\end{code}
