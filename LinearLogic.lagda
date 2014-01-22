%include agda.fmt

\ifverbose
\begin{code}
open import Function using (case_of_)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)
\end{code}
\fi

\section{Linear Logic (LP)}
%{
%include LinearLogic.fmt

\ifverbose
\begin{code}
module LinearLogic (U : Set) (R : U) (⟦_⟧ᵁ : U → Set) where
\end{code}
\fi

\ifverbose
\begin{code}
infixr 40 ¬_
infix  30 _⊗_
infixr 20 _⊸_
infix  4  _⊢_
\end{code}
\fi

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

\begin{code}
data _⊢_ : ∀ (X : List Type) (A : Type) → Set where
  var   : ∀ {A} → A , ∅ ⊢ A
  exch  : ∀ {A X Y Z W} → (X ++ Z) ++ (Y ++ W) ⊢ A → (X ++ Y) ++ (Z ++ W) ⊢ A
  abs   : ∀ {A B X} → A , X ⊢ B → X ⊢ A ⊸ B
  app   : ∀ {A B X Y} → X ⊢ A ⊸ B → Y ⊢ A → X ++ Y ⊢ B
  pair  : ∀ {A B X Y} → X ⊢ A → Y ⊢ B → X ++ Y ⊢ A ⊗ B
  case  : ∀ {A B C X Y} → X ⊢ A ⊗ B → A , B , Y ⊢ C → X ++ Y ⊢ C
\end{code}

\begin{code}
exch₀ : ∀ {A B C X} → A , B , X ⊢ C → B , A , X ⊢ C
exch₀ {A} {B} {X = X} t = exch {X = ∅} {Y = B , ∅} {Z = A , ∅} {W = X} t
\end{code}

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

\begin{code}
to-front : ∀ {X A B} → A , X ⊢ B → X ,′ A ⊢ B
to-front {X} {A} {B} t = lem1 lem2
  where
    lem1 : A , (X ++ ∅) ⊢ B → X ,′ A ⊢ B
    lem1 = exch {X = ∅} {Y = X} {Z = A , ∅} {W = ∅}
    lem2 : A , (X ++ ∅) ⊢ B
    lem2 rewrite xs++[]=xs X = t
\end{code}

\begin{code}
to-back : ∀ {X A B} → X ,′ A ⊢ B → A , X ⊢ B
to-back {X} {A} {B} t = lem2
  where
    lem1 : A , X ++ ∅ ⊢ B
    lem1 = exch {X = ∅} {Y = A , ∅} {Z = X} {W = ∅} t
    lem2 : A , X ⊢ B
    lem2 rewrite sym (xs++[]=xs (A , X)) = lem1
\end{code}

\begin{code}
Y[XZ]↝X[YZ] : ∀ {A} X Y Z → Y ++ (X ++ Z) ⊢ A → X ++ (Y ++ Z) ⊢ A
Y[XZ]↝X[YZ] {A} X Y Z t = exch {X = ∅} {Y = X} {Z = Y} {W = Z} t

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
    lem₂ = exch {X = X} {Y = Y} {Z = Z} {W = ∅} lem₁
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
pair-left : ∀ {X A B C} → A , B , X ⊢ C → A ⊗ B , X ⊢ C
pair-left t = case var t
\end{code}

\begin{code}
pair-leftʳ : ∀ {X A B C} → X ,′ A ,′ B ⊢ C → X ,′ A ⊗ B ⊢ C
pair-leftʳ {X} {A} {B} t = to-front (pair-left (to-back {B , X} {A} (to-back {X ,′ A} {B} t)))
\end{code}

\begin{code}
lemma-∷ʳ : ∀ {a} {A : Set a} xs (y z : A) → xs ,′ y ,′ z  ≡ xs ++ (y , z , ∅)
lemma-∷ʳ ∅ y z = refl
lemma-∷ʳ (x , xs) y z = cong (_,_ x) (lemma-∷ʳ xs y z)

pair-leftʳ′ : ∀ {X A B C} → X ++ (A , B , ∅) ⊢ C → X ,′ A ⊗ B ⊢ C
pair-leftʳ′ {X} {A} {B} rewrite sym (lemma-∷ʳ X A B) = pair-leftʳ {X} {A} {B}
\end{code}

\begin{code}
raise : ∀ {A B X} → X ⊢ A → X ⊢ (A ⊸ B) ⊸ B
raise t = abs (app var t)
\end{code}

\begin{code}
swap : ∀ {A B} → A ⊗ B , ∅ ⊢ B ⊗ A
swap {A} {B} = case var (exch₀ (pair var var))
\end{code}

\begin{code}
⟦_⟧ : Type → Set
⟦ el A   ⟧ = ⟦ A ⟧ᵁ
⟦ ⊥      ⟧ = ⟦ R ⟧ᵁ
⟦ A ⊗ B  ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⊸ B  ⟧ = ⟦ A ⟧ → ⟦ B ⟧
\end{code}

\begin{code}
data Env : ∀ (X : List Type) → Set where
  ∅ : Env ∅
  _,_ : ∀ {A X} → ⟦ A ⟧ → Env X → Env (A , X)

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

\begin{code}
reify : ∀ {A X} → Env X → X ⊢ A → ⟦ A ⟧
reify E var = Env-first E
reify E (exch {_} {X} {Y} {Z} {W} t) = reify (Env-exch {X} {Y} {Z} {W} E) t
reify E (abs t) = λ A′ → reify (A′ , E) t
reify E (app s t) with Env-split E
... | Eˣ , Eʸ = (reify Eˣ s) (reify Eʸ t)
reify E (pair s t) with Env-split E
... | Eˣ , Eʸ = (reify Eˣ s , reify Eʸ t)
reify E (case s t) with Env-split E
... | Eˣ , Eʸ = case reify Eˣ s of λ { (A′ , B′) → reify (A′ , B′ , Eʸ) t }
\end{code}

\begin{code}
[_] : ∀ {A} → ∅ ⊢ A → ⟦ A ⟧
[_] = reify ∅
\end{code}
%}
