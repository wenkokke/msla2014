\documentclass{article}

\usepackage{textgreek}
\usepackage{relsize}
\usepackage{stmaryrd}
\usepackage{natbib}

\usepackage{bussproofs}
\EnableBpAbbreviations
\def\fCenter{\ \vdash \ }
\def\limpl{\multimap}

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\DeclareUnicodeCharacter{8345}{$_n$}
\DeclareUnicodeCharacter{7522}{$_i$}
\DeclareUnicodeCharacter{7480}{$^L$}
\DeclareUnicodeCharacter{7481}{$^M$}
\DeclareUnicodeCharacter{7487}{$^R$}
\DeclareUnicodeCharacter{7488}{$^T$}


%include agda.fmt
%format _>>=_ = "\_\!\!\bind\!\!\_"
%format  >>=  = "\!\bind\!"
%format Vec.lookup = lookup

% verbose:
%  set to true if *all* code should be rendered, including
%  import statements, module declarations, etc...
\newif\ifverbose
\verbosefalse

% complete:
%  set to true if the reader is familiar with Agda syntax
\newif\ifcomplete
\completetrue

\begin{document}

\ifverbose
\begin{code}
open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Category.Monad
open import Category.Monad.Indexed
open import Data.Bool using (Bool; true; false)
open import Data.List using (foldr)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Fin as Fin using (Fin; suc; zero)
open import Data.Nat as Nat using (ℕ; suc; zero) renaming (_+_ to _+ℕ_)
open import Data.Product using (∃; ∃₂; _×_; _,_; _,′_; uncurry; map)
open import Function using (const; id; flip; _$_; _∘_; case_of_)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; cong; sym)
\end{code}
\fi

\ifverbose
\begin{code}
module Main where
\end{code}
\fi

\section{Delimited Continuation Monad}

\begin{spec}
  return  : A → M A
  _>>=_   : M A → (A → M B) → M B
  join    : M (M A) → M A
\end{spec}

\ifverbose
\begin{code}
module ContRemoveThis where
\end{code}
\fi

\begin{code}
  Cont      : Set → Set → Set
  Cont r a  = (a → r) → r

  return    : ∀ {r a} → a → Cont r a
  return x  = λ k → k x

  _>>=_     : ∀ {r a b} → Cont r a → (a → Cont r b) → Cont r b
  c >>= f   = λ k → c (λ x → f x k)

  join      : ∀ {r a} → Cont r (Cont r a) → Cont r a
  join c    = c >>= id
\end{code}

\begin{spec}
  return  : A → M i i A
  _>>=_   : M i j A → (A → M j k B) → M i k B
  join    : M i j (M j k A) → M i k A
\end{spec}

\ifverbose
\begin{code}
module DContRemoveThis where
\end{code}
\fi

\begin{code}
  DCont        : Set → Set → Set → Set
  DCont r i a  = (a → i) → r

  return       : ∀ {r a} → a → DCont r r a
  return x     = λ k → k x

  _>>=_        : ∀ {r i j a b} → DCont r i a → (a → DCont i j b) → DCont r j b
  c >>= f      = λ k → c (λ x → f x k)

  join         : ∀ {r i j a} → DCont r i (DCont i j a) → DCont r j a
  join c       = c >>= id

  shift        : ∀ {r o i j a} → ((a → DCont i i o) → DCont r j j) → DCont r o a
  shift f      = λ k → f (λ x → λ k′ → k′ (k x)) id

  reset        : ∀ {r i a} → DCont a i i → DCont r r a
  reset a      = λ k → k (a id)

  liftM2 : ∀ {r i j a b c} → (a → b → c) → DCont r i a → DCont i j b → DCont r j c
  liftM2 f c₁ c₂ = c₁ >>= λ x → c₂ >>= λ y → return (f x y)

  example : ∀ {r} → DCont r r ℕ
  example = (return 6) +′ reset ((return 4) +′ (shift (λ k → k 2 *′ k 7)))
    where
      _+′_ : ∀ {r i j} → DCont r i ℕ → DCont i j ℕ → DCont r j ℕ
      _+′_ = liftM2 Nat._+_
      _*′_ : ∀ {r i j} → DCont r i ℕ → DCont i j ℕ → DCont r j ℕ
      _*′_ = liftM2 Nat._*_

\end{code}



\section{Abstract Categorial Grammars}

\ifcomplete
\begin{code}
record Translation {ℓ₁ ℓ₂ : Level} {Type₁ : Set ℓ₁} {Type₂ : Set ℓ₂}
                   {Term₁ : Type₁ → Set} {Term₂  : Type₂ → Set} : Set (ℓ₁ ⊔ ℓ₂) where
  field
    ⟦_⟧  : Type₁ → Type₂
    [_]  : ∀ {τ} → Term₁ τ → Term₂ ⟦ τ ⟧
\end{code}
\fi


\def\SubsectionEvaluationContexts{
\subsection{Evaluation Contexts}

\ifverbose
\begin{code}
module Context {ℓ : Level} (Type : Set ℓ) where
\end{code}
\fi

\ifverbose
\begin{code}
  open import Data.Vec as Vec public
    using (_++_; toList)
    renaming (_∷_ to _,_; [] to ∅)
\end{code}
\fi

\begin{code}
  Context = Vec.Vec Type
\end{code}

\begin{code}
  exch : ∀ {γ} (i : Fin γ) → Context (suc γ) → Context (suc γ)
  exch zero     (A , B , Γ)  = B , (A , Γ)
  exch (suc i)  (A , Γ)      = A , (exch i Γ)

  exch-inv : ∀ {γ} Γ (i : Fin γ) → exch i (exch i Γ) ≡ Γ
  exch-inv {._} (x , y , Γ)  (zero {γ})    = refl
  exch-inv {._} (x , Γ)      (suc  {γ} i)  = cong (λ Γ → x , Γ) (exch-inv Γ i)
\end{code}

\ifverbose
\begin{code}
module Environment {ℓ₁ ℓ₂ : Level} {Type₁ : Set ℓ₁} {Type₂ : Set ℓ₂}
                   (Term₁ : Type₁ → Set) (Term₂  : Type₂ → Set)
                   (⟦_⟧ : Type₁ → Type₂) where
\end{code}
\fi

\ifverbose
\begin{code}
  private
    open module Ct = Context Type₁ hiding (exch)
\end{code}
\fi

\ifverbose
\begin{code}
  infixr 5 _∷_
\end{code}
\fi

\begin{code}
  data Env : ∀ {γ} (Γ : Context γ) → Set₁ where
    []   : Env ∅
    _∷_  : ∀ {A} {γ} {Γ} → Term₂ ⟦ A ⟧ → Env {γ} Γ → Env (A , Γ)
\end{code}

\begin{code}
  head : ∀ {A} {γ} {Γ : Context γ} → Env (A , Γ) → Term₂ ⟦ A ⟧
  head (x ∷ _) = x

  split : ∀ {γ} {Γ : Context γ} {δ} {Δ : Context δ} → Env (Γ ++ Δ) → Env Γ × Env Δ
  split {zero}  {∅}         env  = [] , env
  split {suc γ} {A , Γ} (x ∷ env) = map (_∷_ x) id (split env)

  exch : ∀ {γ} {Γ} (i : Fin γ) → Env (Ct.exch i Γ) → Env Γ
  exch {γ} {Γ} i env = doRewrite (exch′ i env)
    where
      exch′ : ∀ {γ} {Γ} (i : Fin γ) → Env Γ → Env (Ct.exch i Γ)
      exch′  zero   (x ∷ y ∷ Γ) = y ∷ x ∷ Γ
      exch′ (suc i) (x ∷ Γ)     = x ∷ exch′ i Γ
      doRewrite : Env (Ct.exch i (Ct.exch i Γ)) → Env Γ
      doRewrite env rewrite exch-inv Γ i = env
\end{code}
}

\section{Multiplicative Intuitionistic Linear Logic}
%{
%include MILL.fmt

\ifverbose
\begin{code}
module Direct (Entity : Set) where
\end{code}
\fi

\begin{prooftree}
\AXC{}
\RightLabel{\scriptsize Axiom}
\UIC{$A \fCenter A$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma, A \fCenter B$}
\RightLabel{\scriptsize $\limpl$-intro}
\UIC{$\Gamma \fCenter A \limpl B$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \fCenter A \limpl B$}
\AXC{$\Gamma \fCenter A$}
\RightLabel{\scriptsize $\limpl$-elim}
\BIC{$\Gamma \fCenter B$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \fCenter A$}
\AXC{$\Gamma \fCenter B$}
\RightLabel{\scriptsize $\otimes$-intro}
\BIC{$\Gamma \fCenter A \otimes B$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \fCenter A \otimes B$}
\AXC{$\Gamma, A, B \fCenter C$}
\RightLabel{\scriptsize $\otimes$-elim}
\BIC{$\Gamma \fCenter C$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma , A , B , \Delta \fCenter C$}
\RightLabel{\scriptsize Exchange}
\UIC{$\Gamma , B , A , \Delta \fCenter C$}
\end{prooftree}

\ifverbose
\begin{code}
  infix  3 _⊢_
  infixr 6 _~o_
  infix  7 _*_
\end{code}
\fi

\begin{code}
  data Type :  Set where
    E       :  Type
    T       :  Type
    _*_     :  Type → Type → Type
    _~o_    :  Type → Type → Type
\end{code}

\ifverbose
\begin{code}
  private
    open module Ct = Context Type public hiding (exch)
\end{code}
\fi

\begin{code}
  data _⊢_ : {γ : ℕ} (Γ : Context γ) (A : Type) → Set where

    var   :  ∀ {A} →
             A , ∅ ⊢ A
    lam   :  ∀ {A B} {γ} {Γ : Context γ} →
             A , Γ ⊢ B → Γ ⊢ A ~o B
    app   :  ∀ {A B} {γ} {Γ : Context γ} {δ} {Δ : Context δ} →
             Γ ⊢ A → Δ ⊢ A ~o B → Γ ++ Δ ⊢ B
    pair  :  ∀ {A B} {γ} {Γ : Context γ} {δ} {Δ : Context δ} →
             Γ ⊢ A → Δ ⊢ B → Γ ++ Δ ⊢ A * B
    case  :  ∀ {A B C} {γ} {Γ : Context γ} {δ} {Δ : Context δ} →
             Γ ⊢ A * B → A , B , Δ ⊢ C → Γ ++ Δ ⊢ C
    exch  :  ∀ {A} {γ} {Γ : Context (suc γ)}
             i → Γ ⊢ A → Ct.exch i Γ ⊢ A
\end{code}

\begin{code}
  Term : Type → Set
  Term A = ∅ ⊢ A
\end{code}

\begin{code}
  swap : ∀ {A B} → ∅ ⊢ A * B ~o B * A
  swap = lam (case var (exch zero (pair var var)))
\end{code}



\subsection{Direct Interpretation}

\begin{code}
  ⟦_⟧ : Type → Set
  ⟦ E       ⟧ = Entity
  ⟦ T       ⟧ = Bool
  ⟦ x * y   ⟧ = ⟦ x ⟧ × ⟦ y ⟧
  ⟦ x ~o y  ⟧ = ⟦ x ⟧ → ⟦ y ⟧
\end{code}

\ifverbose
\begin{code}
  private
    open module Env = Environment {_} {_} {Type} {Set} Term id ⟦_⟧ public hiding (exch)
\end{code}
\fi

\begin{code}
  reify : ∀ {A} {γ} {Γ : Context γ} → Env Γ → Γ ⊢ A → ⟦ A ⟧
  reify { _} {._} {._} Γ (var) = head Γ
  reify {._} {._} {._} Γ++Δ (app {_} {_} x f) with split Γ++Δ
  ... | (Γ , Δ) = reify Δ f (reify Γ x)
  reify {._} { _} { _} Γ (lam x) = λ y → reify (y ∷ Γ) x
  reify {._} {._} {._} Γ++Δ (pair x y) with split Γ++Δ
  ... | (Γ , Δ) = (reify Γ x , reify Δ y)
  reify {._} {._} {._} Γ++Δ (case {_} {_} {_} xy z) with split Γ++Δ
  ... | (Γ , Δ) = case (reify Γ xy) of λ { (x , y) → reify (x ∷ (y ∷ Δ)) z }
  reify {._} {._} {._} Γ (exch {_} i x) = reify (Env.exch i Γ) x
\end{code}

\begin{code}
  [_] : ∀ {A} → Term A → ⟦ A ⟧
  [_] = reify []
\end{code}

\ifverbose
\begin{code}
  direct : Translation {_} {_} {Type} {Set} {Term} {id}
  direct = record { ⟦_⟧ = ⟦_⟧ ; [_] = [_] }
\end{code}
\fi

\subsection{Monadic Interpretation}

\ifverbose
\begin{code}
module Monadic (Entity : Set) (M : Set → Set) (monad : RawMonad M) where
\end{code}
\fi

\ifverbose
\begin{code}
  open Direct Entity
  open RawMonad monad using (return; _⊛_)
\end{code}
\fi

\begin{code}
  ⟦_⟧ᴹ : Type → Set
  ⟦ A ~o B  ⟧ᴹ = M ⟦ A ⟧ → ⟦ B ⟧ᴹ
  ⟦ A       ⟧ᴹ = M ⟦ A ⟧
\end{code}

\begin{code}
  liftᴹ : ∀ {A} → ⟦ A ⟧ → ⟦ A ⟧ᴹ
  liftᴹ {A} x = lift A (return x)
    where
      lift : ∀ A → M ⟦ A ⟧ → ⟦ A ⟧ᴹ
      lift  E         x = x
      lift  T         x = x
      lift  (A * B)   x = x
      lift  (A ~o B)  f = λ x → lift B (f ⊛ x)


  [_]ᴹ : ∀ {A} → Term A → ⟦ A ⟧ᴹ
  [_]ᴹ = reifyᴹ []
    where
      reifyᴹ : ∀ {A} {γ} {Γ : Context γ} → Env Γ → Γ ⊢ A → ⟦ A ⟧ᴹ
      reifyᴹ {A} {γ} {Γ} env p = liftᴹ {A} (reify {A} {γ} {Γ} env p)
\end{code}



\subsection{Continuation-Passing Style and Indexed Monads}

\begin{prooftree}
\AXC{}
\RightLabel{\scriptsize Axiom}
\UIC{$A \fCenter A$}
\end{prooftree}

\begin{prooftree}
\AXC{$Γ, A \fCenter B , Δ$}
\RightLabel{\scriptsize $\limpl$-intro}
\UIC{$Γ \fCenter A \limpl B , Δ$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \fCenter A \limpl B$}
\AXC{$\Gamma \fCenter A$}
\RightLabel{\scriptsize $\limpl$-elim}
\BIC{$\Gamma \fCenter B$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \fCenter A$}
\AXC{$\Gamma \fCenter B$}
\RightLabel{\scriptsize $\otimes$-intro}
\BIC{$\Gamma \fCenter A \otimes B$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma \fCenter A \otimes B$}
\AXC{$\Gamma, A, B \fCenter C$}
\RightLabel{\scriptsize $\otimes$-elim}
\BIC{$\Gamma \fCenter C$}
\end{prooftree}

\begin{prooftree}
\AXC{$\Gamma , A , B , \Delta \fCenter C$}
\RightLabel{\scriptsize Exchange}
\UIC{$\Gamma , B , A , \Delta \fCenter C$}
\end{prooftree}

\ifverbose
\begin{code}
module IndexedRemoveMe (Entity : Set) {M : Set → Set → Set → Set} (imonad : RawIMonad M) where
\end{code}
\fi

\ifverbose
\begin{code}
  open Direct Entity public using (Type; E; T; _*_; _~o_; ⟦_⟧)
  open module Ct = Context Type public hiding (exch)
  open RawIMonad imonad
\end{code}
\fi

\ifverbose
\begin{code}
  infix 3 _⊢_
\end{code}
\fi

\begin{code}
  data _⊢_ : ∀ {γ} (Γ : Context γ) {δ} (Δ : Context δ) → Set where

    var    : ∀ {A} →
             A , ∅ ⊢ A , ∅

    lam    : ∀ {A B} {γ} {Γ : Context γ} →
             A , Γ ⊢ B , ∅ → Γ ⊢ A ~o B , ∅

    app    : ∀ {A B} {γ₁} {Γ₁ : Context γ₁} {γ₂} {Γ₂ : Context γ₂}
                     {δ₁} {Δ₁ : Context δ₁} {δ₂} {Δ₂ : Context δ₂} →
             Γ₁ ⊢ A , Δ₁ → Γ₂ ⊢ A ~o B , Δ₂ → Γ₁ ++ Γ₂ ⊢ B , Δ₁ ++ Δ₂

    pair   : ∀ {A B} {γ₁} {Γ₁ : Context γ₁} {γ₂} {Γ₂ : Context γ₂}
                     {δ₁} {Δ₁ : Context δ₁} {δ₂} {Δ₂ : Context δ₂} →
             Γ₁ ⊢ A , Δ₁ → Γ₂ ⊢ B , Δ₂ → Γ₁ ++ Γ₂ ⊢ A * B , Δ₁ ++ Δ₂

    case   : ∀ {A B C} {γ₁} {Γ₁ : Context γ₁} {γ₂} {Γ₂ : Context γ₂}
                       {δ₁} {Δ₁ : Context δ₁} {δ₂} {Δ₂ : Context δ₂} →
             Γ₁ ⊢ A * B , Δ₁ → A , B , Γ₂ ⊢ C , Δ₂ → Γ₁ ++ Γ₂ ⊢ C , Δ₁ ++ Δ₂

    exchᴸ  : ∀ {γ} {Γ : Context (suc γ)} {δ} {Δ : Context δ}
             i → Γ ⊢ Δ → Ct.exch i Γ ⊢ Δ

    exchᴿ  : ∀ {γ} {Γ : Context γ} {δ} {Δ : Context (suc δ)}
             i → Γ ⊢ Δ → Γ ⊢ Ct.exch i Δ
\end{code}

\begin{code}
  Term : ∀ {γ} → Context γ → Set
  Term Γ = ∅ ⊢ Γ
\end{code}

\begin{code}
  swap : ∀ {A B} → ∅ ⊢ A * B ~o B * A , ∅
  swap = lam (case var (exchᴸ zero (pair var var)))
\end{code}

\ifverbose
\begin{code}
  module CPS (R : Set) where
\end{code}
\fi

\begin{code}
    cps : ∀ {γ} → Context γ → Set
    cps ∅ = R
    cps (A , Γ) = (⟦ A ⟧ → R) → cps Γ
\end{code}

\begin{spec}
    cps ⟦ T ⟧ (E , E , ∅) ↝β (Entity → Bool) → (Entity → Bool) → Bool
\end{spec}

\begin{code}
    Term₁ : Type → Set
    Term₁ A = ∅ ⊢ A , ∅

    open module Env = Environment {_} {_} {Type} {Set} Term₁ id (⟦_⟧)

    reify : ∀ γ (Γ : Context γ) δ (Δ : Context δ) → Env Γ → Γ ⊢ Δ → cps Δ
    reify .1 .(A , ∅) .1 .(A , ∅) env (var {A})
      = λ k → k (head env)
    reify γ Γ .(suc _) .(A ~o B , ∅) env (lam {A} {B} {.γ} {.Γ} p)
      = {!!}
    reify .(γ₁ +ℕ γ₂) .(Γ₁ ++ Γ₂) .(suc (δ₁ +ℕ δ₂)) .(B , Δ₁ ++ Δ₂) env (app {A} {B} {γ₁} {Γ₁} {γ₂} {Γ₂} {δ₁} {Δ₁} {δ₂} {Δ₂} p p₁)
      = {!!}
    reify .(γ₁ +ℕ γ₂) .(Γ₁ ++ Γ₂) .(suc (δ₁ +ℕ δ₂)) .(A * B , Δ₁ ++ Δ₂) env (pair {A} {B} {γ₁} {Γ₁} {γ₂} {Γ₂} {δ₁} {Δ₁} {δ₂} {Δ₂} p p₁)
      = {!!}
    reify .(γ₁ +ℕ γ₂) .(Γ₁ ++ Γ₂) .(suc (δ₁ +ℕ δ₂)) .(C , Δ₁ ++ Δ₂) env (case {A} {B} {C} {γ₁} {Γ₁} {γ₂} {Γ₂} {δ₁} {Δ₁} {δ₂} {Δ₂} p p₁)
      = {!!}
    reify .(suc γ) .(Ct.exch i Γ) δ Δ env (exchᴸ {γ} {Γ} i p)
      = reify _ _ _ _ (Env.exch i env) p
    reify γ Γ .(suc δ) .(Ct.exch i Δ) env (exchᴿ {.γ} {.Γ} {δ} {Δ} i p)
      = {!!}
\end{code}

\begin{code}
  module IndexedX (R : Set) where

    indexed : ∀ {γ} → Context γ → Set
    indexed ∅ = R
    indexed (A , Γ) = M (indexed Γ) R ⟦ A ⟧
\end{code}

\begin{spec}
  indexed (E , E , ∅) ⟦ T ⟧ ↝β M (M Bool Bool Entity) Bool Entity
\end{spec}

\begin{code}
-- import Category.Monad.Continuation as Cont
--
-- RawIMonadDCont : (M : Set → Set → Set → Set) → Set₁
-- RawIMonadDCont M = Cont.RawIMonadDCont {_} {lzero} {Set} id M
--
-- DCont : Set → Set → Set → Set
-- DCont = Cont.DCont id
--
-- DContIMonadDCont : RawIMonadDCont DCont
-- DContIMonadDCont = Cont.DContIMonadDCont {f = lzero} id
--
-- DContIMonad : RawIMonad DCont
-- DContIMonad = Cont.RawIMonadDCont.monad DContIMonadDCont
--
-- data Entity : Set where
--   John : Entity
--   Mary : Entity
--
-- open Indexed Entity DContIMonad
-- open Indexed.Indexed Entity DContIMonad Bool
--
-- test : ( indexed (E , E , ∅) ) ≡ ( (Entity → Bool) → (Entity → Bool) → Bool )
-- test = refl
\end{code}
%}




\SubsectionEvaluationContexts

\bibliographystyle{plainnat}
\bibliography{Main}

\end{document}
