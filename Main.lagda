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
\DeclareUnicodeCharacter{7468}{$^A$}
\DeclareUnicodeCharacter{7486}{$^p$}
\DeclareUnicodeCharacter{7488}{$^T$}
\DeclareUnicodeCharacter{7489}{$^u$}
\DeclareUnicodeCharacter{739}{$^x$}
\DeclareUnicodeCharacter{740}{$^y$}

%include agda.fmt
%include main.fmt
%format # n = n
%include LambekGrishinCalculus.fmt

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
open import Function using (const)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Vec using (foldr; tabulate)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)
\end{code}
\fi

\ifverbose
\begin{code}
module main where
\end{code}
\fi

\include{IntuitionisticLogic}

\include{LinearLogic}

\include{LambekGrishinCalculus}

\begin{code}
data U : Set where
  S N NP : U

Entity : Set
Entity = Fin 2

john mary : Entity
john  = # 0
mary  = # 1

⟦_⟧ᵁ : U → Set
⟦ S   ⟧ᵁ = Bool
⟦ NP  ⟧ᵁ = Entity
⟦ N   ⟧ᵁ = Entity → Bool

_⊃_ : Bool → Bool → Bool
x ⊃ y = not x ∨ y

FORALL : (Entity → Bool) → Bool
FORALL p = foldr (const Bool) _∧_ true (tabulate p)

EXISTS : (Entity → Bool) → Bool
EXISTS p = foldr (const Bool) _∨_ false (tabulate p)
\end{code}

\begin{code}
open import LinearLogic U S ⟦_⟧ᵁ as LP renaming (Type to TypeLP; ⟦_⟧ to ⟦_⟧LP)
open import LambekGrishinCalculus U S ⟦_⟧ᵁ as LG renaming (Type to TypeLG; ⟦_⟧ to ⟦_⟧LG)
\end{code}

\begin{code}
testTV : ⟦ (el NP + ⇒ el S -) ⇐ el NP + ⟧LG ≡ ((el NP ⊗ (el S ⊸ ⊥)) ⊗ el NP) ⊸ ⊥
testTV = refl

testGQ : ⟦ el NP + ⇐ el N + ⟧LG  ≡ ((el NP ⊸ ⊥) ⊗ el N) ⊸ ⊥
testGQ = refl

testN+ : cps + (el N +) ≡ el N
testN+ = refl

testN- : ⟦ el N - ⟧LG ≡ ((el N ⊸ ⊥) ⊸ ⊥)
testN- = refl

PERSON : Entity → Bool
PERSON _ = true

EVERYONE : ⟦ ⟦ (el NP + ⇐ el N +) ⊗ el N + ⟧LG ⟧LP
EVERYONE = ( (λ{ (x , y) → FORALL λ z → y z ⊃ x z }) , PERSON )

SOME : ⟦ ⟦ el NP + ⇐ el N + ⟧LG ⟧LP
SOME = λ{ (x , y) → EXISTS λ z → y z ∧ x z }
\end{code}

\end{document}
