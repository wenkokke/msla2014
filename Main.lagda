\documentclass{article}

%include main.fmt
\include{preamble}
\usepackage{natbib}
\usepackage{ifthen}
\newboolean{showHidden}
\setboolean{showHidden}{false}
\newcommand{\hidden}[1]{\ifthenelse{\boolean{showHidden}}{#1}{}}

\begin{document}

\title{Modeling the Lambek-Grishin calculus in Agda}
\author{Pepijn Kokke}
\date{\today}

\maketitle

\begin{abstract}
In this paper, we present an implementation of the logical systems \textbf{LG}
and \textbf{LP} in \emph{Martin-Löf Type Theory}, and use these implementations
to give a proof of correctness of the \emph{CPS} translation from \textbf{LG}
into \textbf{LP} as presented by in \citet{bastenhof2010} and \citet{moortgat2013}.
\end{abstract}

% \emph{Martin-Löf Type Theory} (\textbf{ITT}) is a type theory and a foundation
% of mathematics which is well-suited to the analysis of simple logical systems.
% \emph{Agda} is a programming language and proof assistant based on \textbf{ITT}.
%
% The \emph{Lambek-Grishin calculus} (\textbf{LG}) is a logical system engineered to
% model the behaviour of natural language syntax, which, in the tradition of
% categorial grammars, can be given a computational interpretation in a target logic.
% In our case, this target logic is Multiplicative Intuitionistic Linear Logic
% (MILL/\textbf{LP}) and the computational interpretation is given by means of
% a \emph{CPS-translation}.
%
% In this paper we present a formalization of the systems \textbf{LG} and
% \textbf{LP} in Agda, and give a constructive proof that the proofs in \textbf{LP}
% given by the \textit{CPS}-translation are indeed valid proofs. In other words,
% we present a translation of the rules of \textbf{LG} into \textbf{LP}.
% In addition, we present a reification of the terms in our embedded logic
% \textbf{LP} into terms of the host language, \textbf{ITT}.


\hidden{
\begin{code}
open import Function using (const)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Vec using (foldr; tabulate)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)
\end{code}
}

\hidden{
\begin{code}
module main where
\end{code}
}

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


\hidden{
\begin{code}
open import LinearLogic U S ⟦_⟧ᵁ as LP renaming (Type to TypeLP; ⟦_⟧ to ⟦_⟧LP)
open import LambekGrishinCalculus U S ⟦_⟧ᵁ as LG renaming (Type to TypeLG; ⟦_⟧ to ⟦_⟧LG)
\end{code}}

%{
%include LambekGrishinCalculus.fmt
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
%}

\bibliographystyle{plain}
\bibliography{main}

\end{document}
