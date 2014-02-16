\documentclass{article}

%include paper.fmt
\input{preamble}

\begin{document}

\title{Modelling Substructural Logics in Agda}
\author{Pepijn Kokke}
\date{\today}

\maketitle

\begin{abstract}
In this paper, we will examine models of substructural logics in
Agda. The reason for this is that most existing models formalise
intuitionistic logic and are entirely unsuitable to modelling
substructural logics. In recent years, however, substructural logics
have seen a surge in usage.

Concretely we present the reader with an explicit model of
intuitionistic logic, and derive models for linear logic and the
Lambek-Grishin calculus. In addition, we show how to reify proofs in
these logics into terms in Agda. All this is implemented as an Agda
library, which is made available on GitHub.

Finally we conclude with an example from formal linguistics in which
we demonstrate one possible usage of our implemented Agda library.
\end{abstract}

\hidden{
\begin{code}
module paper where
\end{code}
}

\section{Introduction}
\label{sec:Introduction}

You can find implementations of the simply-typed lambda calculus in
Agda all across the web---for instance, the implementations by
\citet{mazzoli2013}, \citet{erdi2013} or \citet{mu2008}. It is used
as a running example in \citeauthor{norell2009}'s \emph{Introduction
to  Agda}, and \citeauthor{erdi2013} goes as far as to call it the
``FizzBuzz of dependently-typed programming''---the problem that any
capable programmer in the field should be able to solve.

Though each of these implementation has its own merits, they are all
loosely based on the following model of the simply-typed lambda
calculus.\footnote{It should be noted that for the sake of readability
in this paper implicit arguments are often left out. Any undefined
variable that is encountered upon reading should be considered
implicitly quantified over unless noted otherwise.}

%{
%include IntuitionisticLogic.fmt
\begin{spec}
data _⊢_ : {k : ℕ} (Γ : Vec Type k) (A : Type) → Set where
  var   : (x : Fin k) → Γ ⊢ lookup x Γ
  abs   : A , Γ ⊢ B → Γ ⊢ A ⇒ B
  app   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
\end{spec}
%}

\noindent
The advantages of using such a model are plenty. For instance, you can
use Agda's built-in type-checker to verify the correctness of your
proofs; and you can use the interactive proof assistant to develop
your proofs.

\vspace{1em}

\noindent
This paper has three main contributions; we will present
\begin{itemize}
\myitem
  an investigation into the modelling of logics in Agda;
\myitem
  an investigation into the modelling of \emph{substructural}
  logics in Agda;
\myitem
  and---concretely---models of linear logic and of the Lambek-Grishin
  calculus, and a verification of the correctness of their
  interpretations in intuitionistic logic.
\end{itemize}

\noindent
Below we will briefly motivate these contributions separately.


\paragraph{Why model logics in Agda at all?}
Why should we attempt to model logics at all? In our opinion there are
several good reasons for doing this.

First of all, creating a formal model of a logical system forces you
to make every detail of the system explicit. Not only may this help you
by revealing small errors that would otherwise have gone unnoticed,
but it also forces you to scrutinise the precise formulation of your
axiomas.\footnote{
  An example: a common formulation of the exchange principle is
  $\Gamma , B , A , \Delta \vdash C \to \Gamma A, B , \Delta \vdash
  C$. However, using this principle to define, for instance, the
  swapping of two contexts $\Delta , \Gamma \vdash A \to \Gamma ,
  \Delta \vdash A$ requires a number of applications quadratic in the
  lengths of $\Gamma$ and $\Delta$.
}

Secondly, a model of a logical system in Agda is more than just a
proof of its sanity. It is also a direct implementation of the
calculus, which allows you play with your logic in a computational
environment, using inference rules and proofs as first-class
citizens. In addition to this, as mentioned before, the correctness of
your proofs is checked by Agda's type-checker; and you can use theorem
provers built in or for Agda, such as Agsy \citep{lindblad2006}, to
prove theorems in your modelled logic.

Lastly, for logics which have a computational interpretation in
intuitionistic logic, you can translate proofs in the modelled logic
to terms in Agda, which allows you to use Agda's built-in mechanisms
for reduction and evaluation.

\paragraph{Why should we model \emph{substructural} logics in Agda?}
As discussed above, most models of logic currently implemented in
Agda formalise intuitionistic logic. In addition, the manner in which
these models are implemented usually leaves the structural rules
implicit, making them unsuitable for formalising substructural rules.

In recent years, however, substructural logics have seen a surge in
fields as diverse as philosophy (relevant logics), linguistics (the
Lambek calculus) and computing science (linear logic)
\citep{restall2011}. We therefore think it useful to examine the
modelling of such logics in Agda as well.

Furthermore, when viewed from the perspective of Agda, if we can
formalise a logic with certain properties (such as linearity for
linear logic), then we can easily prove that, when we reify terms of
this logic back into Agda, the corresponding Agda terms will share
this property. This allows us to embed, for instance, provably linear
lambda terms in Agda.


\paragraph{Why model the Lambek-Grishin calculus?}
The formulation of the Lambek-Grishin calculus (\textbf{LG}) modelled
in this paper is quite a complex system. It is a substructural logic
based on the non-associative Lambek calculus (\textbf{NL}), but adds
the dual for each connective \citep{moortgat2013}.
It is formulated in the style of display logic \citep{belnap1982}, and
uses techniques such as polarisation and focusing \citep{andreoli1992}.
We therefore feel that it would be an interesting enterprise to model
the Lambek-Grishin calculus, as it allows us to examine not only the
formalisation of substructure in isolation, but also in the presence
of other techniques.

And, since \textbf{LG} is a very complex logical system, we hope
that an explicit and interactive formalisation may be able to aid
students in understanding it---especially those coming from a
background in computer science.

\vspace{1em}

\noindent
Since this paper is by no means a complete introduction to Agda or to
dependently-typed programming, we advise the interested reader to
refer to \citet{norell2009} for a detailed discussion of Agda in
general, or to the list of Agda tutorials maintained on the Agda
website.\footnote{
  See \url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Othertutorials}.
}

\vspace{1em}

\noindent
Before we start off, it should be mentioned that (although we omit
some of the more tedious parts) this paper is written in literate
Agda, and the code has been made available on GitHub.\footnote{
  See \url{https://github.com/pepijnkokke/SubstructuralLogicsInAgda}.
}

\section{Intuitionistic Logic}
\label{sec:IntuitionisticLogic}
\input{IntuitionisticLogic}

\section{Linear Logic}
\label{sec:LinearLogic}
\input{LinearLogic}

\section{Lambek-Grishin Calculus}
\label{sec:LambekGrishinCalculus}
\input{LambekGrishinCalculus}

\subsection{Examples from natural language}
\label{sec:example}
%include LambekGrishinCalculus.fmt

\hidden{
\begin{code}
open import Data.Bool using (Bool; not; _∨_; _∧_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.Product using (_×_; _,_)
\end{code}
}

In this final section we will demonstrate a possible usage of our
model of \textbf{LG}. We will derive the denotation of the following
example sentence.

\begin{center}
\textit{``Everyone finds some unicorn.''}
\end{center}

\noindent
First, we define a couple of meaning postulates. For brevity's sake,
we will also postulate the existence of an |Entity| type with the
corresponding universal and existential quantifiers, though we could
trivially define this ourselves.

\begin{code}
postulate
  Entity   : Set
  _⊃_      : Bool → Bool → Bool
  FORALL   : (Entity → Bool) → Bool
  EXISTS   : (Entity → Bool) → Bool
  PERSON   : Entity → Bool
  FIND     : Entity → Entity → Bool
  UNICORN  : Entity → Bool
\end{code}

\noindent
Secondly, we must define our type universe. In this case we will
define it to be the usual set of atomic syntactic types.

\begin{code}
data U : Set where S N NP : U

⟦_⟧ᵁ : U → Set
⟦ S   ⟧ᵁ = Bool
⟦ N   ⟧ᵁ = Entity → Bool
⟦ NP  ⟧ᵁ = Entity
\end{code}

\hidden{
\begin{code}
import IntuitionisticLogic U ⟦_⟧ᵁ as IL
import LinearLogic U S ⟦_⟧ᵁ as LP
open import LambekGrishinCalculus U S ⟦_⟧ᵁ as LG
open IL.Explicit using (Ctxt; _,_; ∅)
open IL.Explicit.Reify TypeReify
\end{code}
}

\noindent
Next, we define our lexicon. The entries of our lexicon are lambda
terms typed by the translations of their syntactic types.

\begin{code}
everyone  : ⟦ (el NP + ⇐ el N +) ⊗ el N + ⟧
everyone  = ( (λ{ (A , B) → FORALL (λ x → B x ⊃ A x) }) , PERSON )
finds     : ⟦ (el NP + ⇒ el S -) ⇐ el NP + ⟧
finds     = λ{ ((x , k) , y) → k (FIND y x) }
some      : ⟦ el NP + ⇐ el N + ⟧
some      = λ{ (A , B) → EXISTS (λ x → A x ∧ B x) }
unicorn   : ⟦ el N + ⟧
unicorn   = UNICORN
\end{code}

\noindent
Last, since we have not yet proven decidability, we have to give a
proof that our sentence structure is syntactically correct.

\begin{code}
sent :
  · (el NP + ⇐ el N +) ⊗ el N +         -- everyone
  · ⊗ (· (el NP + ⇒ el S -) ⇐ el NP +  -- finds
  · ⊗ (· el NP + ⇐ el N +               -- some
  · ⊗ · el N + ·                         -- unicorn
  )) ⊢[ el S - ]
sent =
  μ (res₃ (⊗L (res₃ (μ̃* (⇐L (
    μ̃ (res₄ (res₁ (res₁ (res₃ (μ̃* (⇐L (
      μ̃ (res₂ (res₃ (μ̃* (⇐L (⇒L var covar) var))))) var))))))) var)))))
\end{code}

\noindent
With all these components, we can finally compute the meaning of our
sentence, leaving our meaning postulates unevaluated as usual.

\begin{spec}
  [ sent ] (everyone , finds , some , unicorn , ∅) ↝β
    λ k → FORALL (λ x₁ → PERSON x₁ ⊃ EXISTS (λ x₂ → k (FIND x₂ x₁) ∧ UNICORN x₂))
\end{spec}



\section{Future work}

\paragraph{Reification of properties.}
When we reify a term in a substructural logic into Agda, we lose the
information regarding its behaviour. For instance, if we have an
proof in the presented model of \textbf{LP}, we would like to be able
to obtain a proof of linearity for the reified term.

\paragraph{Decidability of focus shifting.}
If we could implement a decision procedure for the focus shifting
principles (not discussed in this paper; a sequence of unfocused
rules, started by a \textmu-application and terminated by a
\textmu-abstraction), we could add them as derived rules to our model
of \textbf{LG}. This would make writing proofs much easier, and would
be a good step in the direction of proving decidability of \textbf{LG}
in general.

\paragraph{Decidability of LG.}
We could implement a decision procedure for \textbf{LG} in
general. Using this procedure we would no longer have to manually
prove syntactic correctness. In addition to this, if we implemented
decidability of \textbf{LG} plus associativity, we could use the
resulting procedure as an implementation of parsing-as-deduction.

\paragraph{Mirror symmetries.}
Another property of \textbf{LG} is that types and proofs obey certain
mirror symmetries (due to the presence of dual operators and
directional implications). Implementing these symmetries as functions
on types and proofs would allow us to easily construct the duals of
types and their proofs, and would aid in the understanding of these
dualities.

\paragraph{Extract Haskell library.}
Since Agda supports the extraction of programs into several languages
(most notably Haskell and JavaScript) we could investigate the
extraction of an optimised Haskell library for \textbf{LG} (and its
use in natural language processing) from our implementation.



\section{Conclusion}

We have presented the reader with several models of intuitionistic
logic, and examined several models for substructural logics (linear
logic and the Lambek-Grishin calculus).
We have shown how proofs in these models can be given an
interpretation in Agda through reification and translation.
And, last, we have demonstrated the usage of our models in an example
taken from formal linguistics.

\nocite{*}
\bibliographystyle{apalike}
\bibliography{paper}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
