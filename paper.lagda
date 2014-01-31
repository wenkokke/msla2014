\documentclass{article}

%include paper.fmt
\input{paper.preamble}

\begin{document}

\title{Modeling Substructural Logics in Agda}
\author{Pepijn Kokke}
\date{\today}

\maketitle

\begin{abstract}
Bacon ipsum dolor sit amet bacon capicola flank rump pork chop in, strip steak
shankle commodo aliqua turducken sunt ground round. Sed tempor fugiat, short
loin exercitation sausage tenderloin shankle nulla hamburger venison. Qui
proident strip steak ut fatback commodo chuck sunt ut pork loin aute. Id in
doner laboris, short ribs ut short loin laborum pastrami ad capicola t-bone
sirloin. Ham meatloaf laborum reprehenderit, jerky ut in pork loin ad aliquip
tail. Cow ut kevin landjaeger, spare ribs eu filet mignon tri-tip meatloaf
voluptate. Venison laborum tail, eiusmod deserunt rump landjaeger corned beef
non labore aliqua jowl tempor.
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
``FizzBuzz of depently-typed programming''---the problem that any
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

The advantages of using such a model are plenty. For instance, you can
use Agda's built-in type-checker to verify the correctness of your
proofs; and you can use the interactive proof assistant to develop
your proofs.
In addition to this it is possible to translate proof terms of the
above and similar logics to Agda terms, which in turn allows you to
use Agda's built-in mechanisms for reduction and evaluation.


In this paper we will examine the use of such models when analysing
substructural logics such as linear logic and the Lambek-Grishin calculus.
In addition, we present an implementation and verification of the
CPS-interpretation of the Lambek-Grishin calculus as developed in
\citet{moortgat2013}.

Since this paper by no means a complete introduction to Agda or to
dependently-typed programming, we advise the interested reader to
refer to \citet{norell2009} for a detailed discussion of Agda in
general, or to the list of Agda tutorials maintained on the Agda
website.\footnote{
  See \url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Othertutorials}.
}

Before we start off, it should be mentioned that (although we omit
some of the more tedious parts) this paper is literate Agda. The code
is available on GitHub.\footnote{
  See \url{https://github.com/pepijnkokke/SubstructuralLogicsInAgda}.
}



\section{Motivation}
\label{sec:Motivation}

This paper has three main contributions; we will present
\begin{itemize}
\item an investigation into the modeling of logics in Agda;
\item an investigation into the modeling of \emph{substructural}
  logics in Agda;
\item and a verification of linear logic and the Lambek-Grishin
  calculus and their translations into the intuitionistic calculus.
\end{itemize}
Therefore it is not absurd to motivate these contributions separately.

First of all, why should we attempt to model logics at all? In our
opinion there are several good reasons.
Creating a formal model of a logical system forces you to make every
detail of the system explicit. Not only may this help you by
revealing small errors that would otherwise have gone unnoticed, but
it also forces you to scrutinise the precise formulation of your
axiomas.\footnote{
  An example: a common formulation of the exchange principle is
  $\Gamma , B , A , \Delta \vdash C \to \Gamma A, B , \Delta \vdash
  C$. However, using this principle to define, for instance, the
  swapping of two contexts $\Delta , \Gamma \vdash A \to \Gamma ,
  \Delta \vdash A$ is quadratic in the lengths of $\Gamma$ and $\Delta$.
}
Another reason is that a model of a logical system in Agda is not only
a proof of its sanity, but also a direct implementation, allowing you
to compute directly with your system using proofs and inference rules
as first-class citizens.

Why then should we explore substructural logics in Agda?
As discussed in \autoref{sec:Introduction}, most models of logic
currently implemented in Agda are models of the intuitionistic
calculus. The manner in which these models are implemented usually
leaves structural rules implicit, which makes then unsuitable for
modeling substructural logics.
In recent years, however, substructural logics have seen a surge in
fields as diverse as philosophy (relevant logics), linguistics (the
Lambek calculus) and computing science (linear logic)
\citep{restall2011}.
If we create a model of a logic with certain behaviour (such as, e.g.
linearity for linear logic), then we can be sure that, if we reify
terms of this logic back into Agda, the corresponding Agda terms will
share this behaviour.

Finally, we would we choose to model the Lambek-Grishin calculus?
The Lambek-Grishin calculus, especially the formulation that we
present here, is quite a complex system. Therefore, we hope that our
formalisation, as it makes everything explicit, can aid in the
understanding of the workings of the calculus and its
CPS-interpretation, especially for readers who come from a background
of computer science.

\section{Intuitionistic Logic}
\label{sec:IntuitionisticLogic}
\input{IntuitionisticLogic}

\section{Linear Logic}
\label{sec:LinearLogic}
\input{LinearLogic}

\section{Lambek-Grishin Calculus}
\label{sec:LambekGrishinCalculus}
\input{LambekGrishinCalculus}

\section{Conclusion}

We have presented the reader with several models of intuitionistic
logic, and examined several models for substructural logics (linear
logic and the Lambek-Grishin calculus).
We have shown how proofs in these models can be given an
interpretation in Agda through reification and translation.

\nocite{*}
\bibliographystyle{apalike}
\bibliography{paper}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
