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
module main where
\end{code}
}

\section{Introduction}

You can find implementations of the simply-typed lambda calculus in
Agda all across the web---for instance, the implementations by
\citet{mazzoli2013}, \citet{erdi2013} or \citet{mu2008}. It is used
as a running example in \citeauthor{norell2009}'s \emph{Introduction
to  Agda}, and \citeauthor{erdi2013} goes as far as to call it the
``FizzBuzz of depently-typed programming''---the problem that any
capable programmer in the field should be able to solve.

Though each of these implementation has its own interesting
contributions, they are all loosely based on the following model of
the simply-typed lambda calculus.

%{
%include IntuitionisticLogic.fmt
\begin{spec}
data _⊢_ : {k : ℕ} (Γ : Vec Type k) (A : Type) → Set where
  var   : ∀ {k Γ} → (x : Fin k) → Γ ⊢ Vec.lookup x Γ
  abs   : ∀ {k Γ A B} → A , Γ ⊢ B → Γ ⊢ A ⇒ B
  app   : ∀ {k Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
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
substructural logics such as linear logic and the Lambek and
Lambek-Grishin calculi.
In addition, we present an implementation of the \emph{CPS}-interpretation
of the Lambek-Grishin calculus as developed in \citet{moortgat2013}.


Since this is not an introduction to Agda or to dependently-typed
programming, we advise the interested reader to refer to \citet{norell2009}
for a detailed discussion of Agda in general, or to the list of Agda
tutorials maintained on the Agda website.\footnote{
  \url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Othertutorials}
}

Before we start off, we will elaborate a bit further on the motivation
for using Agda as a tool to model logical systems.

\section{Motivation}

\begin{itemize}
\item \todo{forces you to make a logic concrete---no hand-waving is allowed;}
% example: exchange laws
\item \todo{allows you to use the Agda proof assistent to write proofs;}
\item \todo{can catch errors in your logic;}
\item \todo{gives you an implementation of your calculus in addition
    to a proof of its validity.}
\end{itemize}

\section{Intuitionistic Logic}
\input{IntuitionisticLogic}

\section{Linear Logic}
\input{LinearLogic}

\section{Lambek Calculus}
\input{LambekCalculus}

\section{Lambek-Grishin Calculus}
\input{LambekGrishinCalculus}

\bibliographystyle{apalike}
\bibliography{main}

\end{document}
