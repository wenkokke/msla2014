%include paper.fmt
%include IntuitionisticLogic.fmt

\hidden{
\begin{code}
open import Level using (Level; _⊔_)
open import Function using (id; case_of_)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc; zero)
open import Data.Vec as Vec using (Vec) renaming (_∷_ to _,_; [] to ∅)
open import Data.List using (_∷_; [])
open import Data.List as List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.Product as Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong)
\end{code}
}

\hidden{
\begin{code}
module IntuitionisticLogic (U : Set) (⟦_⟧ᵁ : U → Set) where
\end{code}
}

\hidden{
\begin{code}
infix  30 _⊗_
infixr 20 _⇒_
\end{code}
}

\subsection{Modeling IL with de Bruijn indices}

If we wish to model the intuitionistic calculus, we first have to do
something about our notation. The reason for this is that the usual
notation with named variables introduces a whole host of problems,
such as checking for proper scopal and binding relations.
To solve this we are going to use a notation introduced first in
\citet{bruijn1972}. In this notation, instead of using names for
binding, we are going to use numbers---the semantics being that the
numbers tell you how many lambdas up they are bound (i.e. they are
indices into our context.) See \autoref{fig:namedvsdebruijn} for an
example of how terms in named notation compare to terms in de Bruijn
notation.

\begin{figure}[h]
  \centering
  \begin{tabular}{l l}
     Named & de Bruijn
  \\ \hline
  \\ $\lambda x \to x$
   & $\textcolor{red}{\lambda}\ \textcolor{red}{0}$
  \\ $\lambda x \to \lambda y \to x$
   & $\textcolor{red}{\lambda}\ \textcolor{blue}{\lambda}\ \textcolor{red}{1}$
  \\ $\lambda x \to \lambda y \to \lambda z \to x \ z \ (y \ z)$
   & $\textcolor{red}{\lambda}\ \textcolor{blue}{\lambda}\ \textcolor{green}{\lambda}\
      \textcolor{red}{2}\ \textcolor{green}{0}\ (\textcolor{blue}{1}\ \textcolor{green}{0})$
  \end{tabular}
  \caption{Named notation versus de Bruijn notation \citep{mazzoli2013}.}
  \label{fig:namedvsdebruijn}
\end{figure}

To aid our translation of the intuitionistic calculus to Agda, we can
formulate the de Bruijn notation as a set of inference rules. The
result can be seen in \autoref{fig:debruijnaslogic}.

\begin{figure}[h]
  \begin{mdframed}
    \begin{scprooftree}{0.8}
      \AXC{}
      \RightLabel{\scriptsize AX}
      \UIC{$\Gamma \fCenter (var \ i) : \Gamma_i$}
    \end{scprooftree}

    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma, A \fCenter t : B$}
        \RightLabel{\scriptsize $\Rightarrow$-intro}
        \UIC{$\Gamma \fCenter (abs \ t) : A \Rightarrow B$}
      \end{scprooftree}
    \end{minipage}%
    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma \fCenter s : A \Rightarrow B$}
        \AXC{$\Gamma \fCenter t : A$}
        \RightLabel{\scriptsize $\Rightarrow$-elim}
        \BIC{$\Gamma \fCenter (app \ s \ t) : B$}
      \end{scprooftree}
    \end{minipage}

    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma \fCenter s : A$}
        \AXC{$\Gamma \fCenter t : B$}
        \RightLabel{\scriptsize $\times$-intro}
        \BIC{$\Gamma \fCenter (pair \ s \ t) : A \times B$}
      \end{scprooftree}
    \end{minipage}%
    \begin{minipage}[c]{0.45\linewidth}
      \begin{scprooftree}{0.8}
        \AXC{$\Gamma \fCenter s : A \times B$}
        \AXC{$A , B , \Gamma \fCenter t : C$}
        \RightLabel{\scriptsize $\times$-elim}
        \BIC{$\Gamma \fCenter (case \ s \ t) : C$}
      \end{scprooftree}
    \end{minipage}
  \end{mdframed}

  \caption{Inference rules for \textbf{IL} corresponding to the de Bruijn notation.}
  \label{fig:debruijnaslogic}
\end{figure}

The first thing we need in order to model the intuitionistic calculus
is a representation for the types (or connectives) that we wish to
use. In this paper we will limit ourselves to implication and
conjunction.

Below, you can see the datatype we use to encode our types. We have
intuitionistic conjunction ($\_\!\times\!\_$) and implication (written
as $\_\!\Rightarrow\!\_$, due to the fact that $\_\!\rightarrow\!\_$
is Agda's function type, or---from our point of view---the
meta-logical implication). In addition, we are abstracting over some
type $U$. The reason for this is that we do not want to be forced to
specify the atomic types---instead we shall allow the user to provide
their own universe of atomic types.\footnote{
  For an example of this, see \todo{make a link and, y'know, a section
  with an actual example of this.}
}

%<*type>
\begin{code}
data Type : Set where
  el    : (A : U) → Type
  _⊗_   : Type → Type → Type
  _⇒_  : Type → Type → Type
\end{code}
%</type>

\hidden{
\begin{code}
module Implicit where
\end{code}
}

\hidden{
\begin{code}
  infix  4  _⊢_
\end{code}
}

Since we already have the formulation of the simply-typed lambda
calculus as presented in \autoref{fig:debruijnaslogic}, all that rests
is to convert it to Agda.

If we use vectors\footnote{
  See \url{http://agda.github.io/agda-stdlib/html/Data.Vec.html\#604}.
} to model contexts and finite sets\footnote{
  See \url{http://agda.github.io/agda-stdlib/html/Data.Fin.html\#775}.
} to model variables, we can ensure that every variable is bound,
either to a type in the context or to a lambda.%
\footnote{
  It should be stated that throughout this paper we will use an
  alternative notation for lists and vectors, using $\_,\_$ for the
  cons operator and $∅$ for the empty list (or vector), as we deem
  this notation to be better suited to writing sequent contexts.
  For the concatination of contexts, however, we will stick to
  $\_\!\plus\!\_$, as usual.
}
We can then define a |lookup| function as follows.

\begin{spec}
  lookup : Fin k → Vec A k → A
  lookup  zero     (A , Γ)  = A
  lookup  (suc x)  (A , Γ)  = lookup x Γ
\end{spec}

And using this function we can finally present a full formalisation of
our inference rules.

%<*il-implicit>
\begin{code}
  data _⊢_ : ∀ {k} (Γ : Vec Type k) (A : Type) → Set where
    var   : ∀ {k} {Γ : Vec Type k} (x : Fin k) → Γ ⊢ Vec.lookup x Γ
    abs   : ∀ {A B} {k} {Γ : Vec Type k} → A , Γ ⊢ B → Γ ⊢ A ⇒ B
    app   : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    pair  : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ⊗ B
    case  : ∀ {A B C} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B → A , B , Γ ⊢ C → Γ ⊢ C
\end{code}
%</il-implicit>

In \autoref{sec:Motivation} we mentioned that one of the advantages of
modeling a logic in Agda was the use of Agda's interactive proof
assistant.
Below we will demonstrate how the proof assistant might be used to
formulate a proof.

Agda allows you to leave holes in expressions; for every hole you
leave, Agda will report the type of the expressions needed to plug
that hole. For instance, in the example below we try to prove the
commutativity of $\_\!\times\!\_$.
After an initial lambda abstraction, we leave a hole, and Agda tells
us the type it is expecting at that position.

\begin{spec}
  swap : Γ ⊢ A × B ⇒ B × A
  swap = abs ?0

  ?0 : A × B , Γ ⊢ B × A
\end{spec}

This provides us with enough information to continue the proof. Let us
assume that after introducing a |case| statement and a |pair|
introduction, we become confused about the exact order our variables
are in, so we once again ask Agda to tell us which sub-proofs we need
to give.

\begin{spec}
  swap : Γ ⊢ A × B ⇒ B × A
  swap = abs (case (var zero) pair (?0 ?1))

  ?0 : A , B , A × B , Γ ⊢ B
  ?1 : A , B , A × B , Γ ⊢ A
\end{spec}

This gives us enough information to complete the proof entirely---in
fact, both holes can be trivially filled by the Agsy theorem
prover,\footnote{
  See \url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Auto}.
} resulting in the following proof.

\begin{code}
  swap : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B ⇒ B ⊗ A
  swap = abs (case (var zero) (pair (var (suc zero)) (var zero)))
\end{code}

This proof corresponds to the following typeset proof in natural
deduction style.

\begin{scprooftree}{0.8}
  \AXC{}\RightLabel{AX}
  \UIC{$A , B , \Gamma ⊢ (var \ 1) : B$}
  \AXC{}\RightLabel{AX}
  \UIC{$A , B , \Gamma ⊢ (var \ 0) : A$}
  \RightLabel{$\times$-intro}
  \BIC{$A , B , \Gamma ⊢ (pair \ (var \ 1) \ (var \ 0)) : B × A$}
  \AXC{}\RightLabel{AX}
  \UIC{$A × B , \Gamma ⊢ (var \ 0) : A × B$}
  \RightLabel{$\times$-elim}
  \BIC{$A × B , \Gamma ⊢ (case \ (var \ 0) \ (pair \ (var \ 1) \ (var \ 0))) : B × A$}
  \RightLabel{$\Rightarrow$-intro}
  \UIC{$\Gamma ⊢ abs \ (case \ (var \ 0) \ (pair \ (var \ 1) \ (var \ 0))) : A × B \Rightarrow B × A$}
\end{scprooftree}



\subsection{Exchange as admissible rule}

While the above model of \textbf{IL} suffices if all we wish to model
is the intuitionistic calculus, it poses some problems if we wish to
model substructural logics such as linear logic or the Lambek
calculus.

The reason for this is that the structural rules (exchange, weakening
and contraction) are actually admissible rules for our formulation,
i.e.\ they are implicit in our formulation of \textbf{IL}.

We shall demonstrate this by giving an explicit formulation of the following
exchange principle.\footnote{
  It should be noted that whilst this is a inconvenient formulation of
  the exchange principle to work with, it has a simple proof of admissibility.
}

\begin{scprooftree}{1}
  \AXC{$\Gamma , B , A , \Delta ⊢ C$}
  \UIC{$\Gamma , A , B , \Delta ⊢ C$}
\end{scprooftree}

First we define what exchange at the $i$-th position means on the
level of contexts.

\begin{code}
  Vec-exch : ∀ {k} (i : Fin k) → Vec Type (suc k) → Vec Type (suc k)
  Vec-exch  zero    (A , B , Γ)  = B , A , Γ
  Vec-exch (suc i)  (A , Γ)      = A , (Vec-exch i Γ)
\end{code}

Secondly, we define what an exchange does at the level of de Bruijn
indices. Note that the way we prove this is by return a new index,
together with a proof that the |lookup| function will return the same
result if we use this new index with the exchanged context.

\begin{code}
  lemma-var : ∀ {k} {Γ : Vec Type (suc k)} → ∀ i x → ∃ λ y → Vec.lookup x Γ ≡ Vec.lookup y (Vec-exch i Γ)
  lemma-var {Γ = A , B , Γ} zero     zero           = suc zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc zero)     = zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc (suc x))  = suc (suc x) , refl
  lemma-var {Γ = A , Γ} (suc i)  zero           = zero , refl
  lemma-var {Γ = A , Γ} (suc i)  (suc x)        = Product.map suc id (lemma-var {Γ = Γ} i x)
\end{code}

Finally, we can define exchange as a recursive function over proofs,
where we exchange for every sub-proof until we reach the axioms (or
variables), at which point we use the lemma we defined above.

\begin{code}
  exch : ∀ {k} {Γ : Vec Type (suc k)} {A} → ∀ i → Γ ⊢ A → Vec-exch i Γ ⊢ A
  exch {Γ = Γ} i (var x) with lemma-var {Γ = Γ} i x
  exch {Γ = Γ} i (var x) | y , p rewrite p  = var y
  exch i (abs t)     = abs (exch (suc i) t)
  exch i (app s t)   = app (exch i s) (exch i t)
  exch i (pair s t)  = pair (exch i s) (exch i t)
  exch i (case s t)  = case (exch i s) (exch (suc (suc i)) t)
\end{code}

Note that this is also what makes exchange admissible in our current
formulation: we need to inspect the proof terms in order to be able to
define it.



\subsection{Explicit structural rules}

If we wish to fix our model of \textbf{IL}, we will have to remove the
implicit exchange, weakening and contraction from our axioms, and add
them as axioms in their own right.

The reason that the structural rules are implicitly present in our
logic is that all premises in our inference rules share a context. If
we make sure that every premise of a rule has its own context, and all
contexts are concatinated in the conclusion, this solves our
issue. Another surprising side-effect is that variables are no longer
needed---simply marking the position in a term as a variable is
sufficient. And because of this we can switch to using lists for our
contexts, instead of vectors.

Below you can find a model of \textbf{IL} in which the structural
rules have been made explicit.

\hidden{
\begin{code}
module Explicit where
\end{code}
}

\hidden{
\begin{code}
  infix  4  _⊢_
\end{code}
}

%<*il-explicit>
\begin{code}
  data _⊢_ : ∀ (X : List Type) (A : Type) → Set where
    var   : ∀ {A} → A , ∅ ⊢ A
    abs   : ∀ {X A B} → A , X ⊢ B → X ⊢ A ⇒ B
    app   : ∀ {X Y A B} → X ⊢ A ⇒ B → Y ⊢ A → X ++ Y ⊢ B
    pair  : ∀ {X Y A B} → X ⊢ A → Y ⊢ B → X ++ Y ⊢ A ⊗ B
    case  : ∀ {X Y A B C} → X ⊢ A ⊗ B → A , B , Y ⊢ C → X ++ Y ⊢ C
    weak  : ∀ {X A B} → X ⊢ B → A , X ⊢ B
    cont  : ∀ {X A B} → A , A , X ⊢ B → A , X ⊢ B
    exch  : ∀ {X Y Z W A} →  (X ++ Z) ++ (Y ++ W) ⊢ A
          →  (X ++ Y) ++ (Z ++ W) ⊢ A
\end{code}
%</il-explicit>

Note that the exchange principle we chose here is slightly different
from the exchange principle we proved above, in that it allows the
exchange of entire contexts.

\hidden{
\begin{code}
  exch₀ : ∀ {X A B C} → B , A , X ⊢ C → A , B , X ⊢ C
  exch₀ {X} {A} {B} = exch {∅} {A , ∅} {B , ∅} {X}
\end{code}
}

Using this model we can once again prove our running
example---the commutativity of $\_\!×\!\_$.\footnote{
  Note that we are using a derived inference rule in the proof, exch₀,
  which has the type $B , A , X ⊢ C → A , B , X ⊢ C$, i.e.\ it
  exchanges the first two types in the context.
}%
\footnote{We can also prove $\Gamma ⊢ A \times B \Rightarrow B \times
A$, i.e.\ commutativity in the presence of a context, but for that we
either need a stronger weakening principle or apply the current
weakening principle recursively.}

\begin{code}
  swap : ∀ {A B} → ∅ ⊢ A ⊗ B ⇒ B ⊗ A
  swap = abs (case var (exch₀ (pair var var)))
\end{code}



\subsection{Reification into Agda}

As mentioned in \autoref{sec:Motivation}, another advantage of
modeling logics in Agda is that one can reify terms in the modeled
logic back into Agda terms, and in this way piggyback on Agda's
evaluation mechanisms.
In this section we will present a reification of our explicit
\textbf{IL} terms into Agda terms.

A reification generally consists of two parts:
\begin{itemize}
\item a translation function (written |⟦_⟧|) that sends types in the
  source language to types in the target language;
\item a translation function (written |[_]|) that sends terms
  in the source language to terms in the target language.
\end{itemize}
However, since Agda has no explicit notation for contexts, we can only
define a reification in this style for closed terms. For open terms,
we shall have to provide our own encoding of contexts.

First of all, however, let us look at the translation of our
\textbf{IL} types into Agda's |Set|. Since we are abstracting over a
user-provided type universe $U$, we do not know what types to map
types in this universe to. Therefore, we shall require the user to
provide us with a translation function |⟦_⟧ᵁ|. Once we have this
function, the full translation is trivial.

\hidden{
\begin{code}
  record Reify {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
    field
      ⟦_⟧ : A → B
\end{code}
}

\hidden{
\begin{code}
  ReifyType : Reify Type Set
  ReifyType = record { ⟦_⟧ = ⟦_⟧ }
    where
\end{code}
}

\begin{code}
    ⟦_⟧ : Type → Set
    ⟦ el A    ⟧ = ⟦ A ⟧ᵁ
    ⟦ A ⊗ B   ⟧ = ⟦ A ⟧ × ⟦ B ⟧
    ⟦ A ⇒ B  ⟧ = ⟦ A ⟧ → ⟦ B ⟧
\end{code}

We encounter the first real difficulty when we wish to translate
terms. As mentioned above, Agda has no explicit notation for
contexts. To overcome this, we need to cook up our own encoding:
so what is a context? A context is a list of values of different
types. This means that we can use heterogeneous lists---a list that is
indexed on the type-level by a list of types.

\begin{code}
  data Ctxt : ∀ (X : List Set) → Set₁ where
    ∅ : Ctxt ∅
    _,_ : ∀ {A X} → A → Ctxt X → Ctxt (A , X)
\end{code}

Using this encoding for we can define a few simple function to work on
environments. An |exch| function, which applies our exchange principle
to a context; and a split function, which splits a context in two parts.

\begin{spec}
  Ctxt-exch   : Ctxt ((X ++ Y) ++ (Z ++ W)) → Ctxt ((X ++ Z) ++ (Y ++ W))
  Ctxt-split  : Ctxt (X ++ Y) → (Ctxt X) × (Ctxt Y)
\end{spec}

For brevity's sake, we will omit the definitions for these
function. The interested reader can refer to the code for a full
account. Instead we will present the reader with the full reification
into Agda.

\hidden{
\begin{code}
  private
    open Reify {{...}} using (⟦_⟧)
\end{code}

\begin{code}
  ReifyCtxt : Reify (List Type) (List Set)
  ReifyCtxt = record { ⟦_⟧ = List.map ⟦_⟧ }
\end{code}
}

\hidden{
\begin{code}
  Ctxt-insert : {A : Type} {X Y : List Type} → ⟦ A ⟧ → Ctxt ⟦ X ++ Y ⟧ → Ctxt ⟦ X ++ (A , Y) ⟧
  Ctxt-insert {A} {∅} {Y} A′ E = A′ , E
  Ctxt-insert {A} {B , X} {Y} A′ (B′ , E) = B′ , Ctxt-insert {A} {X} {Y} A′ E

  Ctxt-exch : {X Y Z W : List Type} → Ctxt ⟦ (X ++ Y) ++ (Z ++ W) ⟧ → Ctxt ⟦ (X ++ Z) ++ (Y ++ W) ⟧
  Ctxt-exch {X = ∅} {Y = ∅} {Z} {W} E = E
  Ctxt-exch {X = ∅} {Y = A , Y} {Z} {W} (A′ , E) = Ctxt-insert {A} {Z} {Y ++ W} A′ (Ctxt-exch {∅} {Y} {Z} {W} E)
  Ctxt-exch {X = A , X} {Y} {Z} {W} (A′ , E) = A′ , Ctxt-exch {X} {Y} {Z} {W} E

  Ctxt-split : {X Y : List Type} → Ctxt ⟦ X ++ Y ⟧ → Ctxt ⟦ X ⟧ × Ctxt ⟦ Y ⟧
  Ctxt-split {∅} {Y} E = ∅ , E
  Ctxt-split {A , X} {Y} (A′ , E) with Ctxt-split {X} {Y} E
  ... | Eˣ , Eʸ = ((A′ , Eˣ) , Eʸ)
\end{code}
}

The reification is fairly straightforward: we simply have to the
constructors of our model with the corresponding constructs in
Agda.
In the case of variables, we know that the environment will contain
exactly one value of exactly the right type.
For lambda abstractions, we abstract over a value and then insert it
into the environment (and thus its type into the context).
The translations for the other rules operate on a similar logic.
Note that for binary rules we indeed split the environment in two, and
pass the halves down the corresponding branches of the translation.

\begin{code}
  reify : {A : Type} {X : List Type} → X ⊢ A → Ctxt ⟦ X ⟧ → ⟦ A ⟧
  reify var         (A′ , ∅)  = A′
  reify (abs t)     E         = λ A′ → reify t (A′ , E)
  reify (app s t)   E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = (reify s Eˢ) (reify t Eᵗ)
  reify (pair s t)  E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = (reify s Eˢ , reify t Eᵗ)
  reify (case s t)  E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = case reify s Eˢ of λ{ (A′ , B′) → reify t (A′ , B′ , Eᵗ)}
  reify (weak t)    (A′ , E)  = reify t E
  reify (cont t)    (A′ , E)  = reify t (A′ , A′ , E)
  reify (exch {X} {Y} {Z} {W} t)    E         = reify t (Ctxt-exch {X} {Y} {Z} {W} E)
\end{code}

\noindent
We could see the type $Ctxt \ ⟦ X ⟧ → ⟦ A ⟧$ as Agda's notation of
sequents, and, though in some cases it is more convenient to work on
closed terms, we shall define the reification |[_]| as a function
returning this type (as a simple alias).

\begin{code}
  [_] : {A : Type} {X : List Type} → X ⊢ A → (Ctxt ⟦ X ⟧ → ⟦ A ⟧)
  [_] = reify
\end{code}

\noindent
We can translate our running example into Agda. Note that we insert
the empty context, since our example is a closed term.

\begin{code}
  swap′ : ∀ {A B} → ⟦ A ⟧ × ⟦ B ⟧ → ⟦ B ⟧ × ⟦ A ⟧
  swap′ {A} {B} = [ swap {A} {B} ] ∅
\end{code}
