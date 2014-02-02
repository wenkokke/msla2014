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

\subsection{Modelling IL with de Bruijn indices}

If we wish to model the intuitionistic calculus, we first have to do
something about our notation. The reason for this is that the usual
notation with named variables introduces a whole host of problems,
such as checking for proper scopal and binding relations.\footnote{
  See \citet{erdi2013} for an implementation that uses variable names.
}

The canonical solution to this is a notation introduced in
\citet{debruijn1972}, where we instead of using variable names for
binding, we will use numbers. The semantics of these numbers will be
that they tell you how many lambdas up the variable is bound (or, from
the perspective of logic, they are indices into the context). See
\autoref{fig:namedvsdebruijn} for an example of how terms in named
notation compare to terms in de Bruijn notation.

\begin{figure}[h]
  \centering
  \begin{tabular}{l l}
     Named & de Bruijn
  \\ \hline
  \\ $\lambda x \to x$
   & $\textcolor{Maroon}{\lambda}\ \textcolor{Maroon}{0}$
  \\ $\lambda x \to \lambda y \to x$
   & $\textcolor{Maroon}{\lambda}\ \textcolor{MidnightBlue}{\lambda}\ \textcolor{Maroon}{1}$
  \\ $\lambda x \to \lambda y \to \lambda z \to x \ z \ (y \ z)$
   & $\textcolor{Maroon}{\lambda}\ \textcolor{MidnightBlue}{\lambda}\ \textcolor{ForestGreen}{\lambda}\
      \textcolor{Maroon}{2}\ \textcolor{ForestGreen}{0}\ (\textcolor{MidnightBlue}{1}\ \textcolor{ForestGreen}{0})$
  \end{tabular}
  \caption{Named notation versus de Bruijn notation \citep{mazzoli2013}.}
  \label{fig:namedvsdebruijn}
\end{figure}

As a preparation for the modelling of the intuitionistic calculus
in Agda, we can formulate the de Bruijn notation as a set of
inference rules; the result of this can be seen in \autoref{fig:debruijnaslogic}.

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

As a first step of we will need a representation of the type
language/formulas that we wish to model. In this paper we will limit
ourselves to formulas containing implication (written
$\_\!\Rightarrow\!\_$) and conjunction (written $\_\!\times\!\_$).

In addition, we will abstract over some type $U$. The reason for
this is that we do not want to be forced to specify the atomic
types---instead we shall allow the user to provide their own universe
of atomic types.\footnote{
  For an example of this, see \autoref{sec:example}.
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

All that is left for us to do, is to translate our inference rules as
presented in \autoref{fig:debruijnaslogic} to an Agda data type. The
translation is almost verbatim, save that we write
$\_\!\rightarrow\!\_$ for the meta-logical implication (instead of a
horizontal line) and---due to the close relationship between proofs
and terms---the term constructors (|var|, |abs|, |case|, et cetera) become
constructors of our data type.

We use vectors\footnote{
  See \url{http://agda.github.io/agda-stdlib/html/Data.Vec.html\#604}.
} to model contexts, and finite sets\footnote{
  See \url{http://agda.github.io/agda-stdlib/html/Data.Fin.html\#775}.
} to model the de Bruijn indices.
In this way we can ensure that every variable is bound,\footnote{
  The reason this works is because vectors encode lists of a fixed
  length $k$, and finite sets encode a data type with precisely $k$
  inhabitants.
} either to a type in the context or to a lambda
abstraction.\footnote{
  It should be stated that throughout this paper we will use an
  alternative notation for lists and vectors, using $\_,\_$ for the
  cons operator and $∅$ for the empty list (or vector), as we deem
  this notation to be better suited to  sequent contexts. For the
  concatenation of contexts, however, we will stick to using
  $\_\!\plus\!\_$, as usual.
}
Because of this invariant we can define a safe |lookup| function as
follows.

\begin{spec}
  lookup : Fin k → Vec A k → A
  lookup  zero     (A , Γ)  = A
  lookup  (suc x)  (A , Γ)  = lookup x Γ
\end{spec}

And using this function we can present a full formalisation of our
inference rules.

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

\noindent
In \autoref{sec:Introduction} we mentioned that one of the advantages
of modelling a logic in Agda was the use of Agda's interactive proof
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

\noindent
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

\noindent
This gives us enough information to complete the proof entirely---in
fact, both holes can be trivially filled by the Agsy theorem
prover,\footnote{
  See \url{http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Auto}.
} resulting in the following proof.

\begin{code}
  swap : ∀ {A B} {k} {Γ : Vec Type k} → Γ ⊢ A ⊗ B ⇒ B ⊗ A
  swap = abs (case (var zero) (pair (var (suc zero)) (var zero)))
\end{code}

\noindent
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
model substructural logics such as linear logic.

The reason for this is that the structural rules (exchange, weakening
and contraction) are admissible rules in our formulation, i.e.\ they
are implicitly present in our formulation of \textbf{IL}.

We shall demonstrate this by giving an explicit formulation of the
following simple exchange principle: exchange at the $i$-th position.

\begin{scprooftree}{1}
  \AXC{$\Gamma , B , A , \Delta ⊢ C$}
  \UIC{$\Gamma , A , B , \Delta ⊢ C$}
\end{scprooftree}

\noindent
We can define this principle in three steps. First we define what
exchange does on the level of contexts.

\begin{code}
  Vec-exch : ∀ {k} (i : Fin k) → Vec Type (suc k) → Vec Type (suc k)
  Vec-exch  zero    (A , B , Γ)  = B , A , Γ
  Vec-exch (suc i)  (A , Γ)      = A , (Vec-exch i Γ)
\end{code}

\noindent
Secondly, we define what an exchange does at the level of the
indices. Note that the way we implement this is by returning a new
index, paired with a proof that the |lookup| function will return
the same result when we use this new index with the exchanged context,
as when we use the old index with the old context.

\begin{code}
  lemma-var : ∀ {k} {Γ : Vec Type (suc k)} → ∀ i x → ∃ λ y → Vec.lookup x Γ ≡ Vec.lookup y (Vec-exch i Γ)
  lemma-var {Γ = A , B , Γ} zero     zero           = suc zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc zero)     = zero , refl
  lemma-var {Γ = A , B , Γ} zero     (suc (suc x))  = suc (suc x) , refl
  lemma-var {Γ = A , Γ} (suc i)  zero           = zero , refl
  lemma-var {Γ = A , Γ} (suc i)  (suc x)        = Product.map suc id (lemma-var {Γ = Γ} i x)
\end{code}

\noindent
Finally, we can define exchange as a recursive function over proofs,
where we recursively apply exchange to every sub-proof until we reach
the axioms (or variables), at which point we use the lemma we defined
above.\footnote{
  Note that this is also what makes exchange admissible instead of
  derivable: we need to inspect the proof terms in order to be able
  to define it.
}

\begin{code}
  exch : ∀ {k} {Γ : Vec Type (suc k)} {A} → ∀ i → Γ ⊢ A → Vec-exch i Γ ⊢ A
  exch {Γ = Γ} i (var x) with lemma-var {Γ = Γ} i x
  exch {Γ = Γ} i (var x) | y , p rewrite p  = var y
  exch i (abs t)     = abs (exch (suc i) t)
  exch i (app s t)   = app (exch i s) (exch i t)
  exch i (pair s t)  = pair (exch i s) (exch i t)
  exch i (case s t)  = case (exch i s) (exch (suc (suc i)) t)
\end{code}



\subsection{Explicit structural rules}

If we wish to make our model of \textbf{IL} suitable for modelling
substructural logics, we will have to remove the implicit exchange,
weakening and contraction from our axioms, and add them as axioms in
their own right.

The reason that the structural rules are implicitly present in our
logic, is that all premises in our inference rules share a context. If
we make sure that every premise of a rule has its own context, and all
contexts are concatenated in the conclusion, we will have solved our
issue. A surprising side-effect of this is that variables will no longer
be needed---simply marking the position in a term as an axiom is
sufficient. As a consequence of this, we can stop using vectors for
modelling contexts, and switch to using simple lists.

Below you will find a model of \textbf{IL} in which the structural
rules have been made explicit.\footnote{
  Note that the exchange principle we chose here is slightly different
  from the exchange principle we proved above, in that it allows the
  exchange of entire contexts.
}

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
    weak  : ∀ {X Y A} → X ⊢ A → X ++ Y ⊢ A
    cont  : ∀ {X A B} → A , A , X ⊢ B → A , X ⊢ B
    exch  : ∀ {X Y Z W A} →  (X ++ Z) ++ (Y ++ W) ⊢ A
          →  (X ++ Y) ++ (Z ++ W) ⊢ A
\end{code}
%</il-explicit>

\hidden{
\begin{code}
  exch₀ : ∀ {X A B C} → B , A , X ⊢ C → A , B , X ⊢ C
  exch₀ {X} {A} {B} = exch {∅} {A , ∅} {B , ∅} {X}
\end{code}
}

Using this model we can once again prove our running
example---the commutativity of $\_\!×\!\_$.\footnote{
  In the proof we use a derived inference rule, exch₀, which has the
  type $B , A , X ⊢ C → A , B , X ⊢ C$, i.e.\ it exchanges the first
  two types in the context.
}

\begin{code}
  swap : ∀ {X A B} → X ⊢ A ⊗ B ⇒ B ⊗ A
  swap {X} {A} {B} = abs (case var (exch₀ (pair var (weak {A , ∅} {X} var))))
\end{code}



\subsection{Reification into Agda}

Another advantage of modelling logics we mentioned in
\autoref{sec:Introduction} is that one can reify proofs in the
modelled system back into Agda terms, and in this way piggyback on
Agda's evaluation mechanisms.

In this section we will present a reification of our explicit
\textbf{IL} terms into Agda terms. But first we will give a general
definition of what a reification is.

A reification generally consists of two parts:\footnote{
  Implicit in the below definition are the data types for the types of
  the source and target logics, and the data types for the proofs or
  terms of the source and target logics.
}
\begin{itemize}
\myitem a translation function (written |⟦_⟧|) that sends types in the
  source logic to types in the target logic;
\myitem a translation function (written |[_]|) that sends terms in the
  source logic to terms in the target logic.
\end{itemize}

\noindent
First of all, let us look at the translation of our \textbf{IL} types
into Agda's |Set|. Since we cannot know what to map types in the
user-provided universe $U$ to, we shall require the user to provide us
with a translation function |⟦_⟧ᵁ|.
With this function, the full translation is trivial.

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

\noindent
Next we will look at the translation of proofs into Agda terms.
Unfortunately for us, Agda has no explicit notion of contexts. We
could therefore require that the proofs we translate are closed terms,
i.e.\ of the form $\emptyset \vdash A$.
Another solution, however, is to invent our own encoding of contexts.

So let us ask ourselves, what is a context? The answer: a context is a
list of types associated with a list of values of those types. Or to
phrase it the other way around: a list of values typed by a list of
types. This means we can use heterogeneous lists \citep{kiselyov2004}
to encode our contexts.

\begin{code}
  data Ctxt : ∀ (X : List Set) → Set₁ where
    ∅ : Ctxt ∅
    _,_ : ∀ {A X} → A → Ctxt X → Ctxt (A , X)
\end{code}

\noindent
Using this definition, our representation of a sequent $X ⊢ A$ in Agda
will be the type $Ctxt \ ⟦ X ⟧ → ⟦ A ⟧$.

Next we need a few simple functions to work with these
contexts. Specifically, an |exch| function, which applies our exchange
principle to the context, and a split function, which splits a context
into two parts (for binary rules).

\begin{spec}
  Ctxt-exch   : Ctxt ((X ++ Y) ++ (Z ++ W)) → Ctxt ((X ++ Z) ++ (Y ++ W))
  Ctxt-split  : Ctxt (X ++ Y) → (Ctxt X) × (Ctxt Y)
\end{spec}

\noindent
For brevity's sake, we will omit the definitions for these
functions. The interested reader can refer to the code for a full
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

The reification is fairly straightforward: we simply have to map the
constructors of our model to the corresponding constructs in Agda.

In the case of \emph{variables}, we know that the environment will
contain exactly one value of exactly the right type, for \emph{lambda
abstractions}, we abstract over a value, which we insert into the
context, et cetera.
Note that for binary rules we have to split the context, and pass the
two parts down the corresponding branches of the proof during
reification.

\begin{code}
  reify : {A : Type} {X : List Type} → X ⊢ A → (Ctxt ⟦ X ⟧ → ⟦ A ⟧)
  reify var         (x , ∅)   = x
  reify (abs t)     E         = λ x → reify t (x , E)
  reify (app s t)   E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = (reify s Eˢ) (reify t Eᵗ)
  reify (pair s t)  E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = (reify s Eˢ , reify t Eᵗ)
  reify (case s t)  E         with Ctxt-split E
  ... | Eˢ , Eᵗ               = case reify s Eˢ of λ{ (x , y) → reify t (x , y , Eᵗ)}
  reify (weak {X} s)    E         with Ctxt-split {X} E
  ... | Eˢ , Eᵗ               = reify s Eˢ
  reify (cont t)    (x , E)   = reify t (x , x , E)
  reify (exch {X} {Y} {Z} {W} t)    E         = reify t (Ctxt-exch {X} {Y} {Z} {W} E)
\end{code}

\noindent
We can now define the reification function |[_]| as a simple alias.

\begin{code}
  [_] : {A : Type} {X : List Type} → X ⊢ A → (Ctxt ⟦ X ⟧ → ⟦ A ⟧)
  [_] = reify
\end{code}

\noindent
And translate our running example into Agda. Note that we can already
insert the empty context, as our example is a closed term.

\begin{code}
  swap′ : ∀ {A B} → ⟦ A ⟧ × ⟦ B ⟧ → ⟦ B ⟧ × ⟦ A ⟧
  swap′ {A} {B} = [ swap {∅} {A} {B} ] ∅
\end{code}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
