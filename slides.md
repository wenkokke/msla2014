# Lambda Calculus

\begin{latex}
\only<1>{%
$$
    s , t ::= x \ | \ \lambda x . t \ | \ (s \ t)
$$
}

\only<2>{
\begin{prooftree}
\AXC{}
\RightLabel{\scriptsize var}
\UIC{$x$}
\end{prooftree}

\noindent
\begin{minipage}[s]{.5\textwidth}
  \begin{prooftree}
    \AXC{$t$}
    \RightLabel{\scriptsize abs}
    \UIC{$\lambda x . t$}
  \end{prooftree}
\end{minipage}%
\begin{minipage}[s]{.5\textwidth}
  \begin{prooftree}
    \AXC{s}
    \AXC{t}
    \RightLabel{\scriptsize app}
    \BIC{$(s \ t)$}
  \end{prooftree}
\end{minipage}
}

\only<3>{
\noindent
\begin{minipage}[s]{.3\textwidth}
\centering
  \begin{prooftree}
    \AXC{}
    \RightLabel{\scriptsize var}
    \UIC{$x$}
    \RightLabel{\scriptsize abs}
    \UIC{$\lambda x . x$}
  \end{prooftree}
\end{minipage}%
\begin{minipage}[c]{.3\textwidth}
\centering
  but also
\end{minipage}%
\begin{minipage}[s]{.3\textwidth}
\centering
  \begin{prooftree}
    \AXC{}
    \RightLabel{\scriptsize var}
    \UIC{$x$}
    \AXC{}
    \RightLabel{\scriptsize var}
    \UIC{$x$}
    \RightLabel{\scriptsize app}
    \BIC{$(x \ x)$}
    \RightLabel{\scriptsize abs}
    \UIC{$\lambda x . (x \ x)$}
  \end{prooftree}
\end{minipage}%
}
\end{latex}



# Simply-Typed Lambda Calculus

\begin{latex}
\only<1>{%
\begin{align*}
   A , B &::= \mathcal{A} \ | \ A \Rightarrow B
\\ s , t &::= x \ | \ \lambda x . t \ | \ (s \ t)
\end{align*}
}

\only<2>{
\begin{prooftree}
  \AXC{$x : A \in \Gamma$}
  \RightLabel{\scriptsize var}
  \UIC{$\Gamma \fCenter x : A$}
\end{prooftree}

\noindent
\begin{minipage}[s]{0.4\textwidth}
  \begin{prooftree}
    \AXC{$\Gamma , x : A \fCenter t : B$}
    \RightLabel{\scriptsize abs}
    \UIC{$\Gamma \fCenter \lambda x . t : B$}
  \end{prooftree}
\end{minipage}%
\begin{minipage}[s]{0.6\textwidth}
  \begin{prooftree}
    \AXC{$\Gamma \fCenter s : A \Rightarrow B$}
    \AXC{$\Gamma \fCenter t : A$}
    \RightLabel{\scriptsize app}
    \BIC{$\Gamma \fCenter (s \ t) : B$}
  \end{prooftree}
\end{minipage}
}

\only<3>{
\noindent
\begin{minipage}[s]{.4\textwidth}
\centering
  \begin{prooftree}
    \AXC{}
    \RightLabel{\scriptsize var}
    \UIC{$\Gamma , x : \mathcal{A} \fCenter x : \mathcal{A}$}
    \RightLabel{\scriptsize abs}
    \UIC{$\Gamma \fCenter \lambda x . x : \mathcal{A} \Rightarrow \mathcal{A}$}
  \end{prooftree}
\end{minipage}%
\begin{minipage}[s]{.2\textwidth}
\centering
    and
\end{minipage}%
\begin{minipage}[s]{.4\textwidth}
\centering
  \begin{prooftree}
    \AXC{}
    \RightLabel{\scriptsize var}
    \UIC{$\Gamma , x : \mathcal{B} \fCenter x : \mathcal{B}$}
    \RightLabel{\scriptsize abs}
    \UIC{$\Gamma \fCenter \lambda x . x : \mathcal{B} \Rightarrow \mathcal{B}$}
  \end{prooftree}
\end{minipage}%
}
\end{latex}



# Polymorphic Lambda Calculus

\begin{latex}
\only<1>{%
\begin{align*}
   A , B &::= \mathcal{A} \ | \ A \Rightarrow B \ | \ \alpha \ | \ \forall \alpha . B
\\ s , t &::= x \ | \ \lambda x . t \ | \ (s \ t) \ | \ \Lambda \alpha . t \ | \ (t \ A)
\end{align*}
}

\only<2>{
$$\vdots$$

\noindent
\begin{minipage}[s]{0.4\textwidth}
  \begin{prooftree}
    \AXC{$\Gamma \fCenter t : B$}
    \RightLabel{\scriptsize $\Lambda$-abs}
    \UIC{$\Gamma \fCenter \Lambda \alpha . t : \forall \alpha . B$}
  \end{prooftree}
\end{minipage}%
\begin{minipage}[s]{0.6\textwidth}
  \begin{prooftree}
    \AXC{$\Gamma \fCenter t : \forall \alpha . B$}
    \RightLabel{\scriptsize $\Lambda$-app}
    \UIC{$\Gamma \fCenter (t \ A) : B [ \alpha \mapsto A ]$}
  \end{prooftree}
\end{minipage}
}
\end{latex}



# Dependently-Typed Lambda Calculus

$$
    s , t , A , B ::= x \ | \ \lambda x . t \ | \ (s \ t) \ | \ldots
$$

\begin{prooftree}
  \AXC{$x \in A$}
  \RightLabel{\scriptsize var}
  \UIC{$x : A$}
\end{prooftree}



# Π-Types

$$
    s , t , A , B ::= \ldots \ | \ (\Pi \, x : A)(B \ x)
$$

\begin{prooftree}
  \AXC{$x : A$}
  \AXC{$A : Set$}
  \AXC{$B \ x : Set$}
  \RightLabel{\scriptsize $\Pi$-form}
  \TIC{$(\Pi \, x : A)(B \ x)$}
\end{prooftree}

\begin{prooftree}
  \AXC{$x : A$}
  \AXC{$t \ x : B \ x$}
  \RightLabel{\scriptsize $\Pi$-intro}
  \BIC{$\lambda x . t : (\Pi \, x : A)(B \ x)$}
\end{prooftree}

\begin{prooftree}
  \AXC{$s : (\Pi \, x : A)(B \ x)$}
  \AXC{$t : A$}
  \RightLabel{\scriptsize $\Pi$-elim}
  \BIC{$s \ t : B \ t$}
\end{prooftree}



# Π-Types (Regaining Function Types)

$$
    A \to B ::= (\Pi \, x : A)B
$$

\begin{prooftree}
  \AXC{$A : Set$}
  \AXC{$B : Set$}
  \RightLabel{\scriptsize $\to$-form}
  \BIC{$A \to B$}
\end{prooftree}

\begin{prooftree}
  \AXC{$x : A$}
  \AXC{$t \ x : B$}
  \RightLabel{\scriptsize $\to$-intro}
  \BIC{$\lambda x . t : A \to B$}
\end{prooftree}

\begin{prooftree}
  \AXC{$f : A \to B$}
  \AXC{$x : A$}
  \RightLabel{\scriptsize $\to$-elim}
  \BIC{$f \ x : B$}
\end{prooftree}

Might as well...
$$
    (x : A) \to B \ x ::= (\Pi \, x : A)(B \ x)
$$



# Π-Types (Regaining Universal Quantification)

$$
    s , t , A , B ::= \ldots \ | \ \forall \, x \to B
$$

\begin{prooftree}
  \AXC{$x : A$}
  \AXC{$B : A \to Set$}
  \RightLabel{\scriptsize $\forall$-form}
  \BIC{$\forall \, x \to B$}
\end{prooftree}

$$\vdots$$



# Σ-Types

$$
    s , t , A , B ::= \ldots \ | \ \langle s , t \rangle \ | \ (\Sigma \, x : A)(B \ x)
$$

\begin{prooftree}
  \AXC{$x : A$}
  \AXC{$A : Set$}
  \AXC{$B \ x : Set$}
  \RightLabel{\scriptsize $\Sigma$-form}
  \TIC{$(\Sigma \, x : A)(B \ x)$}
\end{prooftree}

\begin{prooftree}
  \AXC{$s : A$}
  \AXC{$t : B \ s$}
  \RightLabel{\scriptsize $\Sigma$-intro}
  \BIC{$\langle s , t \rangle : (\Sigma \, x : A)(B \ x)$}
\end{prooftree}

\begin{prooftree}
  \AXC{$\langle x , y \rangle : (\Sigma \, x : A)(B \ x)$}
  \AXC{$f \ x \ y : C \ x \ y$}
  \RightLabel{\scriptsize $\Sigma$-elim}
  \BIC{$f \ x \ y : C \ x \ y$}
\end{prooftree}



# Σ-Types (Regaining Pairs)

$$
    A \times B ::= (\Sigma \, x : A)B
$$

\begin{prooftree}
  \AXC{$A : Set$}
  \AXC{$B : Set$}
  \RightLabel{\scriptsize $\times$-form}
  \BIC{$A \times B$}
\end{prooftree}

\begin{prooftree}
  \AXC{$s : A$}
  \AXC{$t : B$}
  \RightLabel{\scriptsize $\times$-intro}
  \BIC{$\langle s , t \rangle : A \times B$}
\end{prooftree}

\begin{prooftree}
  \AXC{$\langle x , y \rangle : A \times B$}
  \AXC{$f \ x \ y : C$}
  \RightLabel{\scriptsize $\times$-elim}
  \BIC{$f \ x \ y : C$}
\end{prooftree}



# Just Add Sugar

\pause
\ExecuteMetaData[slides/code.tex]{sigma}
\pause
\ExecuteMetaData[slides/code.tex]{pair}
