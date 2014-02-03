## Modelling Substructural Logics in Agda

#### Abstract

> In this paper, we will examine models of substructural logics in
> Agda. The reason for this is that most existing models formalise
> intuitionistic logic and are entirely unsuitable to modelling
> substructural logics. In recent years, however, substructural logics
> have seen a surge in usage.
>
> Concretely we present the reader with an explicit model of
> intuitionistic logic, and derive models for linear logic and the
> Lambek-Grishin calculus. In addition, we show how to reify proofs in
> these logics into terms in Agda. All this is implemented as an Agda
> library, which is made available on GitHub.

> Finally we conclude with an example from formal linguistics in which
> we demonstrate one possible usage of our implemented Agda library.

#### Technical Details

This repository contains the sources for the *[Modelling Substructural Logics in Agda](/SubstructuralLogicsInAgda.pdf?raw=true)*.
The `paper` sub-directory contains the literate Agda files that make up the paper.
The `code` sub-directory contains the extracted Agda source code.

Some notes:

  - the code was written for use with [version 0.7 of the Agda standard
    library](http://www.cse.chalmers.se/~nad/software/lib-0.7.tar.gz);

  - the code is released under an [MIT license](code/LICENSE);

  - the paper is compiled using [lhs2TeX](http://www.andres-loeh.de/lhs2tex/);

  - compilation of the paper and extraction of the code is facilitated
    using a [rake](http://rake.rubyforge.org/) build script (call
    `rake paper` and `rake code`).
