Verifying Datalog Optimizations in Rocq
=======================================

We will be formalizing the results in
[https://arxiv.org/abs/2202.10390](Wang et al's paper). Specifically,
our goal is to create a mechanized proof of the FGH Rule, and
hopefully get to the magic sets example in the appendix.


## Running and Setup
This repo depends on our fork of a
[https://github.com/audreyseo/datalogo](Datalog formalization). To
install all the dependencies using the OCaml package manager, opam,
use the following. (For more on installing Rocq using opam, see
[https://coq.inria.fr/opam-using.html](the docs).)


```sh
opam switch create datalog 4.10.0
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.9.1
opam pin add coq-equations 1.2.1+8.9
opam pin add coq-mathcomp-ssreflect 1.8.0
opam pin add coq-mathcomp-finmap 1.4.0
```

These dependencies are required to build the Datalog formalization.

From the project root directory, run `./bin/setup.sh`. This should
pull the datalogo sources into the `datalogo/` folder, making them
available, as well as install them for you.

You should then be able to run make in the project root directory.
