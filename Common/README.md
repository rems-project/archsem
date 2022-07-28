This folder contain a small Coq library `SSCCommon` (for System Semantic Coq
Common), that is intended to be a small extra standard library for this project.

The goal is that all generic lemmas that are not specific to a model end-up
here, as well as all generic proof-automation, notations, and type classes.

This could either things that could be exported to one of the used library like
stdpp, bbv, bitvectors, hahn, hammer-tactics ... or things required to make
multiple libraries interact together.

System-Semantic-Coq aim to be easily interoperable with the Iris ecosystem, that
is why stdpp is intended to be the main focus, in particular when there is two
version of a concept in multiple sources we will try to use the stdpp one. In
such a case SSCCommon will try to define lemmas and proof-automation to get as
smooth as possible interoperability with the other version of the concept.
