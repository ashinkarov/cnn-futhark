We thank the reviewers for their comments. Before getting responding to specific
questions below, we wish to explain the intent of our paper in a way that we
perhaps we failed to do in the paper itself.

Our paper investigates the use of Agda as a practical tool for scientic
programming, covering the span from problem specification using rank
polymorhism, to transformation via AD, to optimisation and code generation. Not
all parts of the whole are equally completely specified: while rank polymorphism
is the most developed and fully verified part, the AD transformation only
verifies the absence of bounds errors, and code generation does indeed contain
the aptly termed `String → String` monster.

In an ideal world, all parts would of course come with a formal specification
and accompanying proof, but in practice some parts remain an entirely separate
(and nontrivial) research effort to verify functionally correct (such as AD),
while others can be handled using known techniques (such as code generation),
but are somewhat time consuming. We wish to show that even in those cases where
resources preclude full verification, Agda can still be used as a practical
tool, with full verification employed where it is deemed desirable and
practical. This is what we mean by the somewhat oblique "correctness invariants
of our choice" in the abstract.

## Answers to specific questions and remarks

### Reviewer A

### Reviewer B

### Reviewer C

### Reviewer D

#### On the artifact

The artifact is indeed not in a portable state, as we did not anticipate
reviewers would desire to run it at this stage in the process (but are certainly
pleasantly surprised!). The reason is that due to the somewhat complex
dependencies (GPUs, Python library infrastructure), Docker is the most
accessible way to package it, but the GPU-equipped system on which we did our
work does not support Docker. This will of course be rectified in case the paper
is accepted.
