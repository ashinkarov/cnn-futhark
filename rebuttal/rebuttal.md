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
of our choice" in the abstract. Full verification of the entire pipeline is
naturally an important avenue for future work.

We agree that dependent types for index safety trace back to Xi and Pfenning,
and that our AD transformation is hardly state of the art, but our contribution
lies not just in reiterating these known ideas, but in engineering a practical
pipeline: from dependently-typed specifications in Agda to performant code
generation via Futhark, supporting non-trivial array programs and
transformations like AD.

## Answers to specific questions and remarks

### Reviewer A

### Reviewer B

### Reviewer C

#### Improving the benchmarks

The JIT behaviour of industry-standard machine learning tools do pose challenges
for benchmarking, *particularly* when the MNIST benchmark is by modern standards
rather small, so the setup time becomes dominant. This is why we have isolated
it in our measurements. Alternatively, we could inflate the number of training
epochs to inflate the training time, although this is unlikely to actually
improve the training result, and so feels artificial. The purpose of our
experiment is not to provide comprehensive evidence for outperforming
TensorFlow, but to show that the performance of our system seems sufficient to
be useful.

#### Correctness of translation to Futhark

There are no correctness guarantees in the present work, largely for practical
reasons. Since Futhark's dynamic semantics are quite straightforward and similar
to those of Agda, verification is possible via known techniques, but requires
somewhat tedious modelling Futhark in Agda. The main challenge would be
verifying the instantiation of rank polymorphic operations to explicit uses of
`map`, as Futhark does not support rank polymorphism.

### Reviewer D

#### On the artifact

The artifact is indeed not in a portable state, as we did not anticipate
reviewers would desire to run it at this stage in the process (but are certainly
pleasantly surprised!). The reason is that due to the somewhat complex
dependencies (GPUs, Python library infrastructure), Docker is the most
accessible way to package it, but the GPU-equipped system on which we did our
work does not support Docker. This will of course be rectified in case the paper
is accepted.
