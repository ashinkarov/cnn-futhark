<!--
```
{-# OPTIONS  --backtracking-instance-search #-}
module _ where
```
-->
This is an overview of the Agda code that accompanies
the "Correctness meets high performance in Agda" paper.

We used Agda version 2.7.0.1, and the standard library version
2.1.1.


# Agda Framework

## Array operations

The core of the development is operations on multi-dimensional
arrays (ML community calls them tensors).  Arrays are modeled
as functions from indices to values, where array shape is
represented as `List ℕ`.  Indices are indexed by shapes and
for a given shape $s$, they are encoded as `All Fin s`.

The key strength of the encoding is that by abstracting
shapes we get rank-polymorphism, which helps to keep basic
array combinators generic.

All the definitions can be found in `Ar.agda`.

```
open import Ar
```

## CNN

Our running example is a convolutional neural network that
recognises hand-written digits that is trained on the MNIST
data.  In the `CNN.agda` we define a few network-specific
combinators and the network.

```
import CNN
```

# DSL

In order to define AD, we wrap define an intrinsically-shaped
DSL that operates on arrays by wrapping key array combinators.

The definition of the DSL can be found in `Lang.agda`.

```
open import Lang
```

We define parallel substitution and weakening in the usual way.
We also define HOAS-like syntax for our DSL that expands into
terms with de-Bruijn varables.  The syntax is based on Agda's
instance search that we use to precompute context prefixes.
As a result, we end up with the following definition, where
`Let`, `Imap` and `Lcon` are syntactical wrappers.

```
module DSLNetwork where
  open import Data.List using (List; []; _∷_)
  open import Relation.Binary.PropositionalEquality
  open Syntax
  open Primitives

  cnn′ : E _ _
  cnn′ = Lcon (  ar (28 ∷ 28 ∷ []) ∷ ar (6 ∷ 5 ∷ 5 ∷ [])
               ∷ ar (6 ∷ [])       ∷ ar (12 ∷ 6 ∷ 5 ∷ 5 ∷ [])
               ∷ ar (12 ∷ [])      ∷ ar (10 ∷ 12 ∷ 1 ∷ 4 ∷ 4 ∷ [])
               ∷ ar (10 ∷ [])      ∷ ar (10 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []) 
               ∷ [])
              (ar ([])) ε
        λ inp k₁ b₁ k₂ b₂ fc b target → 
        Let c₁₁ := mconv inp k₁ b₁  In
        Let c₁  := logistic c₁₁ In
        Let s₁  := (Imap {s = 6 ∷ []} λ i → avgp₂ 12 12 (sel c₁ i)) In
        Let c₂₁ := mconv s₁ k₂ b₂ In
        Let c₂  := logistic c₂₁ In
        Let s₂  := (Imap {s = 12 ∷ 1 ∷ []} λ i → avgp₂ 4 4 (sel c₂ i)) In
        Let o₁  := mconv s₂ fc b In
        Let o   := logistic o₁ In
        Let e   := meansqerr target o In
        e
```

## Evaluation

We give semantics to our DSL by interpretig it into Agda terms.
See `Eval.agda` for details.  We use shape-safe environment-passing
interpreter defined in the usual way.  This has at least two purposes
  1. This ensures that our DSL is consistent with tensor operations
     that we defined earlier;
  2. We use this interpretation that guarantee that our optimisations
     are semantics-preserving.

```
import Eval
```

## AD

One of the main reasons to define the DSL in the first place is
the ability to perform automatic differentiation internally within
Agda.  This is done in file `Grad.agda` (note that some two of the
definitions are marked as terminating, because Agda's termination
checker does not see that they are safe; termination of these
definitions is given in the file `GradTerm.agda`).

```
open import Grad
open import GradTerm renaming (grad to term-grad)
```

AD is defined in reverse mode as a function from the DSL expression 
(e : E Γ (ar s)), seed value (s : E Γ (ar s)) and the inital environment
(EE Γ Γ) into the environment (EE Γ Γ).  The environment EE Γ Δ is a list
of (E Δ)s of the types given by Γ.  Environment keeps the
values of partial derivatives of all the variables in the context Γ,
at it is set to all zeroes at the initial call.

The interesting feature of the environment construction is that additionally
to the values, we keep a chain of `let`s that make it possible to share
computations that may be reused in the environment elements.  This is
important for performance reasons.

The core gradient computation is rather short, taking about 30 lines of code.

## Optimisation

Expressions that come out of AD are often inefficient if being executed
directly.  Therefore, we design an optimiser which eliminates useless
computations in a semantics preserving way.

### Abstract Reals

We do this by defining an abstract notion of real numbers which is given
by a set ℝ, operations such as +, -, exp, etc; and some properties such
as neutrality of zero for + and neutrality of 1 for *.  These definitions
can be found in `Real.agda` and we use them when proving some of the
optimisations.

```
open import Real
```

### Optimiser

Optimisations can be found in `Opt.agda` where `opt` is an entry point.

```
open import Opt
```

From the `opt` signature it can be seen that not only it computes the
optimised expression but also the proof that this expression evaluates
to the same value (pointwise) as the original one under our standard
interpretation.  Note that `opt` is parametrise by Reals, as the result
of optimisations does not depend on the encoding.

```
module OptExample (r : Real) (rp : RealProp r) where
  open import Data.Product
  open import Eval r

  opt′ : (e : E Γ is) → ∃ λ e′ → (e ≈ᵉ e′)
  opt′ = opt r rp

```

### Deduplication

We found out that it would be usefult to have a deduplication for
the expressions in the let chains, as mathematical rule for derivarives
of logistics function computes logisitcs function of the original argument.
Deduplication is a generally useful optimisation to have, and its main
functionality is given in `Replace.agda` where we traverse the term
and compare if one expression is equal to the other one.  Extraciton
file contains more details on how it is used.

```
open import Replace
```

# Code Generation

After we have computed AD and optimised the result, we translate
the resulting expression inot Futhark that takes care of generating
efficient executables.

## Translation to Futhark

As our DSL is quite simple, compilation into backends is generally
straight-forward.  One non-trivial problem that we identified is
that naive code generation often produces expressions such as
`sel (imap λ i → e) j`, i.e. immediate elimination of the array
that has been constructed.  One could hope that a backend could
eliminate such a pattern reducing this to something like:
`let x = i in e[ i ≔ x]`.  Howeve, the compiler is actually
materialising the entire array in memory prior selecting a single
element, which has a dramatic input on performance.

We solve this problem in an NBE style, reresenting arrays as Agda
functions from symbolic indices to symbolic values.  By doing so
we merge normalisation and compilation into a single extraction step.
The overall code is straight-forward modulo the necessity to deal
with fresh variables, which are handled by the state monad(s).

The code can be found in `Futhark.agda`.

```
open import Futhark
```

## Extraction

The final step of the code generation is extraction which involves
running optimisations, handling names of the external variables
in the context and generating Futhark code.  These steps are
implemented in `Extration.agda`.

```
open import Extraction
```

Code generation for our running example looks as follows:

```
module ExtractionDemo where
  open Extract
  
  extracted-cnn = pp Primitives.cnn (ε ▹ "inp" ▹ "k1" ▹ "b1" ▹ "k2" ▹ "b2" ▹ "fc" ▹ "b" ▹ "target" ) 
```

If you are reading this file in Agda, you can normalise 
`ExtractionDemo.extracted-cnn` to obtain Futhark expression
for the training phase of our network.


