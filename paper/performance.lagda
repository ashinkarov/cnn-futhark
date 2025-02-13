\section{Performance\label{sec:performance}}

% Notes for Troels:
%
% - Leave Agda-side optimisations for Artem
% - Only backend: Futhark
% - Compared with:
%   - TensorFlow (on GPU)
%   - Hand-written Futhark (lower priority)
% - Will try for multicore numbers as well, if does not complicate story


One of the goals of this work is to demonstrate that it is possible to formulate
the problem in a proof assistant and then pass it on to the other system that can
run the algorithm efficiently.  In order to substantiate this claim, we compare
the running times of the code that we generate from the specification at the end of the
Section~\ref{sec:ad} and the hand-written SaC code from~\cite{cnn-array}.
We are not interested in an exhaustive performance study similar to what is provided
in \cite{cnn-array}. Instead, we take the version from that paper as reference point 
and we aim to find out whether we are in the same ballpark.

We take the code from~\cite{cnn-array}, make sure that it runs, and we replace
the hand-written CNN training with the Agda-generated one. 
Our first observation is that both versions 
produce the same results, and none of the shape constraints
that we defined in Section~\ref{sec:sac-primitives} fired.  This means that our
code generation is working.  Unfortunately, the runtime comparison revealed that
our version is about 10$\times$ slower than the hand-written SaC version.

We got in touch with the SaC team who provided a lot of support in identifying
the causes of the disappointing difference in performance.  It turns out that the main culprit has
to do with the inability to optimise away selections into tensor comprehensions in a few situations.
With-Loop-Folding~\cite{wlf}, SaC's mechanism for fusing tensor comprehensions fails to fold
tensor comprehensions that are nested and cannot be flattened statically.
In simple terms, the expression \texttt{\{iv -> e(iv)\}[jv]} in some situation does not reduce to
\texttt{e(jv)} which, in our generated code, is essential to match the hand-written performance.
As a result, several arrays were created
simply to make a single selection into them.  The original code never ran into this
problem as the hand-written code avoided such patterns.  Our \AF{E} optimiser
from Section~\ref{sec:opt} could not help either, because the problem was occurring after
the SaC primitives such as slide and block were inlined.

After numerous attempts on altering \AF{E} to fit SaC requirements and the SaC
team trying to implement some of the missing optimisations, on the February 23rd
(6 days before the ICFP deadline) we realised that the best runtime we can
obtain is still 6$\times$ slower than the hand-written code.  The compiler is too
sensitive to the flavour of the code that we pass to it, and when certain patterns
are not recognised, there is very little one can do other than trying to fit
those patterns.  However, this is not always possible with the generated code.
Performance \emph{is} frustrating!

\subsection{Generating C}

After overcoming the natural instinct to give up, we realised that the real
power of the proposed approach lies in the ability to modify any part of the
code generation pipeline.  This includes swapping the back-end language of choice
to something else.  Therefore, we decided to try generating C code instead of
SaC code.

While C is a canonical low-level language, it has excellent support for
multi-dimensional arrays, given that the ranks are statically known.
At runtime these arrays are flattened vectors, they do not have to live
on the stack, and the language takes care of multi-dimensional indexing.

However, the key difference between the C and SaC is memory management.
SaC is a functional language that uses reference counting to automate
operations on allocating and freeing memory.  In C these decisions are
manual, and as we have seen before, excessive memory allocation is detrimental
for the runtime.  For our use case we avoid memory management problem
entirely, by assuming that all the variables in the \AF{Chain} have
to be preallocated, and if we need any temporary array variables when
extracting array values, we fail extraction.  This way we guarantee
that no memory allocation is ever needed.

Meeting such a requirement means that we need to optimise away operations
like \AC{slide}/\AC{backslide} as they require conceptual array allocation.
The same goes for \AC{imap}s appearing in some of the argument positions.
Putting these considerations together, we extended \AF{E} with the following
explicit operations on indices:
\begin{code}[hide]
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Unit
open import Data.Empty
open import Data.Product as Prod using (Σ; ∃; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List as L using (List; []; _∷_)
open import Function
open import arrays
open Array hiding (sum; slide; backslide)

data IS : Set where
  ix : S → IS
  ar : S → IS

infixl 15 _▹_
data Ctx : Set where
  ε : Ctx
  _▹_ : Ctx → IS → Ctx

variable
  Γ Δ Ξ Ψ : Ctx
  is ip iq ir : IS

data _∈_ : IS → Ctx → Set where
  here : is ∈ (Γ ▹ is)
  there : is ∈ Γ → is ∈ (Γ ▹ ip)

pattern v₀ = here
pattern v₁ = there v₀
pattern v₂ = there v₁
pattern v₃ = there v₂
pattern v₄ = there v₃
pattern v₅ = there v₄
pattern v₆ = there v₅
pattern v₇ = there v₆
pattern v₈ = there v₇
pattern v₉ = there v₈

unit : S
unit = ι 1

data Bop : Set where
  plus mul : Bop
\end{code}
\begin{code}
data E : Ctx → IS → Set where
  div        : s * p ≈ q → (i : E Γ (ix q)) → E Γ (ix s)
  mod        : s * p ≈ q → (i : E Γ (ix q)) → E Γ (ix p)
  ix-plus    : (i : E Γ (ix s)) → (j : E Γ (ix u)) → suc p ≈ u → s + p ≈ r → E Γ (ix r)
  ix-minus   : (i : E Γ (ix r)) → (j : E Γ (ix s)) → s + p ≈ r → suc p ≈ u 
             → (e : E (Γ ▹ ix u) (ar q)) → E Γ (ar q)
  ix-minusᵣ  : (i : E Γ (ix r)) → (j : E Γ (ix u)) → s + p ≈ r → suc p ≈ u 
             → (e : E (Γ ▹ ix s) (ar q)) → E Γ (ar q)
  -- ...
\end{code}
\begin{code}[hide]
  zero one : E Γ (ar s)
  var : is ∈ Γ → E Γ is

  imapₛ : E (Γ ▹ ix s) (ar unit) → E Γ (ar s)
  selₛ : E Γ (ar s) → E Γ (ix s) → E Γ (ar unit)

  imap : E (Γ ▹ ix s) (ar p) → E Γ (ar (s ⊗ p))
  sel : E Γ (ar (s ⊗ p)) → E Γ (ix s) → E Γ (ar p)

  -- Blocked operations for avgpool 
  imapb : s * p ≈ q → E (Γ ▹ ix s) (ar p) → E Γ (ar q)
  selb : s * p ≈ q → E Γ (ar q) → E Γ (ix s) → E Γ (ar p)

  -- zero-but i j e = i == j ? e : 0
  zero-but : E Γ (ix s) → E Γ (ix s) → E Γ (ar p) → E Γ (ar p)
  sum : E (Γ ▹ ix s) (ar p) → E Γ (ar p)
  bin : Bop → E Γ (ar s) → E Γ (ar s) → E Γ (ar s)

  slide : E Γ (ix s) → s + p ≈ r → E Γ (ar r)
        → suc p ≈ u → E Γ (ar u)
  backslide : E Γ (ix s) → E Γ (ar u) → suc p ≈ u
            → s + p ≈ r → E Γ (ar r)
  
  scaledown : ℕ → E Γ (ar s) → E Γ (ar s)
  minus : E Γ (ar s) → E Γ (ar s)

  logistic : E Γ (ar s) → E Γ (ar s)
\end{code}
The \AC{div} and \AC{mod} constructors perform point-wise division or modulo
operation on the index $i$ and the shape $p$.  This is needed to express selections
into blocked arrays as we have seen in Section~\ref{sec:sac-primitives}.
The \AC{ix-plus} is a point-wise addition of $i$ and $j$.  The \AC{ix-minus} and
\AC{ix-minusᵣ} correspond to left and right subtraction from the Section~\ref{sec:cnn}.
The meaning of these constructors is follows: if $j$ can be subtracted from $i$
(in the sense of existence of inverse to \AF{⊕ₚ} exists) then we evaluate $e$ at that index,
otherwise we return zero.

\subsubsection{Optimisations}
We add the following optimisations to facilitate removal of temporary arrays in
the generated code.  We show the only ones that we added, all the optimisations
we defined before are still valid.
\begin{code}[hide]
_/_ : (Γ : Ctx) → is ∈ Γ → Ctx
(Γ ▹ x) / here = Γ
(Γ ▹ x) / there v = (Γ / v) ▹ x

-- See the actual definition in the ./code directory in the
-- root of the repo, here we just make a stub to explain the
-- code below.
postulate
  wkv : (v : is ∈ Γ) → ip ∈ (Γ / v) → ip ∈ Γ
  wk : (v : is ∈ Γ) → E (Γ / v) ip → E Γ ip

-- Nicer syntax for common case:
infixr 18 ↑_
↑_ : E Γ is → E (Γ ▹ ip) is
↑_ = wk here

infixr 18 ↑↑_
↑↑_ : E Γ is → E (Γ ▹ ip ▹ iq) is
↑↑_ = ↑_ ∘ ↑_

data Eq : is ∈ Γ → ip ∈ Γ → Set where
  eq : {x : is ∈ Γ} → Eq x x
  neq : (x : is ∈ Γ) → (y : ip ∈ (Γ / x)) → Eq x (wkv x y)

postulate
  eq? : (x : is ∈ Γ) → (y : ip ∈ Γ) → Eq x y
  sub : (v : is ∈ Γ) → E Γ ip → E (Γ / v) is → E (Γ / v) ip

\end{code}
\begin{code}
opt : E Γ is → E Γ is
opt (selₛ e e₁) with opt e | opt e₁
... | imapb m e         | i = selₛ (sub v₀ e (div m i)) (mod m i)
... | slide i pl a su   | k = selₛ a (ix-plus i k su pl)
--- | ... as before ...
\end{code}
Here we optimise away scalar selections into blocked imaps.  Recall that $m$ tells us
that we have an array of shape $s * p$, and $e$ computes blocks of shape $p$.  If we
are selecting into such a blocked array at the index $i$, we know that we are selecting
$(i / p)$-th block, and from that block we are selecting $(i \% p)$ element.  Existence
of explicit \AC{div} and \AC{mod} operations on indices makes it possible to implement
this rewrite rule that is again very similar to $\beta$-reduction.
\begin{code}[hide]
... | a                 | i = selₛ a i
\end{code}
\begin{code}
opt (sum e) with opt e
... | zero-but (var i) (ix-plus (var j) (var k) su pl) a  with eq? v₀ i | eq? v₀ j | eq? v₀ k
... | neq _ i′  | neq _ j′  | eq        = ix-minus   (var i′) (var j′) pl su a
... | neq _ i′  | eq        | neq _ k′  = ix-minusᵣ  (var i′) (var k′) pl su a
... | _         | _         | _         = sum (zero-but (var i) (ix-plus (var j) (var k) su pl) a)
--- | ... as before ...
\end{code}
\begin{code}[hide]
opt (sum e) | a = sum a
\end{code}
Here we are dealing with the sum over summation index $t$ where the inner expression is
a conditional on indices of the form \texttt{i == j + k ? e : 0}.  Here we apply the
same comparison of index variables as before.  If $k$ happens to be the variable $t$,
then overall sum will only add one non-zero element at $(i-j)$-th index, given that this
(left) subtraction is possible in the sense of existence of the inverse to \AF{\_⊕ₚ\_} operation
defined in Section~\ref{sec:general-ix-ops}.  The same happens when the summation index
$t$ is equal to $j$, we only need to consider $(i-k)$-th element given that this (right)
subtraction is possible.  One could cover other cases where $t$ is equal to $i$, or
when $i$ and $j+k$ are swapped, but these are not occurring in our running example.

\begin{code}
opt (scaledown x e) with opt e
... | sum a = sum (scaledown x a)
--- | ... as before ...
\end{code}
Finally, here is a rule that looks very innocent in the high-level language, yet
becomes of importance in the low-level one.  The rule says that if we are summing
the array and then dividing it by a constant, we should move division inside the
summation.  The reason for this rewrite rule being important is when the result
of the sum is non-scalar, we need to create a temporary array, before scaling down
all its elements.  A language with first class arrays can obviously take care of
such minor details, but in C we have to be explicit about it.
\begin{code}[hide]
... | a = scaledown x a
opt e = e
\end{code}

\subsubsection{Code Generation}
Due to space limitations, we only consider the basic mechanisms we used in the
code generator, all the code is available in supplementary materials.  We use
heap-allocated multi-dimensional arrays that can be defined as follows:
\begin{lstlisting}[language=C]
  float(*k1)[6][5][5] = malloc(sizeof(*k1));
\end{lstlisting}
This ensures that \texttt{k1} is represented as a continuous region of memory
of size $6*5*5$ floats.  When such arrays are indexed (\eg{} \texttt{(*k1)[i][j][k]}),
the indices are translated into a single offset into the continuous memory.
Therefore, there is no pointer chasing which makes this approach efficient at
runtime.  As C uses row-major order to compute the offsets, we do obtain
partial array selections on the left, \eg \texttt{(*k1)[i]} is a $5\times 5$
array that can be further indexed or passed to \texttt{sizeof} that correctly
identifies the size of this subarray.  Surely, this is a pointer into the \texttt{k1}
array, so all the modifications to \texttt{(*k1)[i]} will modify \texttt{k1}.
As a great convenience feature, C compiler tracks the ranges of the indices
and produces warnings in cases when it figures out that ranges of indices
and the array we are indexing do not match.

Whenever we translate some $e$ in \AF{E} into C, we have to provide a storage
where $e$ has to be written to.  In case of compiling the \AF{Chain} every
local variable becomes such a storage for the bound expression.  Therefore,
our extractor always has a result variable as an argument.

For example, let us consider an expression $a ⊞ a$ of shape
(\AC{ι} 5 \AC{⊗} \AC{ι} 5), where $a$ is mapped to the C variable
\texttt{float (*a)[5][5]} that is written to the result variable
\texttt{float (*r)[5][5]}.  Here is the code that we generate:
\begin{lstlisting}[language=C]
  for (size_t x1_1 = 0; x1_1 < 5; x1_1++) { 
    for (size_t x1_2 = 0; x1_2 < 5; x1_2++) { 
      (*r)[x1_1][x1_2] = ((*a)[x1_1][x1_2] + (*a)[x1_1][x1_2]);
    }}
\end{lstlisting}
We started with checking that $a ⊞ a$ is a \emph{selectable} expression.
This means that we can always generate expression at the given index.
As we know that the shape of $a ⊞ a$ is (\AC{ι} 5 \AC{⊗} \AC{ι} 5),
we need to generate a loop nest of that shape that assigns where
we assign the expression at the given index to the result at the given
index.

We need to distinguish whether we are writing into the result or adding
into it as in cases when dealing with \AF{sum}.  Consider the code that
is generated for (\AC{sum} (\AC{selₛ} (\AB{a} (\AC{var v₀}))) where
we are adding all the elements of the array $a$ into result variable
\texttt{float (*r)[1]}:
\begin{lstlisting}[language=C]
  for (size_t x2_1 = 0; x2_1 < 5; x2_1++) {
    for (size_t x2_2 = 0; x2_2 < 5; x2_2++) {
      for (size_t x3_1 = 0; x3_1 < 1; x3_1++) { 
        (*r)[x3_1] += (&(*a)[x2_1][x2_2])[x3_1];
      }}}
\end{lstlisting}
Two things are happening here, first we generate \texttt{+=} assignment
and we make an implicit assumption that resulting variables are initialised
to zero.  In the extractor, additionally to the resulting variable we
track whether we need to do an assignment or assignment with addition.
Secondly, while $a$ is two-dimensional, we have three-dimensional loop
nest.  The latter comes from the representation of scalars as 1-element
vectors.  When we resolved the two-dimensional summation index \texttt{x2},
we know that we need to assign into the object of shape (\AC{ι} 1), but
the left-hand-side is a scalar (float).  The trick here is that in C we
can always turn scalars into 1-element vectors by simply taking the address
of the scalar.  This is why we have this 1-iteration for-loop over
\texttt{x3\_1} that will be immediately optimised away by the C compiler.

Finally, when we it comes to the operation on indices, such as addition,
subtraction, division or modulo, we generate the corresponding operation
on the individual loop indices.

Remaining details of the code generation take care of traversing through
the structure of \AF{E} with some plumbing that has to do with generating
loop-nests around expressions and checking that they are selectable.

\subsubsection{Running the Generated C Code}
In order to run the generated C code we translate the boilerplate code
from SaC to C.  While doing so, we made sure that our code can be run
in parallel.  While the  SaC compiler does this automatically, there is one
obvious loop that requires parallelisation which is computation of
the batch.  When we train the CNN, we take a batch of images and the
weights and we compute gradients for those weights per every image.
After that we average all the gradients in the batch, and we update
the weights, after all the batch is processed.  Clearly, all the
gradient computations in the batch can run in parallel.  We achieve
this by organising the batch loop such that all the gradients are
stored in a separate memory region, and we parallelise this loop
using OpenMP annotations.

We verify that the code that we generate compute the same results
as the hand-written SaC code.  Then we replicate the experiment from
the~\cite{cnn-array} using 40 epochs, 100 images in the batch, and
feeding 10000 training images.  We run the experiment on the 18-core
13th Gen Intel(R) Core(TM) i5-13600K machine using sac2c version
\texttt{1.3.3-MijasCosta-1161-gb543c} and the GCC compiler
version \texttt{12.2.0}.  The first thing that we learn is that
our generated C code is sensible (factor of 3 running time)
to the compilation flags that we enable.  We identified the set
of flags that when passed to both compilers\footnote{SaC compiler
generates C code, so we can control what flags it uses when
compiling it.}, the runtime at the
largest number of cores are 11s for the hand-written SaC implementation 
and 13.5s for the generated C code, with
very little variance.  This 20\% difference is orthogonal
to parallel execution, as it is also observed when running
the code on a single core.  The set of flags has to do with
floating point operations: \texttt{-fno-signed-zeros} ignores
the distinction between negative and positive zeroes that is given
by IEEE 754 standard, allowing to reduce (-0.0*x) to 0.0;
\texttt{-fno-math-errno} does not set errno after calling math functions;
\texttt{-fno-trapping-math} and \texttt{-fassociative-math} make
sure that we can assume associativity of floating point operations
which does not hold according to the IEEE 754.

The main performance difference comes from the fact that
compiled SaC code uses less intermediate arrays, significantly reducing the number
of memory writes.  There are numerous ways how to improve the performance
of the generated C code, but for the purposes of this paper we consider that getting within
20\% of the hand-written SaC code is sufficient evidence for our hypothesis
that the two-languages approach seems viable for achieving proved
correctness and performance.
We have automatic differentiation in the safe environment
that generates the C code that runs almost as fast as the hand-written
SaC code.


















