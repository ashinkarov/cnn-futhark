\begin{code}[hide]
{-# OPTIONS  --backtracking-instance-search #-}
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty
--open import Function hiding (⟨_⟩)

-- Our local files.
open import arrays
module _ where
\end{code}
\section{Embedded DSL \label{sec:edsl}}

Any implementation of automatic differentiation has to decide which operations
are supported.  Surely, it does not make sense to compute derivatives
of a function that opens a file.  Some systems make it possible to extend
the set of operations via traits or typeclasses, yet when all the instances
are resolved, we end up with a set of operations that
can be seen as a definition of an embedded language.
Once we accept the idea of an embedded language, we may consider to implement
it through deep embedding which gives us the following two advantages.
Firstly, AD, extraction and optimisations can be implemented within the
host language without any compiler modifications.  Secondly, as our host
language is a theorem prover, our implementations can include correctness
guarantees of our choice.  This is the approach we are taking here.

One challenge lies in identifying the primitives for the embedded language,
so that it is sufficiently powerful to define CNNs and to express AD.
Finding the right level of abstraction for the primitives is non-trivial,
as it heavily depends on the capabilities of the backend language and the
optimisations that we can perform locally.  However, keeping the DSL,
optimisations and extraction within a single framework makes it possible
to experiment with these choices easily.


We have chosen sufficiently generic primitives so that many interesting
functions can be defined within the DSL, yet all the primitives are easily
implementable in the backend.  Another consideration is the ability to define
AD within the same DSL, which is useful because we can compute higher-order
derivatives and we can share optimisations between the programs and their
derivatives.
\begin{code}[hide]
module Lang where
  --open Array hiding (sum; slide; backslide)
  open import Data.Nat using (ℕ; zero; suc)
  infixl 15 _▹_
  module Ar where
    open Array public
    open CNN public

  open Ar hiding (sum; slide; backslide; imapb; selb; logistic)

\end{code}

We leverage our dependently-typed setting by making our
embedded language well-scoped and intrinsically typed (shaped),
following a long tradition type- and scope-safe definitions~\cite{intrinsic1,intrinsic2,intrinsic3}.
This is very useful as it eliminates a large class of errors that have to do
with uses of wrong variables and ill-typed expressions.
Types are given by \AD{IS}: we have arrays of
shape $s$ (denoted by \AC{ar}) and indices of shape $s$
(denoted by \AC{ix}).  Contexts are given by \AD{Ctx} and they are
snoc-lists of \AF{IS}-es.  We use de Bruijn variables which are given
by the relation \AF{\_∈\_} in the usual way. 
%We also define variables \AB{v₁}, \AB{v₂}, \etc{}
%by iteratively applying \AC{vₛ} to \AC{v₀} (definition not shown).
\begin{mathpar}
\codeblock{\begin{code}
  data IS : Set where
    ix  : S → IS
    ar  : S → IS
\end{code}}
\and
\codeblock{\begin{code}
  data Ctx : Set where
    ε    : Ctx
    _▹_  : Ctx → IS → Ctx
\end{code}}
\and
\codeblock{\begin{code}[hide]
  variable
    Γ Δ Ξ Ψ : Ctx
    is ip iq ir : IS
\end{code}
\begin{code}
  data _∈_ : IS → Ctx → Set where
    v₀  : is ∈ (Γ ▹ is)
    vₛ  : is ∈ Γ → is ∈ (Γ ▹ ip)
\end{code}}
\end{mathpar}
Note that while our contexts are non-dependent (\ie{} types do not depend on the
members of the context), constructors of the language (\eg{} \AC{imapb}, \AC{sel}) carry non-trivial shape dependencies captured by pointwise shape relations.
The embedded language does not have a notion of shape as a value, therefore all
the shape dependencies are handled by Agda, keeping our language simply
typed (shaped).  This is helpful when it comes to writing
embedded programs.% XXX: more explanation? 
\begin{code}[hide]
  --pattern v₀ = v₀
--  pattern v₁ = vₛ v₀
--  pattern v₂ = vₛ v₁
--  pattern v₃ = vₛ v₂
--  pattern v₄ = vₛ v₃
--  pattern v₅ = vₛ v₄
--  pattern v₆ = vₛ v₅
--  pattern v₇ = vₛ v₆
--  pattern v₈ = vₛ v₇
--  pattern v₉ = vₛ v₈

  infixl 10 _⊞_
  infixl 15 _⊠_
\end{code}

All arrays in our language are assumed to be arrays of reals.  Our contexts
do not carry array element types, and we distinguish
singleton arrays of shape \AC{[]} (\emph{scalars}) that will be mapped
into the type that represents real numbers in the backend \eg{} \texttt{double}.
This means that in the language we do not need to introduce
\AF{nest}/\AF{unnest} operations, as there is no notion of nested arrays.
We do this to keep the language minimal as well as facilitate extraction
described in Section~\ref{sec:extraction}. 

% The language supports two binary operations (addition and multiplication)
% as well as unary minus.
% \begin{mathpar}
% \codeblock{\begin{code}
%   unit : S
%   unit = []
% \end{code}}
% \and
% \codeblock{\begin{code}
%   data Bop : Set where
%     plus mul : Bop
% \end{code}}
% \end{mathpar}

The embedded language \AF{E} includes: variables \AC{var}; constants 0 and 1
(of arbitrary shape) given by \AC{zero} and \AC{one} correspondingly; three
flavours of array constructor/eliminator pairs given by \AC{imaps}/\AC{sels},
\AC{imap}/\AC{sel} and \AC{imapb}/\AC{selb} that we explain below;
summation \AC{sum}; conditional
\AC{zero-but} which compares the equality of two indices and returns either
the third argument or zero; \AC{slide} and \AC{backslide} exactly as described before;
numerical operations which includes \AC{logistic}, plus,
multiplication, division by a constant \AC{scaledown}, and unary \AC{minus};
finally, let bindings for arrays are given by \AC{let′}.
The definition of the embedded language \AF{E} follows. We also introduce 
the syntax for infix minus denoted as \AF{⊟}.
%\begin{mathpar}
%\codeblock{
\begin{code}
  data E : Ctx → IS → Set where
    var        : is ∈ Γ → E Γ is
    zero       : E Γ (ar s)
    one        : E Γ (ar s)

    imaps      : E (Γ ▹ ix s) (ar []) → E Γ (ar s)
    sels       : E Γ (ar s) → E Γ (ix s) → E Γ (ar [])

    imap       : E (Γ ▹ ix s) (ar p) → E Γ (ar (s ⊗ p))
    sel        : E Γ (ar (s ⊗ p)) → E Γ (ix s) → E Γ (ar p)

    imapb      : s * p ≈ q → E (Γ ▹ ix s) (ar p) → E Γ (ar q)
    selb       : s * p ≈ q → E Γ (ar q) → E Γ (ix s) → E Γ (ar p)

    sum        : E (Γ ▹ ix s) (ar p) → E Γ (ar p)
    zero-but   : E Γ (ix s) → E Γ (ix s) → E Γ (ar p) → E Γ (ar p)

    slide      : E Γ (ix s) → s + p ≈ r → E Γ (ar r) → suc p ≈ u → E Γ (ar u)
    backslide  : E Γ (ix s) → E Γ (ar u) → suc p ≈ u → s + p ≈ r → E Γ (ar r)

    logistic   : E Γ (ar s) → E Γ (ar s)
    _⊞_ _⊠_    : E Γ (ar s) → E Γ (ar s) → E Γ (ar s)
    scaledown  : ℕ → E Γ (ar s) → E Γ (ar s)
    minus      : E Γ (ar s) → E Γ (ar s)
    let′       : E Γ (ar s) → E (Γ ▹ ar s) (ar p) → E Γ (ar p)

  pattern _⊟_ a b = a ⊞ (minus b)
\end{code}

The \AC{imap}/\AC{sel} pairs are similar to array versions of lambda
abstraction and application in lambda calculus, except that we
have three flavours of them.
The difference between \AC{imap} and \AC{imapb} (imap blocked)
follows
from the previous definitions: the former turns an $s$-shaped array
of $p$-shaped arrays into a $(s ⊗ p)$-shaped array, whereas \AC{imapb}
performs tiling based on the $s * p ≈ q$ equation.  Strictly speaking,
\AC{imaps} (imap scalar) is not needed, because
the same functionality can be achieved with \AC{imap}/\AC{sel}.
However, if \AC{imap} computes a scalar in the body, its resulting shape 
is $s ⊗ \AF{[]}$ which is not definitionally equal to $s$.  Using
\AC{sel} for selecting a scalar from an $s$-shaped array requires
casting the shape into $s ⊗ \AC{[]}$.  Hence every scalar imap or
selection will require transporting over the $s ⊗ \AC{[]} ≡ s$ equality,
This significantly clutters equality.  One could quotient the shape
type by the above equality, but this requires switching to a more
powerful type theory such as setoid- or cubical type theory.




\subsection{Evaluation}

We give semantics of our language by interpreting \AD{E} expressions
into \AD{Ar} arrays using combinators that we defined earlier.  
This semantics will be also used to prove that optimisations preserve
the meaning of programs.

\subsubsection{Reals}
We parametrise our semantics by the type of reals.
This makes it possible to abstract away from the implementational
details of numerical encoding which are not relevant here.
We define a minimalist interface to reals and their basic
operations as follows.
\begin{mathpar}
\codeblock{\begin{code}
record Real : Set₁ where
  field
    R : Set
    fromℕ : ℕ → R
    _+_ _*_ _÷_ : R → R → R
    -_ e^_ : R → R
\end{code}}
\and
\codeblock{\begin{code}[hide]
  infixl 10 _+_ 
  infixl 15 _*_ 
  infixl 15 _÷_ 
\end{code}
\begin{code}
  logisticʳ : R → R
  logisticʳ x = fromℕ 1 ÷ (fromℕ 1 + e^ (- x))

  0ᵣ = fromℕ 0
  1ᵣ = fromℕ 1
\end{code}}
\end{mathpar}
We require a type of reals that we call \AR{R}, and we define standard
operations that define an exponential field structure on \AF{R} as usual.
We define \AF{fromℕ} to lift natural numbers into \AF{R}.  Also we define
a derived \AF{logistic} function as well as constants 0 and 1.

\begin{code}[hide]
module Eval (real : Real) where
  --open import Data.Float as F renaming (Float to ℝ) hiding (⌊_⌋)
  open import Data.Unit
  open import Data.Product using (_×_; proj₁; proj₂; _,_)
  open import Data.Fin using (Fin; zero; suc; #_)
  open import Relation.Nullary.Decidable
  open import Data.Bool

  open Lang
  open Array
  open Real real
\end{code}

We interpret expressions in (\AF{E} \AB{Γ} \AB{is}) as a value of type
(\AF{Val} \AB{is}) in the environment (\AF{Env} \AB{Γ}).  The values are either
arrays or positions of the corresponding shape.  Environments for the given context
\AB{Γ} are tuples of values of the corresponding shapes.  The \AF{lookup} function
translates variables within the context into variables within the environment.
\begin{mathpar}
\codeblock{\begin{code}
  Val : IS → Set
  Val (ar s)  = Ar s R
  Val (ix s)  = P s
\end{code}}
\and
\codeblock{\begin{code}
  Env : Ctx → Set
  Env ε         = ⊤
  Env (Γ ▹ is)  = Env Γ × Val is
\end{code}}
\and
\codeblock{\begin{code}
  lookup : is ∈ Γ → Env Γ → Val is
  lookup v₀      (ρ , x)  = x
  lookup (vₛ v)  (ρ , _)  = lookup v ρ
\end{code}}
\end{mathpar}

Interpretation is given by \AF{⟦\_⟧} that is defined as follows.  Note that we pass
the environment as instance argument\footnote{For more details on instance arguments
refer to \url{https://agda.readthedocs.io/en/v2.7.0.1/language/instance-arguments.html}.}
which allows us to omit mentioning the environment
in recursive calls when it is passed unchanged.
%  ⟦_⟧ : E Γ is → Env Γ → Val is
%  ⟦ var x               ⟧ ρ  = lookup x ρ
%  ⟦ zero                ⟧ ρ  = K (fromℕ 0)
%  ⟦ one                 ⟧ ρ  = K (fromℕ 1)
%  ⟦ imaps e             ⟧ ρ  = λ i → ⟦ e ⟧ (ρ , i) [] 
%  ⟦ sels e e₁           ⟧ ρ  = K (⟦ e ⟧ ρ (⟦ e₁ ⟧ ρ))
%  ⟦ imap e              ⟧ ρ  = unnest λ i → ⟦ e ⟧ (ρ , i)
%  ⟦ sel e e₁            ⟧ ρ  = nest (⟦ e ⟧ ρ) (⟦ e₁ ⟧ ρ)
%  ⟦ imapb m e           ⟧ ρ  = Ar.imapb (λ i → ⟦ e ⟧ (ρ , i)) m
%  ⟦ selb m e e₁         ⟧ ρ  = Ar.selb (⟦ e ⟧ ρ) m (⟦ e₁ ⟧ ρ)
%  ⟦ sum e               ⟧ ρ  = Ar.sum (Ar.zipWith _+_) (K (fromℕ 0)) (λ i → ⟦ e ⟧ (ρ , i))
%  ⟦ zero-but i j e      ⟧ ρ  = if ⌊ ⟦ i ⟧ ρ ≟ₚ ⟦ j ⟧ ρ ⌋ then ⟦ e ⟧ ρ else K (fromℕ 0)
%  ⟦ slide e p e₁ s      ⟧ ρ  = Ar.slide (⟦ e ⟧ ρ) p (⟦ e₁ ⟧ ρ) s
%  ⟦ backslide e e₁ s p  ⟧ ρ  = Ar.backslide (⟦ e ⟧ ρ) (⟦ e₁ ⟧ ρ) s (fromℕ 0) p
%  ⟦ logistic e          ⟧ ρ  = Ar.map logisticʳ (⟦ e ⟧ ρ)
%  ⟦ e ⊞ e₁              ⟧ ρ  = Ar.zipWith _+_ (⟦ e ⟧ ρ) (⟦ e₁ ⟧ ρ)
%  ⟦ e ⊠ e₁              ⟧ ρ  = Ar.zipWith _*_ (⟦ e ⟧ ρ) (⟦ e₁ ⟧ ρ)
%  ⟦ scaledown n e       ⟧ ρ  = Ar.map (_÷ fromℕ n) (⟦ e ⟧ ρ) 
%  ⟦ minus e             ⟧ ρ  = Ar.map -_ (⟦ e ⟧ ρ)
%  ⟦ let′ e e₁           ⟧ ρ  = ⟦ e₁ ⟧ (ρ , ⟦ e ⟧ ρ)
\begin{code}
  ⟦_⟧ : E Γ is → ⦃ Env Γ ⦄ → Val is
  ⟦ var x               ⟧ ⦃ ρ ⦄  = lookup x ρ
  ⟦ zero                ⟧ ⦃ ρ ⦄  = Ar.K 0ᵣ
  ⟦ one                 ⟧ ⦃ ρ ⦄  = Ar.K 1ᵣ
  ⟦ imaps e             ⟧ ⦃ ρ ⦄  = λ i → ⟦ e ⟧ ⦃ ρ , i ⦄ [] 
  ⟦ sels e e₁           ⟧ ⦃ ρ ⦄  = Ar.K (⟦ e ⟧ ⟦ e₁ ⟧)
  ⟦ imap e              ⟧ ⦃ ρ ⦄  = Ar.unnest λ i → ⟦ e ⟧ ⦃ ρ , i ⦄
  ⟦ sel e e₁            ⟧ ⦃ ρ ⦄  = Ar.nest ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ imapb m e           ⟧ ⦃ ρ ⦄  = Ar.imapb (λ i → ⟦ e ⟧ ⦃ ρ , i ⦄) m
  ⟦ selb m e e₁         ⟧ ⦃ ρ ⦄  = Ar.selb ⟦ e ⟧ m ⟦ e₁ ⟧
  ⟦ sum e               ⟧ ⦃ ρ ⦄  = Ar.sum (Ar.zipWith _+_) (Ar.K 0ᵣ) (λ i → ⟦ e ⟧ ⦃ ρ , i ⦄)
  ⟦ zero-but i j e      ⟧ ⦃ ρ ⦄  = if ⌊ ⟦ i ⟧ ≟ₚ ⟦ j ⟧ ⌋ then ⟦ e ⟧ else Ar.K 0ᵣ
  ⟦ slide e p e₁ s      ⟧ ⦃ ρ ⦄  = Ar.slide ⟦ e ⟧ p ⟦ e₁ ⟧ s
  ⟦ backslide e e₁ s p  ⟧ ⦃ ρ ⦄  = Ar.backslide ⟦ e ⟧ ⟦ e₁ ⟧ s 0ᵣ p
  ⟦ logistic e          ⟧ ⦃ ρ ⦄  = Ar.map logisticʳ ⟦ e ⟧
  ⟦ e ⊞ e₁              ⟧ ⦃ ρ ⦄  = Ar.zipWith _+_ ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ e ⊠ e₁              ⟧ ⦃ ρ ⦄  = Ar.zipWith _*_ ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ scaledown n e       ⟧ ⦃ ρ ⦄  = Ar.map (_÷ fromℕ n) ⟦ e ⟧
  ⟦ minus e             ⟧ ⦃ ρ ⦄  = Ar.map -_ ⟦ e ⟧
  ⟦ let′ e e₁           ⟧ ⦃ ρ ⦄  = ⟦ e₁ ⟧ ⦃ ρ , ⟦ e ⟧ ⦄
\end{code}
Mostly, the interpretation is a straightforward mapping to the \AF{Ar} constructors.
In the \AC{imaps} case we can see how the implicit conversion from what would be a
shape $s ⊗ \AC{[]}$ into $s$.  In case of \AC{sels} we make a singleton array
using \AF{K}. Note that \AC{sum} has explicit summation index like in a mathematical
$\sum$-notation.  We fix the default value of \AC{backslide} to zero for simplicity.
For arrays of reals, we can get general \AF{backslide} behaviour through masking.
However, this operation can be generalised in case we decide to support arrays of
other element types.


% With the above definition we can better explain the choices of language constructors.
% The most important question to clarify is why do we have three array
% constructors/eliminators.  As the only conceptual datatype of our language is
% an array (of some shape), we do not have any direct way to talk about array elements.
% Therefore, we model the type of array elements (scalars) as arrays of a singleton shape.
% As can be seen, scalar selection \AC{selₛ} returns a singleton array
% (application of \AF{K}) where all the element(s) are equal to the element we are
% selecting.  The corresponding array constructor \AC{imapₛ} makes sure that if we
% compute \AB{s} elements of the shape \AF{unit}, we produce an array of shape \AB{s}
% (and not \AB{s} \AC{⊗} \AF{unit}).  This soves the problem of constructing arays
% from scalars, but how do we construct an array of a product shape?  Given that we
% have an expression in the context (\AB{Γ} \AC{▹} \AC{ix} \AB{s} \AC{▹} \AC{ix} \AB{p}),
% we need to produce an array of \AB{s} \AC{⊗} \AB{p}.  There are several ways how to
% solve this (\eg{} introducing nest/unnest or projections and pairing on indices),
% but it is clear that we need something more than just an \AC{imapₛ}.
% This is the reason to introduce \AC{imap}/\AC{sel} pair which operates on arrays
% of product shapes.  
% As average pooling operates on blocked arrays, we need
% a construction to express this in \AF{E}.  One could introduce explicit 
% \AF{block}/\AF{unblock}, but we merge blocking/unlocking action with
% imap/sel obtaining \AC{imapb}/\AC{selb}.  Our \AC{sum} constructor 
% gets an argument in the extended context which is summation index, so 
% conceptually we generate the values at every summation index before
% summing these values together.  As a result, we only need
% one instance of \AC{sum} which makes our expressions a little tidier.




\subsection{Weakening and Substitution}
In this section, we recall a standard construction of weakening and
substitution that will be employed in subsequent sections. We present this
construction in the style of references \cite{par-sub2,intrinsic1,intrinsic2},
exposing a minimal set of constructions necessary for the remainder of the
paper.

The key structure required is a category of weakenings \cite{ope-cat}, in which
objects are contexts and morphisms are order-preserving embeddings denoted by
\AD{\_⊆\_}. Order-preserving embeddings
give rise to Kripke semantics, where contexts are interpreted as worlds, and
\AF{⊆} serves as a binary relation on these worlds. Binders can be interpreted
as Kripke function spaces, leading to an elegant formulation \cite{intrinsic3}
of normalisation. However, our focus here is solely on weakening and
substitution.

If \AB{Γ} \AD{⊆} \AB{Δ}, then \AB{Γ} can be embedded into \AB{Δ} in the original
order (possibly with some gaps).  The action on the variables is given by
\AF{wkv} as defined below.
\begin{code}[hide]
module WkSub where
  open Lang
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  data _⊆_ : Ctx → Ctx → Set where
    ε     : ε ⊆ ε
    skip  : Γ ⊆ Δ → Γ ⊆ (Δ ▹ is)
    keep  : Γ ⊆ Δ → (Γ ▹ is) ⊆ (Δ ▹ is)
\end{code}}
\and
\codeblock{\begin{code}  
  wkv : Γ ⊆ Δ → is ∈ Γ → is ∈ Δ
  wkv (skip s) v       = vₛ (wkv s v)
  wkv (keep s) v₀      = v₀
  wkv (keep s) (vₛ v)  = vₛ (wkv s v)
\end{code}}
\end{mathpar}


The action on \AF{E} is given by \AF{wk}, which type is defined below.
Identity of context embeddings is given by \AF{⊆-eq}, and we omit the
composition that can be defined as well.
A common case of weakening expressions into the context with one extra variable
is denoted with \AF{\_↑} and it is defined as follows.
\begin{mathpar}
\codeblock{\begin{code}
  wk : Γ ⊆ Δ → E Γ is → E Δ is
\end{code}}
\and
\codeblock{\begin{code}
  ⊆-eq : Γ ⊆ Γ
  ⊆-eq {ε}      = ε
  ⊆-eq {Γ ▹ x}  = keep ⊆-eq
\end{code}}
\and
\codeblock{\begin{code}
  _↑ : E Γ is → E (Γ ▹ ip) is
  _↑ = wk (skip ⊆-eq)
\end{code}}
\end{mathpar}

\begin{code}[hide]
  wk s (var x) = var (wkv s x)
  wk s zero = zero
  wk s one = one
  wk s (imaps e) = imaps (wk (keep s) e)
  wk s (sels e e₁) = sels (wk s e) (wk s e₁)
  wk s (imap e) = imap (wk (keep s) e)
  wk s (sel e e₁) = sel (wk s e) (wk s e₁)
  wk s (imapb x e) = imapb x (wk (keep s) e)
  wk s (selb x e e₁) = selb x (wk s e) (wk s e₁)
  wk s (sum e) = sum (wk (keep s) e)
  wk s (zero-but e e₁ e₂) = zero-but (wk s e) (wk s e₁) (wk s e₂)
  wk s (slide e x e₁ x₁) = slide (wk s e) x (wk s e₁) x₁
  wk s (backslide e e₁ x x₁) = backslide (wk s e) (wk s e₁) x x₁
  wk s (logistic e) = logistic (wk s e)
  wk s (e ⊞ e₁) = (wk s e) ⊞ (wk s e₁)
  wk s (e ⊠ e₁) = (wk s e) ⊠ (wk s e₁)
  wk s (scaledown x e) = scaledown x (wk s e)
  wk s (minus e) = minus (wk s e)
  wk s (let′ e e₁) = let′ (wk s e) (wk (keep s) e₁)
\end{code} 

We implement parallel substitution~\cite{par-sub1,par-sub2} in the usual way.
The key structure that
gives rise to the substitution is a mapping of variables in the context \AB{Δ}
into expressions in the context \AB{Γ}.
This is given by \AF{Sub} \AB{Γ} {Δ} and it represents a \AF{Δ}-long
list of (\AF{E} \AB{Γ})-s where each expression is of a type that corresponds to the
variable type at the given position of \AF{Δ}.  We define \AF{wks} which weakens
all the expressions of \AF{Sub} in the following way.
\begin{mathpar}
\codeblock{\begin{code}
  data Sub (Γ : Ctx) : Ctx → Set where
    ε    : Sub Γ ε
    _▹_  : Sub Γ Δ → E Γ is → Sub Γ (Δ ▹ is)
\end{code}}
\and
\codeblock{\begin{code}
  wks : Sub Γ Δ → Γ ⊆ Ψ → Sub Ψ Δ
  wks ε p        = ε
  wks (s ▹ x) p  = (wks s p) ▹ wk p x
\end{code}}
\end{mathpar}
Using \AF{wks} we define two useful combinators: \AF{sdrop} to lift all
expressions in the \AD{Sub} list into a context that is extended by one variable;
\AF{skeep} to shift the substitution by one variable, keeping the top variable
as is.  With these combinators we define the identity substitution \AF{sub-id}
that has no effect when applying it.  Finally, the type of the actual substitution
that replaces all the variables in \AF{E} according to some \AF{Sub} list is given
by \AF{sub}.
\begin{mathpar}
\codeblock{\begin{code}
  sdrop : Sub Γ Δ → Sub (Γ ▹ is) Δ
  sdrop s = wks s (skip ⊆-eq)

  skeep : Sub Γ Δ → Sub (Γ ▹ is) (Δ ▹ is)
  skeep s = sdrop s ▹ var v₀
\end{code}}
\and
\codeblock{\begin{code}
  sub-id : Sub Γ Γ
  sub-id {ε}      = ε
  sub-id {Γ ▹ x}  = skeep sub-id

  sub : E Δ is → Sub Γ Δ → E Γ is
\end{code}}
\end{mathpar}
\begin{code}[hide]
  subv : Sub Γ Δ → is ∈ Δ → E Γ is
  subv (s ▹ x) v₀      = x
  subv (s ▹ x) (vₛ v)  = subv s v
  
  sub (var x) s = subv s x
  sub zero s = zero
  sub one s = one
  sub (imaps e) s = imaps (sub e (skeep s))
  sub (sels e e₁) s = sels (sub e s) (sub e₁ s)
  sub (imap e) s = imap (sub e (skeep s))
  sub (sel e e₁) s = sel (sub e s) (sub e₁ s)
  sub (imapb x e) s = imapb x (sub e (skeep s))
  sub (selb x e e₁) s = selb x (sub e s) (sub e₁ s)
  sub (sum e) s = sum (sub e (skeep s))
  sub (zero-but e e₁ e₂) s = zero-but (sub e s) (sub e₁ s) (sub e₂ s)
  sub (slide e x e₁ x₁) s = slide (sub e s) x (sub e₁ s) x₁
  sub (backslide e e₁ x x₁) s = backslide (sub e s) (sub e₁ s) x x₁
  sub (logistic e) s = logistic (sub e s)
  sub (e ⊞ e₁) s = (sub e s) ⊞ (sub e₁ s)
  sub (e ⊠ e₁) s = (sub e s) ⊠ (sub e₁ s)
  sub (scaledown x e) s = scaledown x (sub e s)
  sub (minus e) s = minus (sub e s)
  sub (let′ e e₁) s = let′ (sub e s) (sub e₁ (skeep s))

  _∙ˢ_ : Sub Δ Ψ → Sub Γ Δ → Sub Γ Ψ
  ε ∙ˢ t = ε
  (s ▹ x) ∙ˢ t = (s ∙ˢ t) ▹ sub x t
\end{code}
As our contexts are not dependent (\eg{} the type of the variables does not
depend on previous variables) we can define a substitution that swaps two top
variables in the context.  This substitution is given by \AF{sub-swap} and it
will be used in optimisations.
\begin{mathpar}
\codeblock{\begin{code}
  sub-swap : Sub (Γ ▹ is ▹ ip) (Γ ▹ ip ▹ is)
  sub-swap = sdrop (sdrop sub-id) ▹ var v₀ ▹ var (vₛ v₀)
\end{code}}
\end{mathpar}

\subsection{Syntax}
Deeply-embedded DSLs with intrinsic de Bruijn variables guarantee well-scopedness,
but they are not intuitive for humans.  This section proposes a mechanism
to overcome the encoding burden by providing HOAS-like syntactic wrappers for
\AD{E}.

Our goal is to replace de Bruijn variables with Agda's variables.  One immediate
difficulty with this approach is that whenever we go under binders such as 
\AC{imap} or \AC{let′}, all the variables/expressions we defined before have to be
lifted into the extended context.  We tackle this problem by forcing Agda to
compute such lifted expressions automatically by (ab)using Agda's
instance resolution mechanism.

We only ever need to lift expressions/variables into
contexts where a certain number of variables were added at the end, \ie{} the
prefix of the extended context always correspond to the context of the original
expression.  Therefore, we define a binary relation \AF{Prefix} \AB{Γ} \AB{Δ}
that determines whether the \AB{Γ} is a prefix of \AB{Δ}.  We annotate
constructors of \AF{Prefix} with the \AK{instance} keyword, and we wrap
the argument of the \AC{suc} constructor into double braces, turning this into
an instance argument.  Simultaneously, \AF{prefix-⊆} defines a translation from
\AD{Prefix} into order-preserving embeddings \AD{⊆} so that we can
leverage weakening.
\begin{mathpar}
\codeblock{\begin{code}[hide]
module Syntax where
  open Lang
  open import Data.List as L using (List; []; _∷_)
  open Array hiding (sum)
  open WkSub
\end{code}
\begin{code}
  data Prefix : (Γ Δ : Ctx) → Set where
    instance
      zero : Prefix Γ Γ
      suc  : ⦃ Prefix Γ Δ ⦄ → Prefix Γ (Δ ▹ is)
\end{code}}
\and
\codeblock{\begin{code}
  prefix-⊆ : Prefix Γ Δ → Γ ⊆ Δ
  prefix-⊆ zero         = ⊆-eq
  prefix-⊆ (suc ⦃ p ⦄)  = skip (prefix-⊆ p)
\end{code}}
\end{mathpar}

As a result, Agda is able to construct an element of
\AD{Prefix} \AB{Γ} (\AB{Γ} \AC{▹} \AB{is} ▹ \AB{ip} ▹ \AB{iq}) automatically.
Similarly
to hidden arguments, there is no guarantee that the solution will be found
in all cases --- Agda will report an error in case of failure.
Note that instance resolution is looking for the \emph{unique} solution.
This is the reason why we could not use \AD{⊆} instead of \AD{Prefix} easily,
even thought the former is more general than the latter.
Contexts (\AB{Γ} \AC{▹} \AB{is}) and (\AB{Γ} \AC{▹} \AB{is} \AC{▹} \AB{is}),
are related by \AD{Prefix} in a unique way.  However, these two contexts are
related by \AD{⊆} in two different ways (by keeping the first or the
second variable).

We introduce generalised variables \AF{GV} and expressions \AF{GE} that
are defined in context \AB{Γ} but can be lifted into any context \AB{Δ}, given
that \AB{Γ} is a prefix of \AB{Δ}.  The trick here is that both types define
a function of two hidden arguments that Agda will be able to fill-in automatically.
\begin{mathpar}
\codeblock{\begin{code}
  GE : Ctx → IS → Set
  GE Γ is = ∀ {Δ} → ⦃ Prefix Γ Δ ⦄ → E Δ is
\end{code}}
\and
\codeblock{\begin{code}
  GV : Ctx → IS → Set
  GV Γ is = ∀ {Δ} → ⦃ p : Prefix Γ Δ ⦄ → is ∈ Δ
\end{code}}
\end{mathpar}
We can lift expressions into generalised expressions in two steps: 
(i) we translate prefixes into \AC{⊆}; (ii) we use weakening that we defined earlier.
\begin{mathpar}
\codeblock{\begin{code}
  ⟨_⟩ : E Γ is → GE Γ is
  ⟨_⟩ t {Δ} ⦃ p ⦄ = wk (prefix-⊆ p) t
\end{code}}
\and
\codeblock{\begin{code}
  ⟨_⟩ᵛ : is ∈ Γ → GV Γ is
  ⟨_⟩ᵛ v ⦃ p ⦄ = wkv (prefix-⊆ p) v
\end{code}}
\end{mathpar}
With these operations we define HOAS-like wrappers for the \AF{E} binders
such as \AC{imap} family, \AC{sum} and \AC{let′}.  Consider
a wrapper for \AC{imap} defined as follows.
\begin{code}
  Imap : (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p)) → E Γ (ar (s ⊗ p))
  Imap f = imap (f (var ⟨ v₀ ⟩ᵛ))
\end{code}
The first argument is a function in Agda's function space where the
argument is a generalised expression of type $\AC{ix}\ s$ in the context
extended by $\AC{ix}\ s$ (the imap index); and the return type is the array
expression that will be computed in the body of the imap.  The implementation
of the wrapper constructs an \AC{imap}, lifting the index variable
\AC{v₀} of the context \AB{Γ} \AC{▹} $\AC{ix}\ s$ into a larger context that is determined
by the hidden/instance arguments of $f$.  This means that within the body of $f$
we can use the argument under further binders as follows:
\begin{code}
  _ : E ε _ 
  _ = Imap {s = ι 5} λ i → Imap {s = ι 5} λ j → sels (sel one j) i
\end{code}
Implementation of wrappers for \AC{sum}, \AC{imaps}, \AC{imapb} looks very similar
so we omit it here.  However, when defining a wrapper for \AC{let′} we
use Agda's \AK{syntax} feature\footnote{See
\url{https://agda.readthedocs.io/en/v2.7.0.1/language/syntax-declarations.html}
for more details.} to define a familiar syntax for let bindings in \AF{E}.
\begin{code}[hide]
  Sum : ∀ {Γ}
       → (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p))
       → E Γ (ar p)
  Sum f = sum (f λ {Δ} ⦃ p ⦄ → var ⟨ v₀ ⟩ᵛ)

  Imaps : ∀ {Γ}
        → (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar []))
        → E Γ (ar s)
  Imaps f = imaps (f λ {Δ} ⦃ p ⦄ → var ⟨ v₀ ⟩ᵛ)

  Imapb : ∀ {Γ}
        → s * p ≈ q 
        → (GE (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p)) 
        → E Γ (ar q)
  Imapb p f = imapb p (f λ {Δ} ⦃ p ⦄ → var ⟨ v₀ ⟩ᵛ)
\end{code}
\begin{code}
  Let-syntax : E Γ (ar s) → (GE (Γ ▹ (ar s)) (ar s) → E (Γ ▹ (ar s)) (ar p)) → E Γ (ar p)
  Let-syntax x f = let′ x (f (var ⟨ v₀ ⟩ᵛ))
  syntax Let-syntax e (λ x → e') = Let x := e In e'
\end{code}
With these definitions we can write expressions with let binding as follows:
\begin{code}
  _ : E ε (ar [])
  _ = Let x := one In Let y := x ⊞ one In (x ⊞ y) ⊠ x  
\end{code}
One final syntactical convenience is the ability to
represent contexts in the HOAS style.
First of all, we define a helper function \AF{ext} that appends a list of \AF{IS}
at the end of some context \AF{Γ}.
Secondly, we define \AF{lfun} that for the given list of \AF{IS}-es
(l = [is₁, \dots, isₙ]), some context \AF{Γ} and some \AF{IS}
ip computes an Agda function of type (\AF{GE} (\AF{ext} \AF{Γ} l) is₁ →
\dots → \AF{GE} (\AF{ext} \AF{Γ} l) isₙ → \AD{E} (\AF{ext} Γ l) ip).
The function \AF{lvar} lifts a variable in some context Γ into
a generalised expression within the \AF{ext}ended context.
\begin{mathpar}
\codeblock{\begin{code}[hide]
  infixl 3 Let-syntax

  -- Extend context with a list of types
  -- (List is a context that grows to the left)
\end{code}
\begin{code}
  ext : Ctx → List IS → Ctx
  ext Γ []      = Γ
  ext Γ (x ∷ l) = ext (Γ ▹ x) l
\end{code}}
\and
\codeblock{\begin{code}
  lfun : (l : List IS)  (Γ : Ctx) (is : IS) → Set
  lvar : ∀ l → is ∈ Γ → GE (ext Γ l) is
\end{code}}
\end{mathpar}
\begin{code}[hide]
  -- Turn the list of IS into the following function:
  --   l = [a, b, c]
  --   X = X
  --   Γ = Γ
  --   ----------------------------
  --   GE Γ a → GE Γ b → GE Γ c → X
  lfunh : (l : List IS) (X : Set) (Γ : Ctx) → Set
  lfunh [] X Γ = X
  lfunh (a ∷ l) X Γ = GE Γ a → lfunh l X Γ

  -- Diagonalise lfunh:
  --   l = [a, b]
  --   Γ = Γ
  --   is = is
  --   ---------------------------------------------
  --   GE (ext Γ l) a → GE (ext Γ l) → E (ext Γ l) is
  lfun l Γ τ = lfunh l (E (ext Γ l) τ) (ext Γ l)
  lvar [] v = var ⟨ v ⟩ᵛ
  lvar (x ∷ l) v = lvar l (vₛ v)
\end{code}
With these helper functions we define \AF{Lcon} which computes
an expression in the context extended by $l$ from the function
of $l$ arguments:
\begin{code}
  Lcon : ∀ l is Γ → (f : lfun l Γ is) → E (ext Γ l) is
  Lcon []      is Γ f  = f
  Lcon (x ∷ l) is Γ f  = Lcon l is (Γ ▹ x) (f (lvar l v₀))
\end{code}
In practice, this allows one to bind the last $n$ elements of the
context to Agda variables and use them under binders without weakening.
For example, consider the expression:
\begin{code}
  _ : E _ _
  _ = Lcon (ar (ι 5) ∷ ar (5 ∷ 5 ∷ []) ∷ []) (ar []) ε
      λ a b → Sum λ i → sels a i ⊞ sels (sel b i) i
\end{code}
where \AB{a} and \AB{b} are Agda's variables that represent
de Bruijn variable 1 and 0{} in the context (ε ▹ \AC{ar} (5 ∷ []) ▹ 
\AC{ar} (5 ∷ 5 ∷ [])).



\subsection{CNN Primitives in \AD{E}}
The built-in operations of \AD{E} are not specific to the CNN that we
are defining.  Therefore, similarly to Sec.~\ref{sec:ar-cnn-prim},
the primitives required for the running example have to be
implemented in terms of \AD{E}.  Syntactic wrappers help us
to achieve similarity between the operations defined below and the
\AF{Ar} primitives.

Implementation of \AF{conv}, \AF{mconv} and \AF{avgp₂} is a direct
translation of the respective \AD{Ar} counterparts, the only visible
differences are: lack of \AF{map} combinator and
rank-polymorphic addition and multiplication.
\begin{code}[hide]
module Primitives where

  open import Data.List as L using (List; []; _∷_)
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open import Function using (_$_; it; _∋_)
  open import Relation.Binary.PropositionalEquality
  open Array hiding (slide)
  open Syntax
  open WkSub
  open Lang

 
\end{code}
\begin{code}
  conv : E Γ (ar r) → ⦃ s + p ≈ r ⦄ → E Γ (ar s) → ⦃ suc p ≈ u ⦄ → E Γ (ar u)
  conv f ⦃ s+p ⦄ g ⦃ ss ⦄ = Sum λ i → (slide i s+p ⟨ f ⟩ ss) ⊠ Imaps λ j → sels ⟨ g ⟩ i

  mconv : ⦃ s + p ≈ r ⦄ → (inp : E Γ (ar r)) (ws : E Γ (ar (u ⊗ s)))
          (bᵥ : E Γ (ar u)) → ⦃ suc p ≈ w ⦄ → E Γ (ar (u ⊗ w))
  mconv ⦃ sp ⦄ inp wᵥ bᵥ ⦃ su ⦄ = Imap λ i → conv ⟨ inp ⟩ (sel ⟨ wᵥ ⟩ i) ⊞ Imaps λ _ → sels ⟨ bᵥ ⟩ i

  avgp₂ : ∀ m n → (a : E Γ (ar (m ℕ.* 2 ∷ n ℕ.* 2 ∷ []))) → E Γ (ar (m ∷ n ∷ []))
  avgp₂ m n a = Imaps λ i → scaledown 4 $ Sum λ j → sels (selb it ⟨ a ⟩ i) j
\end{code}
The mean squared error function \AF{meansqerr} computes
$\sum_i \frac{1}{2}(r_i - o_i)^2$ for the argument arrays $r$ and $o$
which must be of the same shape.
\begin{code}
  sqerr : (r o : E Γ (ar [])) → E Γ (ar [])
  sqerr r o = scaledown 2 ((r ⊟ o) ⊠ (r ⊟ o))

  meansqerr : (r o : E Γ (ar s)) → E Γ (ar [])
  meansqerr r o = Sum λ i → sqerr (sels ⟨ r ⟩ i) (sels ⟨ o ⟩ i) 
\end{code}
With these primitives, we embed our running example in $E$ as follows:
\begin{mathpar}
\codeblock{\begin{code}
  cnn : E _ _
  cnn = Lcon (  ar (28 ∷ 28 ∷ []) ∷ ar (6 ∷ 5 ∷ 5 ∷ []) ∷ ar (6 ∷ []) ∷ ar (12 ∷ 6 ∷ 5 ∷ 5 ∷ [])
                ∷ ar (12 ∷ []) ∷ ar (10 ∷ 12 ∷ 1 ∷ 4 ∷ 4 ∷ []) ∷ ar (10 ∷ [])
                ∷ ar (10 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []) ∷ [])
             (ar []) ε
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
\end{code}}
\end{mathpar}
Note that with the proposed syntax, the above definition looks very similar
to the one we defined directly in Agda.  We use more let bindings in this
definition, which is not an arbitrary choice, and we will come back to this
discussion in the next section.

% \paragraph{Building Blocks}
% Now we implement the remaining building blocks in \AD{E} that are needed
% to define our CNN.
% \begin{code}[hide]
% module BB where
%   open import Data.Nat as ℕ using (ℕ; zero; suc)
%   open Array hiding (sum; slide; backslide)
%   open Lang
%   open SubWk using (wk; ↑_; ↑↑_)
% 
%   --_⊞_ _⊠_ : (a b : E Γ (ar s)) → E Γ (ar s)
%   Imapₛ : (E (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar unit)) → E Γ (ar s)
%   Imap : (E (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p)) → E Γ (ar (s ⊗ p))
%   Sum : (E (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p)) → E Γ (ar p)
% \end{code}
% We start with a several convenience functions that wrap \AC{imap}s and \AC{sum}
% such that when we write (\AF{Imap} \AB{λ} \AB{i} \AB{→} \AB{⋯}), Agda's variable
% $i$ is mapped to the \AF{E}'s variable \AC{v₀}.
% \begin{mathpar}
% \codeblock{\begin{code}
%   Imapₛ f = imapₛ (f (var v₀))
% \end{code}}
% \and
% \codeblock{\begin{code}
%   Imap f = imap (f (var v₀))
% \end{code}}
% \and
% \codeblock{\begin{code}
%   Sum f = sum (f (var v₀))
% \end{code}}
% \end{mathpar}
% 
% The remaining operations are \AF{conv}, \AF{mconv} and \AF{avgp₂} which
% can be defined as functions on \AF{E} as follows.
% \begin{code}
%   conv : E Γ (ar r) → s + p ≈ r → E Γ (ar s) → suc p ≈ u → E Γ (ar u)
%   conv f sp g su = Sum λ i → slide i sp (↑ f) su ⊠ Imapₛ λ _ → selₛ (↑↑ g) (↑ i)
% 
%   mconv : s + p ≈ r → (inp : E Γ (ar r)) (we : E Γ (ar (u ⊗ s))) (b : E Γ (ar u))
%         → suc p ≈ w → E Γ (ar (u ⊗ w))
%   mconv sp inp we b su = Imap λ i → conv (↑ inp) sp (sel (↑ we) i) su ⊞ Imapₛ λ _ → selₛ (↑↑ b) (↑ i)
% 
%   avgp₂ : ∀ m n → (a : E Γ (ar (ι (m ℕ.* 2) ⊗ ι (n ℕ.* 2)))) → E Γ (ar (ι m ⊗ ι n))
%   avgp₂ m n a = Imapₛ λ i → scaledown 4 $ Sum λ j → selₛ (selb (ι ⊗ ι) (↑↑ a) (↑ i)) j
% 
% \end{code}
% Note that these definitions are not very different from those found in
% Section~\ref{sec:array-theory}.  Some operations such as \AF{nest} and \AF{unnest}
% got inlined into \AF{E}'s operators, and all we really have to take care of is 
% weakening of the expressions whenever we go under binders.

