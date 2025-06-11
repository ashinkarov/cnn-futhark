\begin{code}[hide]
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List using (List; []; _∷_)
open import Data.Empty
open import Function

-- Our local files.
open import arrays
open import lang
module _ where
\end{code}

\section{Automatic Differentiation\label{sec:ad}}


We implement the reverse mode of automatic differentiation for expressions in
\AF{E}. Our focus on the reverse mode is due to its significance in machine
learning and the increased complexity associated with its implementation. We
begin with a brief introduction to automatic differentiation; for more
comprehensive explanations, please refer to~\cite{autodiff-survey,
backprop-stlc}.

Consider the differentiation of a function composition consisting of the
functions \(f\), \(g\), and \(h\):
\(
y = (f \circ g \circ h)\ x.
\)
By introducing temporary variables (on the left-hand side), the
chain rule (on the right-hand side) is defined as follows:
\begin{mathpar}
  w_0 = x; \quad w_1 = h\ w_0; \quad w_2 = g\ w_1; \quad y = f\ w_2
  \and
  \frac{\partial y}{\partial x} = \frac{\partial y}{\partial w_0} 
    = \frac{\partial y}{\partial w_2}
      \frac{\partial w_2}{\partial w_1}
      \frac{\partial w_1}{\partial w_0}.
\end{mathpar}
The primary distinction between the forward and reverse differentiation modes
lies in the direction in which the chain rule is traversed. In forward mode, we
traverse function compositions from right to left (following the order of
evaluation), whereas in reverse mode, we traverse from left to right, thereby
computing the recursive relation:
\(
\frac{\partial y}{\partial w_i} = \frac{\partial y}{\partial w_{i+1}} \frac{\partial w_{i+1}}{\partial w_i}.
\)
In our example, we compute \(\frac{\partial y}{\partial w_2}\), followed by
\(\frac{\partial w_2}{\partial w_1}\), and finally \(\frac{\partial
w_1}{\partial w_0}\). While the direction makes no difference for functions of
a single variable, a significant difference arises for functions of \(n\)
variables, as reverse mode computes partial derivatives with respect to all inputs
simultaneously.

\paragraph{Example of Reverse AD}
We illustrate the process using the function \(\sin(xy + x)\) of two arguments \(x\)
and \(y\)
(on the left-hand side) with temporary variables introduced on the right-hand side:
\begin{mathpar}
  z = \sin(xy + x)
  \and
  w_0 = xy; \quad w_1 = w_0 + x; \quad z = \sin w_1.
\end{mathpar}

% TODO: Turn this back into a wrapfigure once we no longer need latexdiff.
\begin{figure}
  \includegraphics{ad-example.pdf}
  \caption{\label{fig:ad-graph}Reverse AD for \(z = \sin(xy+x)\)}
\end{figure}

The individual steps of the process are depicted in Fig.~\ref{fig:ad-graph},
where the nodes represent variable definitions, and the edges connect variable
definitions with their uses, as is commonly done in the literature on automatic
differentiation. The steps of the reverse mode of automatic differentiation
compute the \textit{adjoints}\footnote{In the literature these objects can be
also called \emph{partials} or \emph{1-forms}.} \(\bar{t}\), which correspond to the partial
derivative of \(z\) with respect to \(t\), that is, \(\bar{t} = \frac{\partial
z}{\partial t}\). We denote by \(\mathtt{succ}\, t\) those variables that
reference \(t\) in their definitions (the direct neighbours of \(t\) in
Fig.~\ref{fig:ad-graph}). The chain rule provides the following formula for
computing \(\bar{t}\) for those \(t\) that have successors:
\(
\bar{t} = \sum_{u \in \mathtt{succ}\, t} \bar{u} \frac{\partial u}{\partial t}.
\)

We conceptually traverse the graph in Fig.~\ref{fig:ad-graph} from the bottom
to the top (hence the term \emph{reverse mode}) and compute the
adjoints for \(\bar{w}_1\), \(\bar{w}_0\), \(\bar{x}\), and \(\bar{y}\). Since
\(z\) does not have successors, we compute \(\bar{z}\) directly: \(\bar{z} =
\frac{\partial z}{\partial z} = 1\). It is important to note that \(x\) has two
successors; therefore, \(\bar{x}\) is the sum of \(\bar{x}_l\) and
\(\bar{x}_r\).

Let us verify the correctness of \(\bar{x}\) and \(\bar{y}\) by inlining the
adjoints of the temporary variables:
\begin{align*}
  \bar{x} &= \bar{x}_l + \bar{x}_r = \bar{w}_1 + \bar{w}_0\cdot y 
          = \cos(w_1) + \cos(w_1)\cdot y = \cos(xy +x)(1 + y)\\
  \bar{y} &= \bar{w}_0\cdot x = \bar{w}_1 \cdot x = \cos(w_1)\cdot x = \cos(xy + x)x
\end{align*}


\subsection{AD for \AD{E}}

Opposed to the above description, in the implementation we will not
introduce temporary
variables for all sub-expressions, but instead rely on existing
let bindings.  We traverse the expression with the given adjoint and
we collect partial derivatives for each variable within the context that
the expression is defined in.  When we compute derivatives for let
bindings, we ensure sharing of adjoints by introducing
new variables.
 
Technically, if some expression \AF{E} is defined in some context \AB{Γ},
we need a structure that stores all the partial derivatives with respect
to the variables in \AB{Γ}.  Each partial
derivative is an expression \AF{E} in context \AF{Γ}.  We call this
structure an \emph{environment}, and is a \AB{Γ}-long list of expressions
in context \AB{Γ} and it is given by \AF{Env}.
This  construction is
similar to our parallel substitution \AF{Sub}, except we ignore the values of index
types --- they never contribute to the computation of derivatives, so we do not need to
keep any information in the environment for them.  However, the presence of lets in \AF{E}
means that the let-bound expressions may be shared by several partial derivatives.
Replication of let bindings for every partial derivative
may lead to unnecessary code duplication which in turn results in
poor performance.  As a solution, we allow let bindings for the entire \AF{Env},
which is given by the \AF{EE} structure as follows.
\begin{mathpar}
\codeblock{\begin{code}[hide]
module AD where
  open import Data.Unit
  open import Data.Product as Prod
  open Array hiding (sum; backslide; slide)
  open WkSub
  open Lang
  open Syntax
\end{code}
\begin{code}
  data Env : Ctx → Ctx → Set where
    ε     : Env ε Γ
    skip  : Env Γ Δ → Env (Γ ▹ ix s) Δ
    _▹_   : Env Γ Δ → E Δ (ar s) → Env (Γ ▹ ar s) Δ
\end{code}}
\and
\codeblock{\begin{code}
  data EE : Ctx → Ctx → Set where
    env   : Env Γ Δ → EE Γ Δ
    let′  : E Δ (ar s) → EE Γ (Δ ▹ ar s)
          → EE Γ Δ 
\end{code}}
\end{mathpar}

We briefly explain some of the combinators that manipulate (let-extended) environments.
We can weaken environments in two ways: \AF{ee-wk} weakens each element of the environment;
\AF{ee-wk-zero} extends the length of the environment by inserting \AC{zero}
elements according to the \AF{⊆}-argument.  We can add two environments with \AF{ee-plus}
which: (i) adds elements of the environments point-wise; (ii) combines two \AF{EE} let
chains into a single one.  For the environment where elements are in the context
where the zero-th variable
is some (\AC{ix} s), \AF{ee-map-sum} applies \AF{sum} to all the elements.  Note that
here we inline let-bindings of the environment into the elements, because the bindings
may refer to the index.  This potentially leads to code duplication, but for now, we
assume that further optimisations will be able to deal with this.  We may reconsider
this choice later.  Empty environments where all the elements are
\AC{zero} are created with \AF{ee-zero}.  The top element of the environment can
be removed with \AF{ee-tail}.  We use \AF{ee-update+} \AB{ρ} \AB{i} \AB{e} to add
$e$ to the $i$-th element of the environment $ρ$ (this returns a new environment 
with the updated $i$-th position).
Finally, we extend the environment by adding \AC{zero} at the top with
\AF{\_▹𝟘}.
\begin{mathpar}
\codeblock{\begin{code}
  ee-wk       : Δ ⊆ Ψ → EE Γ Δ → EE Γ Ψ
  ee-wk-zero  : EE Γ Δ → Γ ⊆ Ψ → EE Ψ Δ
\end{code}}
\and
\codeblock{\begin{code}
  ee-plus     : (ρ ν : EE Γ Δ) → EE Γ Δ
  ee-map-sum  : EE Γ (Δ ▹ ix s) → EE Γ Δ
\end{code}}
\and
\codeblock{\begin{code}
  ee-tail     : EE (Γ ▹ is) Δ → EE Γ Δ
  ee-zero     : EE Γ Δ
\end{code}}
\and
\codeblock{\begin{code}
  ee-update+  : EE Γ Δ → ar s ∈ Γ → E Δ (ar s) → EE Γ Δ
  _▹𝟘         : EE Γ Δ → EE (Γ ▹ ar s) (Δ ▹ ar s)
\end{code}}
\end{mathpar}
\begin{code}[hide]
  -- Weaken all expressions in the Env enironment
  env-wk : Δ ⊆ Ψ → Env Γ Δ → Env Γ Ψ
  env-wk w ε = ε
  env-wk w (skip ρ) = skip (env-wk w ρ)
  env-wk w (ρ ▹ x) = env-wk w ρ ▹ wk w x

  -- Weaken all expressions in the EE environment
  ee-wk w (env x) = env (env-wk w x)
  ee-wk w (let′ x ρ) = let′ (wk w x) (ee-wk (keep w) ρ)

  -- Throw away the last element
  ee-tail (env (skip ρ)) = env ρ
  ee-tail (env (ρ ▹ _)) = env ρ
  ee-tail (let′ x ρ) = let′ x (ee-tail ρ)

  -- Insert zeroes in the environment Env according to the ⊆ content
  env-wk-zero : Env Γ Δ → Γ ⊆ Ψ → Env Ψ Δ
  env-wk-zero ρ ε = ρ
  env-wk-zero ρ (skip {is = ix x} w) = skip (env-wk-zero ρ w)
  env-wk-zero ρ (skip {is = ar x} w) = env-wk-zero ρ w ▹ zero
  env-wk-zero (skip ρ) (keep {is = ix x} w) = skip (env-wk-zero ρ w)
  env-wk-zero (ρ ▹ x₁) (keep {is = ar x} w) = env-wk-zero ρ w ▹ x₁

  -- Insert zeroes in the environment EE according to the ⊆ content
  ee-wk-zero (env ρ) w = env (env-wk-zero ρ w)
  ee-wk-zero (let′ x ρ) w = let′ x (ee-wk-zero ρ w)

  -- Add zero to the end of EE (wrapper for ee-wk-zero)
  ee-push-zero : EE Γ Δ → EE (Γ ▹ ar s) Δ
  ee-push-zero ρ = ee-wk-zero ρ (skip ⊆-eq) 

  zero-env : Env Γ Δ
  zero-env {ε} = ε
  zero-env {Γ ▹ ix x} = skip zero-env
  zero-env {Γ ▹ ar x} = zero-env ▹ zero

  ee-zero = env (zero-env)

  env-update+ : Env Γ Δ → (v : ar s ∈ Γ) → (t : E Δ (ar s)) → Env Γ Δ
  env-update+ (ρ ▹ x) v₀ t = ρ ▹ (x ⊞ t)
  env-update+ (skip ρ) (vₛ v) t = skip (env-update+ ρ v t)
  env-update+ (ρ ▹ x) (vₛ v) t = env-update+ ρ v t ▹ x

  ee-update+ (env ρ) v t = env (env-update+ ρ v t)
  ee-update+ (let′ x ρ) v t = let′ x (ee-update+ ρ v (t ↑))
 
  env-map-sum : Env Γ (Δ ▹ ix s) → Env Γ Δ
  env-map-sum ε = ε
  env-map-sum (skip ρ) = skip (env-map-sum ρ)
  env-map-sum (ρ ▹ x) = env-map-sum ρ ▹ E.sum x

  ee-fold : EE Γ Δ → Env Γ Δ
  ee-fold (env x) = x
  ee-fold {Δ = Δ} (let′ {s = s} x ρ) = map-let (ee-fold ρ)
    where map-let : ∀ {Γ} → Env Γ (Δ ▹ ar s) → Env Γ Δ 
          map-let ε = ε
          map-let (skip ν) = skip (map-let ν)
          map-let (ν ▹ e) = map-let ν ▹ let′ x e

  ee-map-sum ρ = env (env-map-sum (ee-fold ρ))

  env-plus : (ρ ν : Env Γ Δ) → Env Γ Δ
  env-plus ε ν = ν
  env-plus (skip ρ) (skip ν) = skip (env-plus ρ ν)
  env-plus (ρ ▹ x) (ν ▹ y) = env-plus ρ ν ▹ (x ⊞ y)

  {-# TERMINATING #-}  -- See GradTerm.agda file where this terminates
                       -- here we simple present a more readable version
  ee-plus (env ρ) (env ν) = env (env-plus ρ ν)
  ee-plus (env ρ) (let′ x ν) = let′ x (ee-plus (ee-wk (skip ⊆-eq) (env ρ)) ν)
  ee-plus (let′ x ρ) ν = let′ x (ee-plus ρ (ee-wk (skip ⊆-eq) ν))

  δ ▹𝟘 = ee-push-zero $ ee-wk (skip ⊆-eq) δ
\end{code}

We define\footnote{Agda does not recognise that the definition of \AF{∇} that
we give here terminates.  We fix this in the supplementary materials by choosing
an inductively decreasing invariant.  However we keep this definition in the
paper for readability.} the function (\AF{∇} $e$ $s$ $\delta$) that takes an
expression ($e$ : \AF{E} \AB{Γ} (\AC{ar} $s$)), the seed $s$ (initially set
to one), environment $\delta$ (initially set to \AF{ee-zero}) and we compute
the gradient of $e$ which is an environment that contains partial derivatives
for each variable.
We use two helper functions: (i) \AF{∇Σ} which applies \AF{sum} to all
the elements of the environment returned by the \AF{∇} call in the empty environment;
(ii) \AF{∇ₗ} which deals with the derivative of let expressions.  The code is presented
below and the explanation of how it works follow.
\begin{code}[hide]
  {-# TERMINATING #-}  -- See GradTerm.agda file where this terminates
                       -- here we simply present a more readable version.
\end{code}
\begin{code}
  ∇ₗ : E Γ (ar s) → EE (Γ ▹ ar s) Γ → EE Γ Γ
  ∇Σ : (e s : E (Γ ▹ ix s) (ar p)) → EE Γ Γ → EE Γ Γ

  ∇ : (e s : E Γ is) → EE Γ Γ → EE Γ Γ
  ∇ {is = ix _} (var x)    s   = id
  ∇ {is = ar _} (var x)    s   = λ δ → ee-update+ δ x s
  ∇ zero                   s   = id
  ∇ one                    s   = id

  ∇ (imaps e)              s   = ∇Σ e (sels     (s ↑) (var v₀))
  ∇ (imap e)               s   = ∇Σ e (sel      (s ↑) (var v₀))
  ∇ (E.imapb m e)          s   = ∇Σ e (E.selb m (s ↑) (var v₀))

  ∇ (sels e i)             s   = ∇ e (imaps     (zero-but (var v₀) (i ↑) (s ↑)))
  ∇ (sel e i)              s   = ∇ e (imap      (zero-but (var v₀) (i ↑) (s ↑)))
  ∇ (E.selb m e i)         s   = ∇ e (E.imapb m (zero-but (var v₀) (i ↑) (s ↑)))

  ∇ (E.sum e)              s   = ∇Σ e (s ↑) 
  ∇ (zero-but i j e)       s   = ∇ e (zero-but i j s) 

  ∇ (E.slide i p e su)     s   = ∇ e (E.backslide i s su p) 
  ∇ (E.backslide i e su p) s   = ∇ e (E.slide i p s su) 

  ∇ (e ⊞ e₁)               s   = ∇ e s ∘ ∇ e₁ s
  ∇ (e ⊠ e₁)               s   = ∇ e (s ⊠ e₁) ∘ ∇ e₁ (s ⊠ e)
  ∇ (scaledown x e)        s   = ∇ e (scaledown x s)
  ∇ (minus e)              s   = ∇ e (minus s)
  ∇ (logistic e)           s   = ∇ e (let′ (logistic e) ((s ↑) ⊠ var v₀ ⊠ (one ⊟ var v₀)))
  
  ∇ (let′ e e₁)            s   = λ δ → ∇ₗ e (let′ e (∇ e₁ (s ↑) (δ ▹𝟘)))

  ∇Σ e s δ = ee-plus δ $ ee-tail $ ee-map-sum (∇ e s ee-zero)

  ∇ₗ e (env (ρ ▹ x))  = ee-tail $ let′ x (∇ (e ↑) (var v₀) (env ρ ▹𝟘))
  ∇ₗ e (let′ x ρ)     = let′ x (ee-tail $ ∇ₗ (e ↑) (ee-wk-zero ρ (keep (skip ⊆-eq))))
\end{code}
\paragraph{Constants and variables} The derivative of constants (\AC{zero} and \AC{one})
is zero, so nothing needs to be updated in the environment.  Index variables are
not stored in the environment, so no updates are needed either.  If we differentiate
the variable $x$ with some seed \AB{s}, we update the $x$-th position in the environment
by incrementing it by \AB{s}.

\paragraph{Imaps} Conceptually, differentiation of \AC{imap}s proceeds as follows:
for every index $i$ of the imap index-space, we compute a derivative of $i$-th
element of $e$ with the seed $s\ i$; after that we sum-up all the environments
over the index $i$.  Technically, $e$ is an expression that may refer to the index
of the \AC{imap} which is given by the variable \AC{v₀}.  This means that $e$
is defined in a larger context (extended by the index variable) than the context
of \AC{imap} $e$.  If we inline \AF{∇Σ}, we compute \AF{∇} $e$ with the seed
$s$ selected at index \AC{v₀} (note that we had to weaken $s$, as we are in
the extended context).  At this point we have accumulated per-index changes
in the environment (over a larger context).  After that, these changes are
summed-up by applying \AC{sum} to all the elements of the environment.

While this selection-based rule might seem unusual, keep in mind that \AC{imap}s
are array constructors, which means that they potentially run different computations
on different indices.  Therefore, the effect that these computations had on the
given variable within the context have to be aggregated through summation.


\paragraph{Selections} When differentiating selections, we have to
recurse into the array expression we are selecting from. This means
that we have to create a seed that masks all the array elements except
the one that is given by the index of the selection. Hence seed
expressions in selection rules, which construct \emph{one-hot}
cotangent arrays that contains zeros everywhere except the index we
were selecting at. While this code would be asymptotically inefficient
if executed as is, the optimisations discussed later can deal reliably
with these patterns, as summing elements of such an array is exactly
the single nonzero element.

\paragraph{Conditionals} Differentiating
conditionals is straight-forward.  Both arguments $i$ and $j$ are index expressions
which have no effect on derivatives, therefore we proceed with 
differentiating $e$ with the $i == j$ predicate on the seed.  If indices were equal,
we will compute the update, otherwise we will differentiate with seed \AC{zero} which
has no effect.  As we are operating in a total language, there is no need to worry
about pulling expressions out of conditionals.

\paragraph{Arithmetic and slides} The argument of \AC{sum} is defined in the
extended context, so we apply the same rules as for the \AC{imap} family,
except we propagate the original seed to all the summands.  Addition and
multiplication rules are straight-forward application of rules of symbolic
differentiation. The \AC{slide}/\AC{backslide} pair forms a satisfying
\AF{∇}-symmetry.  Finally, \AC{scaledown}, \AC{minus} and \AC{logistic} follow
the rules of differentiation.  Note that in the definition of derivative
for logistic we use explicit de Bruin indices and weakening.

\paragraph{Let expressions} The rules for the let case look complicated due to
encoding, but their essence is easy to understand through the following example.
Consider an expression in one variable $a$ that binds a local variable $x$ to $a^2$.
The initial environment contains one position for $\partial a$, and we start
with the empty environment $\langle 0 \rangle$:
\[ 
   \AF{∇}\ (\AC{let}\ x = a^2\ \AC{in}\ (a + a)x)\ 1\ \langle 0 \rangle
\]
The first step applies \AF{∇} to the body of the let.  This
requires extending our environment with the initial (zero) value for $\partial x$.
In the environment that preserves the $x$-bound expression we compute:
\[ 
   \AF{∇}\ ((a + a)x)\ 1\ (\AC{let}\ x = a^2\ \AC{in}\ \langle 0, 0 \rangle)
   = \AC{let}\ x = a^2\ \AC{in}\ \langle x+x, a+a \rangle
\]
This exactly the call we do in the \AC{let′} case of \AF{∇}.
The next step applies the chain rule, computing the derivative of the
$x$-bound expression using the result of the previous computation as seed:
\[ 
   \AF{∇}\ a^2\ (a+a)\ (\AC{let}\ x = a^2\ \AC{in}\ \langle x+x \rangle)
   = \AC{let}\ x = a^2\ \AC{in}\ \langle x+x + a(a+a) + a(a+a) \rangle
\]
which gives the expected result $6a^2$ (we were differentiating $2a^3$ written
in a funny way).  However, direct use of $(a+a)$ as a seed in the last step
inlines the computation of the $(a+a)$ expression.  Instead, we can share 
this computation by defining a new let-binding and rearranging the call to
\AF{∇} as follows:
\[
   \AC{let}\ x = a^2\ \AC{in}\ 
   \AC{let}\ y = a+a\ \AC{in}\ 
   (\AF{∇}\ a^2\ y\ \langle x \rangle)
   = 
   \AC{let}\ x = a^2\ \AC{in}\ 
   \AC{let}\ y = a+a\ \AC{in}\
   \langle x+x + ya + ya \rangle
\]
this is exactly what \AF{∇ₗ} is doing.  It traverses under the let chain
and it shares the seed by introducing a new variable.


 
 
 
\subsection{Optimisations\label{sec:opt}}
Our rule-based AD algorithm from the previous section guarantees that its
output preserves correct shapes and that all the variables are well-scoped.
However, direct compilation of the AD-generated expressions may be
computationally inefficient.
While we can hope that the backend will take care of this, it is relatively
easy to implement a number of rewriting rules that will be applied
prior extraction.  Designing optimisations for a small DSL is much easier
than for a general-purpose language.  Also, we can leverage semantics
of \AF{E}, to formally prove that our optimisations preserve the meaning
of programs.  We demonstrate the setting and key optimisations in this section;
for further details refer to supplementary materials.

Semantics preservation proofs require several ring/field properties
of reals such as presence of neutral elements for addition and multiplication.
Similarly to \AF{⟦\_⟧}, we abstract our proofs over the collection
of properties on reals that we call \AD{RealProp} that are defined as follows:
\begin{code}[hide]
module Opt where
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open import Data.Product
  open Lang
  open WkSub
\end{code}
\begin{code}
  record RealProp (r : Real) : Set where
    open Real r; field
      +-neutˡ : ∀ {x} → 0ᵣ + x  ≡ x;  +-neutʳ : ∀ {x} → x + 0ᵣ  ≡ x
      *-neutˡ : ∀ {x} → 1ᵣ * x  ≡ x;  *-neutʳ : ∀ {x} → x * 1ᵣ  ≡ x
\end{code}
The meaning of semantics preservation is given by the \AF{\_≈ᵉ\_}
relation, which says that two expressions are equivalent if they evaluate
to equivalent values.  Equivalence of values is given by the propositional
equality of indices and extensional equality of arrays.  The type of
semantics-preserving \AF{opt}imisation function is given as follows.
\begin{code}[hide]
  postulate
    real : Real

  open Eval real
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  _≈ᵛ_ : (a b : Val is) → Set
  _≈ᵛ_ {ix s} a b = a ≡ b
  _≈ᵛ_ {ar s} a b = ∀ i → a i ≡ b i
\end{code}}
\and
\codeblock{\begin{code}
  _≈ᵉ_ : E Γ is → E Γ is → Set
  _≈ᵉ_ {Γ} a b = ⦃ ρ : Env Γ ⦄ → ⟦ a ⟧ ≈ᵛ ⟦ b ⟧
  
  opt : (e : E Γ is) → ∃[ e′ ] (e ≈ᵉ e′)
\end{code}}
\end{mathpar}
\begin{code}[hide]
  reflᵉ : ∀ (e : E Γ is) → e ≈ᵉ e
  reflᵉ {is} {ix x} = λ e → refl
  reflᵉ {is} {ar x} = λ e i → refl
  opt e = e , reflᵉ e
\end{code}

Consider the follow examples of the rewrites that we are implementing.
We omit the proofs for readability, and we omit trivial rules such
as (\AC{zero} \AF{⊞} $x \rightsquigarrow x$), but they are available in the
supplementary materials.
\begin{mathpar}
   \AC{sels}\ zero\ e \rightsquigarrow \AC{zero}
   \and
   \AC{sels}\ one\ e \rightsquigarrow \AC{one}
   \and
   \AC{sels}\ (\AC{sum}\ e)\ i \rightsquigarrow \AC{sum}\ (\AC{sels}\ e\ (i\ \AF{↑}))
   \and
   \AC{sum}\ \AC{zero} \rightsquigarrow \AC{zero}
   \and
   \AC{sum}\ (\AC{imap*}\ e) \rightsquigarrow 
   \AC{imap*}\ (\AC{sum}\ (\AF{sub}\ e\ \AF{sub-swap}))
\end{mathpar}
The last rule that swaps \AC{sum} and \AC{imap} may feel counterintuitive.
However, all it is saying is that $[a_1 + b_1, a_2 + b_2] = [a_1, a_2] + [b_1, b_2]$;
recall that \AF{sum} is shape polymorphic with respect to summands.
Moreover, we have a formal proof that justifies correctness of this rewrite.

Semantics preservation becomes especially useful in the following cases which
are not immediately obvious:
\begin{align*}
   \AC{sum}\ (\AC{zero-but}\ (\AC{var}\ i)\ (\AC{var}\ j)\ e)
   &\mathop{|} i = v_0 \wedge j = v_0
   \rightsquigarrow 
   \AC{sum}\ e
   \\
   \AC{sum}\ (\AC{zero-but}\ (\AC{var}\ i)\ (\AC{var}\ j)\ e)
   &\mathop{|} i \neq v_0 \wedge j = v_0
   \rightsquigarrow 
   \AF{sub}\ e\ (\AF{sub-id}\ \AC{▹}\ \AC{var}\ i)
   \\
   \AC{sum}\ (\AC{zero-but}\ (\AC{var}\ i)\ (\AC{var}\ j)\ e)
   &\mathop{|} i = v_0 \wedge j \neq v_0
   \rightsquigarrow 
   \AF{sub}\ e\ (\AF{sub-id}\ \AC{▹}\ \AC{var}\ j)
\end{align*}
which tell us that if we are summing-up comparisons of indices that
happen to be variables, we can check whether either of the variables
is \AC{v₀} (the index of \AC{sum}), and if this is the case we can
avoid comparison or summation. This is the crucial optimisation that
handles the one-hot arrays produced when differentiating selections.

The set of implemented rewrite rules is driven by the chosen example
and the backend compiler, therefore by no means it is complete in
any sense.  However, adding new rewrite rules is reasonably
straight-forward.


Additionally to rewrites described above, we implemented a pass that
identifies whether let bodies re-define expressions that are bound to
the let variable.  If this is the case, then the expression is substituted
by that variable.  The main reason for this is the derivative rule for
\AC{logistic} $e$, which recomputes \AC{logistic} $e$.  While
this is correct mathematically, this creates code duplication in cases
\AC{logistic} $e$ is already bound to some variable.  Instead of reusing
the variable the rule will recomputes the entire expression.
As it is difficult to tell whether the call to logistic has been bound
somewhere before, we implement a generally useful deduplication pass that
solves this problem.

One general concern for optimisation systems such as the one described
here is finding an optimal sequence of rewrites that leads to the best
performance.  This is an open problem in compiler research, and we do
not have a final answer here.  However, the following strategy seem to
work for practical cases such as our running example.  A programmer
have a control over the number of let bindings that they introduce
in the code, and all our optimisations respect these (we never inline
lets).  All the expressions within lets are aggressively inlined by
the rules described here and by normalisation defined in the next
section.

% \begin{code}[hide]
% module Opt where
%   open import Data.Nat as ℕ using (ℕ; zero; suc)
%   open Lang
%   open SubWk
%   --open Eval using (sub; ctx-swap; ↑_; ↑↑_; eq?)
%   open Array hiding (sum; slide;backslide)
%   open BB
%   open AD
% \end{code}
% \begin{code}
%   opt : E Γ is → E Γ is
%   opt (selₛ e e₁) with opt e | opt e₁
%   ... | zero            | i = zero
%   ... | one             | i = one
%   ... | imapₛ e         | i = sub v₀ e i
%   ... | bin op a b      | i = bin op (selₛ a i) (selₛ b i)
%   ... | sum e           | i = sum (selₛ e (↑ i))
%   ... | zero-but i j a  | k = zero-but i j (selₛ a k)
%   ... | a               | i = selₛ a i
% 
%   opt (sum e) with opt e
%   ... | zero            = zero
%   ... | imap a          = imap     (sum (ctx-swap v₁ a))
%   ... | imapₛ a         = imapₛ    (sum (ctx-swap v₁ a))
%   ... | imapb m a       = imapb m  (sum (ctx-swap v₁ a))
%   ... | zero-but (var i) (var j) a with eq? v₀ i | eq? v₀ j
%   ... | eq        | eq        = sum a
%   ... | neq _ i′  | eq        = sub v₀ a (var i′)
%   ... | eq        | neq _ j′  = sub v₀ a (var j′)
%   ... | neq _ i′  | neq _ j′  = zero-but (var i′) (var j′) (sum a)
%   opt (sum e) | a = sum a
%   -- ⋯
% \end{code}
% Selection into \AC{zero} and \AC{one} is \AF{zero} and \AC{one}, as our constants
% are shape-polymorphic.  Selection into an \AF{imapₛ} is evaluation of the \AC{imapₛ}
% body at the given index (this is an array version of the $\beta$-rule).  Selection
% from the binary operation is a binary operation of selections.  Selection into \AC{sum}
% is the \AC{sum} of selections.  Selection into conditional is the same as conditional
% over selection.  Summing \AC{zero} is \AC{zero}.  Summing $s$-many $p$-shaped arrays
% is the same as computing the sum of $i$-th index of every array for all $p$ indices.
% If we have a sum of the conditional with the predicate is the equality of indices
% $i$ and $j$ and we know that $i$ and $j$ are variables, we can compare the index
% variable of the \AC{sum} with $i$ and $j$.  If they match, then conditional will
% be triggered at every iteration so it can be removed.  If only one of them match,
% and we are comparing variables of the same shape, there will be exactly one case
% (for non-empty shapes) where this conditional will be triggered.  Therefore, all
% the iterations except the one at the non-matching variable will turn to zero, and
% we can simply return the expressions substituted at this variable.  If the shape
% of the index variables is empty, we are in the absurd case, as we cannot possibly
% create an element of an empty type.  Finally, if none of the variables match,
% the iteration within the \AC{sum} do not affect the result of the predicate ---
% it will be either true or false for all the iterations.  Therefore, we can lift
% the conditional outside of the sum.
% \begin{code}[hide]
%   opt zero = zero
%   opt one = one
%   
%   opt (var x) = var x
%   
%   opt (imapₛ e) = imapₛ (opt e)
%   
%   -- Literal copy of the above, replaing scalar versions
%   -- with normal one
%   opt (imap e) = imap (opt e)
%   opt (sel e e₁) with opt e | opt e₁
%   ... | zero | i = zero
%   ... | one | i = one
%   ... | imap e | i = sub v₀ e i
%   --... | imapb m e | i = ?
%   ... | bin op a b | i = bin op (sel a i) (sel b i)
%   ... | sum e | i = sum (sel e (wk v₀ i))
%   ... | zero-but i j a | k = zero-but i j (sel a k)
%   ... | a | i = sel a i
%   
%   -- Literal copy of the above for the blocked version
%   opt (imapb m e) = imapb m (opt e)
%   opt (selb m e k) with opt e
%   ... | zero = zero
%   ... | one = one
%   ... | sum e = sum (selb m e (↑ k {- var $ vₛ k-}))
%   ... | zero-but i j a = zero-but i j (selb m a k)
%   ... | bin op a b = bin op (selb m a k) (selb m b k)
%   opt (selb m e j) | a = selb m a j
%   
%   
%   opt (zero-but (var i) (var j) e) with opt e
%   ... | a with eq? i j
%   ... | eq = a
%   ... | neq _ _ = zero-but (var i) (var j) a
%   --opt (zero-but i j e) = zero-but i j (opt e)
%   
%   opt (bin plus e e₁) with opt e | opt e₁
%   ... | zero | b = b
%   ... | a | zero = a
%   ... | (zero-but i j e) | b = zero-but i j (bin plus e b)
%   ... | a | (zero-but i j e) = zero-but i j (bin plus a e)
% 
%   ... | imapₛ a | b = imapₛ (bin plus a (selₛ (↑ b) (var v₀)))
%   ... | a | imapₛ b = imapₛ (bin plus (selₛ (↑ a) (var v₀)) b)
%   ... | imap a | b = imap (bin plus a (sel (↑ b) (var v₀)))
%   ... | a | imap b = imap (bin plus (sel (↑ a) (var v₀)) b)
%   ... | imapb m a | b = imapb m (bin plus a (selb m (↑ b) (var v₀)))
%   ... | a | imapb m b = imapb m (bin plus (selb m (↑ a) (var v₀)) b)
% 
%   ... | a | b = bin plus a b
%   opt (bin mul e e₁) with opt e | opt e₁
%   ... | zero | b = zero
%   ... | a | zero = zero
%   ... | one | b = b
%   ... | a | one = a
%   ... | (zero-but i j e) | b = zero-but i j (bin mul e b)
%   ... | a | (zero-but i j e) = zero-but i j (bin mul a e)
%   
%   ... | imapₛ a | b = imapₛ (bin mul a (selₛ (↑ b) (var v₀)))
%   ... | a | imapₛ b = imapₛ (bin mul (selₛ (↑ a) (var v₀)) b)
%   ... | imap a | b = imap (bin mul a (sel (↑ b) (var v₀)))
%   ... | a | imap b = imap (bin mul (sel (↑ a) (var v₀)) b)
%   ... | imapb m a | b = imapb m (bin mul a (selb m (↑ b) (var v₀)))
%   ... | a | imapb m b = imapb m (bin mul (selb m (↑ a) (var v₀)) b)
%   
%   ... | a | b = bin mul a b
%   
%   -- XXX: not calling opt on e, as this is index
%   opt (slide i pl e su) with opt e
%   ... | zero = zero
%   ... | a = slide i pl a su
%   opt (backslide i e su pl) with opt e
%   ... | zero = zero
%   ... | a = backslide i a su pl
%   opt (scaledown x e) with opt e
%   ... | scaledown y a = scaledown (x ℕ.* y) a
%   ... | a = scaledown x a
%   -- TODO: propogate minues inside of +, *, imap, etc.
%   opt (minus e) with opt e
%   ... | minus a = a
%   ... | imapₛ a = imapₛ (minus a)
%   ... | imap a = imap (minus a)
%   ... | imapb m a = imapb m (minus a)
%   ... | sum e = sum (minus e)
%   ... | bin plus a b = bin plus (minus a) (minus b)
%   ... | bin mul a b = bin plus (minus a) b
%   ... | a = minus a
%   opt (logistic e) with opt e
%   ... | imapₛ a = imapₛ (logistic a)
%   ... | imap a = imap (logistic a)
%   ... | a = logistic a
% 
% 
%   multiopt : ℕ → E Γ is → E Γ is
%   multiopt zero e = e
%   multiopt (suc n) e = opt (multiopt n e)
% 
%   module TryOpt where
% \end{code}
% 
% Let us observe optimisation effects when computing derivatives of
% the scalar dot-product defined as follows.
% \begin{code}
%     dotp : E Γ (ar s) → E Γ (ar s) → E Γ (ar unit)
%     dotp a b = Sum λ i → selₛ (↑ a) i ⊠ selₛ (↑ b) i
% \end{code}
% \begin{code}[hide]
%     C : Ctx 
%     a : E C _ 
%     b : E C _
%     seed : E C _
% \end{code}
% We define the context \AF{C} where two top variables are of 5-element vector shape
% and the last variable (\AC{v₂}) is of scalar shape.  We bind these variables to Agda
% variables for convenience.
% \begin{code}
%     C = ε ▹  ar (ι 1)       ▹  ar (ι 5)    ▹  ar (ι 5);
%              seed = var v₂  ;  a = var v₁  ;  b  = var v₀
% \end{code}
% \begin{code}[hide]
%     ∂a     = env-ix {C} (∇ {C} (dotp a b) seed (env-zero {C})) v₁
%     ∂a′    = multiopt 3 ∂a
% \end{code}
% We compute the derivatives of \AF{dotp a b} with seed \AF{seed} and we inspect
% the $a$-th position in the returned environment that we call \AF{∂a}.  Then we repeatedly
% apply \AF{opt} (three times) to \AF{∂a} and save it in \AF{∂a′}.  We force Agda to
% verify that the content of the variables is as follows:
% \begin{code}
%     non-opt   : ∂a   ≡ (Sum λ i → zero ⊞ Imapₛ λ j → zero-but j (↑ i) (↑↑ seed ⊠ selₛ (↑↑ b) (↑ i))) ⊞ zero
%     with-opt  : ∂a′  ≡ Imapₛ λ i → (↑ seed ⊠ selₛ (↑ b) i)
% \end{code}
% \begin{code}[hide]
%     non-opt = refl
%     with-opt = refl
% -- open Lang
% -- open SubWk
% \end{code}
% As it can be seen, \AF{∂a} sums-up the arrays, where only one element is non-zero at
% every iteration.  Such a computation is highly inefficient when executed directly,
% as it needs to compute all the inner arrays before summing them up.  However, the
% optimised version correctly rewrites \AF{∂a} into \AC{imap} that multiplies
% the \AB{seed} by $b$, which is the expected answer.  This reduces complexity
% of the expression form squared to linear.
% 
\subsection{Extraction\label{sec:extraction}}

The embedded language \AF{E} serves two purposes. Firstly, \AF{E} makes it
possible to implement automatic differentiation within Agda, as we described in
the previous section. Secondly, programs in \AF{E} can be extracted into
programming languages that can generate efficient code. This section describes
extraction process into Futhark. Note that our extraction does not guarantee
correctness of the generated code. This is largely due to expediency---Futhark
is a simple language with straightforward semantics quite close to Agda, and
could be modeled using standard techniques.

Futhark is a functional language with automatic memory management and
a built-in type for arrays.  Futhark provides key array combinators such as
map and reduce, which makes the translation process straightforward.
The only boilerplate code we require from Futhark in order
to run the generated code is: implementations of operation on reals
from \AD{Real} (these are mapped into 32-bit floating point operations);
and rank-$n$ versions of the imap and sum combinators.  The latter is defined
as follows:
\begin{Verbatim}
def imap1 'a : (n: i64) -> (i64 -> a) -> [n]a =
  \n f -> map f (iota n)
def imap2 'a : (m: i64) -> (n: i64) -> (i64 -> i64 -> a) -> [m][n]a =
  \m n f -> imap m (\i -> imap n (f i))
...
def isum1 : (m: i64) -> (i64 -> real) -> real =
  \m f -> loop r = zero for i < m do r F.+ f i
def isum2 : (m: i64) -> (n: i64)
          -> (i64 -> i64 -> real) -> real =
  \m n f -> loop r = zero for i < m do r F.+ isum1 n (f i)
...
\end{Verbatim}


\paragraph{Static Ranks} As Futhark does not support rank polymorphism,
we must define imap and sum variants for every needed array rank. This also means that
it is not possible to translate an arbitrary expression in \AF{E} into
Futhark, because \AF{E} can define a function that abstracts over shapes
(which, in turn, means abstraction over ranks).  For the purpose of
extraction, we assume that all the ranks are known statically, and we
resolve possible shape abstractions during extraction.  The assumption about
static ranks holds for many numerical applications including our
running example.  Relaxing this assumption is an interesting future work.

\paragraph{Normalisation} Consider translating an expression like
\AC{sel} (\AC{imap} λ i → \AB{e}) \AB{u}.  If we were to treat arrays
as functions and selections as applications, then the above expression
could be normalised into $e[i := u]$.  One could hope that Futhark could do
such a $\beta$-reduction on the generated code, but this is not the case.
The intuition for this choice is that in Futhark arrays are tabulated
functions, and inlining arbitrary evaluation of array elements may
have a significant performance cost.  For example, in the expression
\texttt{let a = imap \textbackslash i -> }$e$ \texttt{in imap \textbackslash j -> a[f j]}, Futhark
allocates memory for $a$ and manifests elements in memory, and within the
body of the let, selection fetches array elements from memory.  If we were
to inline $a$ by replacing $a[f\ j]$ with $e[i := f\ j]$, we would loose sharing,
potentially recomputing $e$ (at index $f\ j$) much more often than needed.
\Eg{} assume that $i$ ranges over 10 elements, but $j$ over $10^5$.
Resolving when such inlining is beneficial for performance is non-trivial,
so Futhark (and many other array languages) does not inline 
computation of array elements.  For our running example, naive translation
results in too many cases when arrays are constructed just to select
a single element from them.  Therefore, we need some notion of normalisation
prior to extraction.  Note that while normalisation could have been
implemented as a part of optimisations, we implement it here because
some of the \AF{E} primitives such as \AC{slide} are implemented
through Futhark's \texttt{imap/isum}. 


We combine normalisation and extraction in a single step,
resulting in an approach that is similar to normalisation by evaluation~\cite{nbe1,nbe2}.
We model Futhark arrays as Agda functions, which makes it
easy to encode normalisation steps.
\begin{code}[hide]
module Futhark where
  open import Data.Nat.Show using () renaming (show to show-nat)
  open import Data.List as L using (List; []; _∷_)
  open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
  open import Relation.Binary.PropositionalEquality
  open import Data.String
  open import Text.Printf
  open import Data.Unit
  open import Data.Product as Prod hiding (_<*>_)
  open import Data.Nat using (ℕ; zero; suc)
  open import arrays 
  open import lang
  open import Function
  open Array hiding (Ix)
  open Lang

  open import Effect.Monad.State
  open import Effect.Monad using (RawMonad)
  open RawMonadState {{...}} -- public
  open RawMonad {{...}} -- public
  
  instance
    _ = monad
    _ = applicative
    _ = monadState
\end{code}
Futhark indices for an array of shape $s$ are given by the type \AD{Ix} which
is a list of strings where each string represents the name of the index variable
of the given dimension.
The \AF{Sem} function gives an interpretation to types of \AF{E} expressions.
Indices are interpreted as \AF{Ix} of the corresponding shape.  Array
types are morally functions from indices to strings.  However, in the definition
the type is a little more complicated:
\begin{mathpar}
\codeblock{\begin{code}
  data Ix : S → Set where 
    []  : Ix []
    _∷_ : String → Ix s → Ix (n ∷ s)
\end{code}}
\and
\codeblock{\begin{code}
  Sem : IS → Set
  Sem (ar s) = (Ix s → State ℕ ((String → String) × String))
  Sem (ix s) = Ix s
\end{code}}
\end{mathpar}
Let us explain the complexity of the array type.  First of all, the codomain
of the array is wrapped into a state monad which gives a source of fresh variable
names.  Within that monad we have a pair of a function from string to string and
a string.  The string represents the actual content of the array, whereas the
function represents a context around the array content.
This context is needed because of the interplay between let bindings and
imaps which is easy to understand from the following example.
Consider for a moment that the arrays are interpreted as \AD{Ix} $s$ → \AF{State} \AF{ℕ} \AD{String},
and we are compiling an expression:
\AF{Let} z \AF{:=} \AC{zero} \AF{in} \AF{Imaps} λ i → z.  This would
result in something like:
\begin{code}
  f : Ix s → State ℕ String
  f i = return ("let z = 0 in " ++ (λ j → "z") i)
\end{code}
Selections into $f$ are applications, and we can compose such arrays
with other functions.  However,
at a certain point we may need to turn this expression into the actual
Futhark code, which can be achieved by \AS{"imap λ i → "} \AF{++} f \AS{"i"}.
This expression evaluates to \AS{"imap λ i → let z = 0\ in z"},
which inlines the let binding computation into the body of the imap,
potentially causing performance penalty.
By introducing contexts in \AF{Sem}, we control where
we can inject the \AS{"imap"} under the let chain, obtaining
\AS{"let z = 0\ in imap λ i →  z"}.

Extraction requires an environment of Futhark values that is given by
\AF{FEnv}.  Two functions that perform most of the translation are
\AF{to-fut} which computes the \AF{Sem} value, and \AF{to-str} that
calls \AF{to-fut} and wraps the result with \texttt{imap} or \texttt{isum}
similarly to the way we described above.
\begin{mathpar}
\codeblock{\begin{code}
  FEnv : Ctx → Set
  FEnv ε = ⊤
  FEnv (Γ ▹ is) = FEnv Γ × Sem is
\end{code}}
\and
\codeblock{\begin{code}[hide]
  lookup : is ∈ Γ → FEnv Γ → Sem is
  lookup v₀ (ρ , e) = e
  lookup (vₛ x) (ρ , e) = lookup x ρ

  --show-shape : S → String
  --show-shape s = printf "[%s]" $ intersperse ", " $ L.map show-nat s

  s-list : S → List ℕ
  s-list [] = []
  s-list (n ∷ ns) = n ∷ s-list ns

  list-s : List ℕ → S
  list-s [] = []
  list-s (n ∷ ns) = n ∷ list-s ns

  shape-args : S → String
  shape-args = intersperse " " ∘ L.map show-nat ∘ s-list

  dim : S → ℕ
  dim = L.length ∘ s-list

  fresh-var : ℕ → String
  fresh-var n = "x" ++ show-nat n
  
  fresh-ix : String → Ix s
  fresh-ix n = proj₂ (runState (go n) 0)
    where
      go : String → State ℕ (Ix s)
      go {[]} n = return []
      go {x ∷ s} n = do
        c ← get
        modify suc
        is ← go {s} n
        return (printf "%s_%u" n c ∷ is)

  iv : (s : S) → State ℕ (Ix s)
  iv s = do
    c ← get
    modify suc
    return (fresh-ix (fresh-var c))

  
  -- bop : Bop -> String
  -- bop plus = "F.+"
  -- bop mul = "F.*"

  show-array-type : S → String
  show-array-type [] = "f32"
  show-array-type s = printf "%sf32" $ intersperse "" $ L.map (printf "[%s]" ∘ show-nat) (s-list s)

  _⊗ⁱ_ : Ix s → Ix p → Ix (s Ar.⊗ p)
  [] ⊗ⁱ js = js
  (i ∷ is) ⊗ⁱ js = i ∷ (is ⊗ⁱ js)
  
  splitⁱ : (ij : Ix (s Ar.⊗ p)) → Σ (Ix s) λ i → Σ (Ix p) λ j → i ⊗ⁱ j ≡ ij
  splitⁱ {[]} ij = [] , ij , refl
  splitⁱ {_ ∷ s} (x ∷ ij) with splitⁱ {s} ij
  ... | i , j , refl = (x ∷ i) , j , refl

  ix-curry : (Ix (s Ar.⊗ p) → X) → Ix s → Ix p → X
  ix-curry f i j = f (i ⊗ⁱ j)

  ix-uncurry : (Ix s → Ix p → X) → Ix (s Ar.⊗ p) → X
  ix-uncurry {s = s} f ij with splitⁱ {s} ij
  ... | i , j , refl = f i j

  ix-map : (String → String) → Ix s → Ix s
  ix-map f [] = []
  ix-map f (x ∷ i) = f x ∷ ix-map f i
  
  ix-zipwith : ((a b : String) → String) → Ix s → Ix s → Ix s
  ix-zipwith f [] [] = []
  ix-zipwith f (x ∷ i) (y ∷ j) = f x y ∷ ix-zipwith f i j


  ix-join : Ix s → String → String
  ix-join [] d = ""
  ix-join (x ∷ []) d = x
  ix-join {s = _ ∷ s} (x ∷ y ∷ xs) d = x ++ d ++ ix-join {s} (y ∷ xs) d

  ix-to-list : Ix s → List String
  ix-to-list [] = []
  ix-to-list (x ∷ xs) = x ∷ ix-to-list xs


  to-sel : Ix s → String → String
  to-sel i a = a ++ ix-join (ix-map (printf "[%s]") i) ""


  to-imap : (s : S) → (i : Ix s) → (e : String) → String
  to-imap s i e = printf "(imap%u %s (\\ %s -> %s))" 
                   (dim s) (shape-args s) (ix-join i " ")
                   e
  --to-sum : (s : S) → (i : Ix s) → (e : String) → String
  --to-sum [] i e = e
  --to-sum s  i e = printf "(sum%ud %s)" (dim s) (to-imap s i e)

  to-sum : (s : S) → (i : Ix s) → (e : String) → String
  to-sum [] i e = e
  to-sum s  i e = printf "(isum%u %s (\\ %s -> %s))" (dim s) (shape-args s)
                         (ix-join i " ") e 

  ix-plus : s + p ≈ r → (suc_≈_ p u) 
          → (i : Ix s)
          → (j : Ix u)
          → Ix r
  ix-plus []  [] [] [] = []
  ix-plus (cons ⦃ _ ⦄ ⦃ s+p ⦄) (cons ⦃ _ ⦄ ⦃ sp ⦄) (i ∷ is) (j ∷ js) =
    printf "(%s + %s)" i j ∷ ix-plus s+p sp is js

  ix-eq : (i j : Ix s) → String
  ix-eq i j = ix-join (ix-zipwith (printf "(%s == %s)") i j) " && " 

  ix-minus : s + p ≈ r → (suc_≈_ p u)
           → (i : Ix r)
           → (j : Ix s)
           → Ix u
  ix-minus []  [] [] [] = []
  ix-minus (cons ⦃ _ ⦄ ⦃ s+p ⦄) (cons ⦃ _ ⦄ ⦃ sp ⦄) (i ∷ is) (j ∷ js) =
    printf "(%s - %s)" i j ∷ ix-minus s+p sp is js


  to-div-mod : s * p ≈ q → Ix q 
             → Ix s × Ix p 
  to-div-mod []   [] = [] , []
  to-div-mod (cons {n = n} ⦃ _ ⦄ ⦃ eq ⦄) (x ∷ i) =
    -- (i: Fin (m*n)) → [p,q] : Fin [m,n] => p=i/n q=i%n
    Prod.map (printf "(%s / %s)" x (show-nat n) ∷_)
             (printf "(%s %% %s)" x (show-nat n) ∷_)
             (to-div-mod eq i)

  from-div-mod : s * p ≈ q 
               → Ix s → Ix p 
               → Ix q
  from-div-mod [] [] [] = []
  from-div-mod (cons {n = n} ⦃ _ ⦄ ⦃ eq ⦄) (i ∷ is) (j ∷ js) =
    -- (i : Fin m) (j : Fin n)  (k : Fin (m * n))  k = i * n + j  
    printf "((%s * %s) + %s)" i (show-nat n) j
    ∷ from-div-mod eq is js

  -- Generate a new name for an external array
  mkar : String → Ix s → State ℕ ((String → String) × String)
  mkar a i = return (id , to-sel i a)
\end{code}
\begin{code}
  to-fut : E Γ is → FEnv Γ → State ℕ (Sem is)
  to-str : E Γ (ar s) → FEnv Γ → State ℕ String
\end{code}}
\end{mathpar}
Consider the definition of \AF{to-fut} for \AC{imap} an \AC{sel}.
In both cases the array we are constructing or selecting from is
of shape $s ⊗ p$.  We use two helper functions \AF{ix-curry}
and \AF{ix-uncurry} that translate between functions of type
\AD{Ix (s ⊗ p)} → X and \AD{Ix} s → \AD{Ix p} → X.  In the
\AC{imap} case we generate a function that keeps let
chains within the imap expression.  In case of \AF{sel}, we
compute the array we are selecting from and the index we
are selecting at, and we bind them to variables $a$ and $i$.
After that, we construct an expression for $p$-shaped array, where
$a$ is applied to the corresponding indices.  This application
implements the normalisation step.
\begin{mathpar}
\codeblock{\begin{code}
  to-fut (imap {s = s} e) ρ = 
    return $ ix-uncurry {s} λ i j → do
      b ← to-fut e (ρ , i)
      f , b′ ← b j
      return (id , f b′)
\end{code}}
\and
\codeblock{\begin{code}
  to-fut (sel e e₁) ρ = do
     a ← to-fut e ρ
     i ← to-fut e₁ ρ
     return λ j → do
       f , a′ ← ix-curry a i j
       return (f , a′)
\end{code}}
\end{mathpar}
\begin{code}[hide]
  to-fut (var x) ρ = return $ lookup x ρ
  to-fut zero ρ = return (λ _ → return (id , "zero"))
  to-fut one ρ = return (λ _ → return (id , "one"))
  to-fut (imaps e) ρ = return λ i → do
     b ← to-fut e (ρ , i)
     f , b′ ← b []
     return (id , f b′)

     --λ i → let k = to-fut e (ρ , i) ; r = (_$ []) <$> k in join r
  to-fut (sels e e₁) ρ = do
     a ← to-fut e ρ
     x ← to-fut e₁ ρ
     return λ i → do
       f , a′ ← a x
       return (f , a′)
     --return λ _ → f x
  to-fut (E.imapb x e) ρ = return λ i → do
    let j , k = to-div-mod x i
    b ← to-fut e (ρ , j)
    f , b′ ← b k
    return (id , f b′)
  to-fut (E.selb x e e₁) ρ = do
    a ← to-fut e ρ
    i ← to-fut e₁ ρ
    return λ j → do
      let k = from-div-mod x i j
      f , a′ ← a k
      return (f , a′)
  to-fut (E.sum {s = s} e) ρ = do
    i ← iv s
    b ← to-fut e (ρ , i)
    return λ j → do
      f , b′ ← b j
      return (id , to-sum s i (f b′))
  to-fut (zero-but e e₁ e₂) ρ = do
    i ← to-fut e ρ
    j ← to-fut e₁ ρ
    a ← to-fut e₂ ρ
    return λ k → do
      f , a′ ← a k
      -- move context under if, so that we do not evaluate stuff that we do not need.
      return (id , printf "(if (%s) then %s else zero)" (ix-eq i j) (f a′))
  to-fut (E.slide e x e₁ x₁) ρ = do
    i ← to-fut e ρ
    a ← to-fut e₁ ρ
    return λ j → do
      f , a′ ← a (ix-plus x x₁ i j)
      return (f , a′)
  to-fut (E.backslide {u = u} e e₁ x x₁) ρ = do
    i ← to-fut e ρ
    a ← to-fut e₁ ρ
    return λ j → do
      let j-i = ix-minus x₁ x j i
      let j≥i = intersperse " && " (L.zipWith (printf "%s >= %s") (ix-to-list j) (ix-to-list i)) 
      let j-i<u = intersperse " && " (L.zipWith (printf "%s < %u") (ix-to-list j-i) (s-list u))

      f , a′ ← a j-i
      -- Again, move the context under if.
      let b = printf "if (%s && %s) then %s else zero"
                     j≥i j-i<u (f a′)

      return (id , b)
  to-fut (logistic e) ρ = do
    a ← to-fut e ρ
    return λ i → do
      f , a′ ← a i
      return (f ,  printf "(logistics %s)" a′)
  to-fut (e ⊞ e₁) ρ = do
    l ← to-fut e ρ
    r ← to-fut e₁ ρ
    return λ i → do
      f , l′ ← l i
      g , r′ ← r i
      return (f ∘ g , printf "(%s F.+ %s)" l′ r′)

  to-fut (e ⊠ e₁) ρ = do
    l ← to-fut e ρ
    r ← to-fut e₁ ρ
    return λ i → do
      f , l′ ← l i
      g , r′ ← r i
      return (f ∘ g , printf "(%s F.* %s)" l′ r′)

  to-fut (scaledown x e) ρ = do
    a ← to-fut e ρ
    return λ i → do
      f , a′ ← a i
      return (f ,  printf "(%s F./ fromi64 %s)" a′ (show-nat x))


  to-fut (minus e) ρ = do
    a ← to-fut e ρ
    return λ i → do
      f , a′ ← a i
      return (f ,  printf "(F.neg %s)" a′)

  to-fut (let′ e e₁) ρ = do
    c ← get
    modify suc
    let n = fresh-var c 
    b ← to-fut e₁ (ρ , (mkar n))
    return λ i → do
      x ← to-str e ρ
      f , b′ ← b i
      return (printf "(let %s = %s\nin %s)" n x ∘ f ,  b′)


  to-str {s = []} e ρ = do
    p ← to-fut e ρ
    f , b ← p []
    return (f b)
  to-str {s = s} e ρ = do
    p ← to-fut e ρ
    i ← iv s
    f , b ← p i
    return (f (to-imap s i b))
\end{code}
The rest of the code generator looks very similar, therefore we omit it
here but the full code is available in the supplementary materials.




% 
% Next, we have to take care of shapes.  Array shapes in \AF{E} are binary trees,
% but array shapes in SaC are 1-dimensional arrays (flattened binary trees).
% When some expression in \AF{E} is of product shape, we usually have to
% supply left or right subshapes of the product to SaC. These are always available
% through implicit arguments of \AF{E} constructors. Assuming that by the
% time we come to extraction, all the \AF{E} shapes are constants, we can
% always generate shape expressions in SaC.  This is implemented in \AF{show-shape}.
% Relaxing the assumption about constant shapes is possible but requires
% extension of \AF{E} so that we can always bind the shapes used in \AF{E}
% to some expressions in SaC.
% 
% We also need a source of fresh variables so that we can generate indices
% for \AC{imap} expressions.  We define a stateful function \AF{iv} that
% generates a fresh index variable.  
% 
% Extraction is given by \AF{to-sac} that translates the expression $e$ in
% the environment $\rho$.  The function is stateful so that we can generate
% fresh variables when needed.
% 
% The definitions of \AF{SEnv}, \AF{iv}, {\AF{show-shape}, and \AF{to-sac} follow.
% \begin{code}[hide]
% module Sac where
%   open import Data.Unit
%   open import Data.Product
%   open import Data.List as L using (List; []; _∷_; _++_)
%   open import Data.Nat as ℕ using (ℕ; zero; suc)
%   open import Data.Nat.Show using () renaming (show to show-nat)
%   open import Data.String hiding (_++_)
%   open import Text.Printf
%   open import Category.Monad.State --using (State; StateMonad; RawMonadState)
%   open import Category.Monad using (RawMonad)
%   --open RawMonad {{...}} public
%   open RawMonadState {{...}} public
%   open Lang
%   open Array hiding (sum; slide; backslide)
%   open SubWk
% 
%   instance
%     -- stateMon : ∀ {S : Set} → RawMonad (State S)
%     -- stateMon {S} = StateMonad S
% 
%     stateMonState : ∀ {S : Set} → RawMonadState S (State S)
%     stateMonState {S} = StateMonadState S
% \end{code}
% \begin{mathpar}
% \codeblock{\begin{code}
%   SEnv : Ctx → Set
%   SEnv ε         = ⊤
%   SEnv (Γ ▹ is)  = SEnv Γ × String
% \end{code}}
% \and
% \codeblock{\begin{code}
%   iv : S → State ℕ String
%   iv s = do  v ← get
%              modify suc
%              return $ printf "x%u" v
% \end{code}
% \begin{code}[hide]
% 
%   lookup : is ∈ Γ → SEnv Γ → String
%   lookup v₀      (ρ , e) = e
%   lookup (vₛ x)  (ρ , e) = lookup x ρ
% 
% 
%   -- show-shape : S → String
%   -- show-shape (ι x) = show-nat x
%   -- show-shape (s S.⊗ p) = printf "⟨%s, %s⟩" (show-shape s) (show-shape p)
% 
%   fresh-var : ℕ → String
%   fresh-var n = printf "x%u" n
% 
%   bop : Bop -> String
%   bop plus = "+"
%   bop mul = "*"
% 
%   dim : S → ℕ
%   dim (ι _) = 1
%   dim (s Array.⊗ p) = dim s ℕ.+ dim p
% 
%   ivl : S → State ℕ (List String)
%   ivl (ι _) = do
%     v ← get
%     modify suc
%     return $ (fresh-var v ∷ [])
%   ivl (s S.⊗ p) = do
%     l ← ivl s
%     r ← ivl p
%     return $ l L.++ r
%   
%   --iv s = printf "[%s]" ∘ intersperse ", " <$> ivl s
% \end{code}}
% \and
% \codeblock{\begin{code}
%   show-shape : S → String
%   show-shape s = printf "[%s]" 
%                $ intersperse ", " 
%                $ go s
%     where
%       go : S → List String
%       go (ι x)    = show-nat x ∷ []
%       go (s ⊗ p)  = go s ++ go p
% \end{code}}
% \and
% \codeblock{\begin{code}
%   to-sac : (e : E Γ is) → (ρ : SEnv Γ) → State ℕ String
%   to-sac (imap {s = s} e) ρ = do
%      i ← iv s
%      b ← to-sac e (ρ , i)
%      return $ printf "{ %s -> %s | %s < %s }"
%                      i b i (show-shape s)
%   to-sac (sel e e₁) ρ = 
%      printf "(%s)[%s]" <$> to-sac e ρ ⊛ to-sac e₁ ρ
%   -- ⋯
% \end{code}}
% \end{mathpar}
% \begin{code}[hide]
%   to-sac zero ρ = return "zero"
%   to-sac one ρ = return "one"
%   to-sac (var x) ρ = return $ lookup x ρ
%   to-sac (imapₛ {s = s} e) ρ = do
%      i ← iv s
%      b ← to-sac e (ρ , i)
%      let sh = show-shape s
%      --return $ printf "{ %s -> %s | %s < %s }" i b i sh
%      return $ printf "IMAPS(%s, (%s), (%s))" i b sh
%   to-sac (selₛ e e₁) ρ = do
%      a ← to-sac e ρ
%      i ← to-sac e₁ ρ
%      --return $ printf "(%s)[%s]" a i
%      return $ printf "sels(%s, %s)" a i
% 
%   -- Copy-paste from scalar versions
% 
%   -- Copy-paste from scalar versions
%   to-sac (imapb {s = s}{p} m e) ρ = do
%      i ← iv s
%      b ← to-sac e (ρ , i)
%      let sh-s = show-shape s
%      let sh-p = show-shape p
%      return $ printf "unblock({ %s -> %s | %s < %s }, %s)" i b i sh-s sh-p
%   to-sac (selb {p = p} m e e₁) ρ = do
%      a ← to-sac e ρ
%      i ← to-sac e₁ ρ
%      let sh-p = show-shape p
%      return $ printf "selb(%s, %s, %s)" a i sh-p
% 
%   to-sac (zero-but i j e) ρ 
%      = printf "%s == %s ? %s : zero" <$> (to-sac i ρ) ⊛ (to-sac j ρ) ⊛ (to-sac e ρ)
%   to-sac (sum {s = s} {p = p} e) ρ = do
%      -- outer index 
%      i ← iv s
%      -- inner index which is juts a fresh name
%      j ← iv p
%      b ← to-sac e (ρ , i)
%      -- `s` is outer shape, and `p` is the inner one
%      let sh-s = show-shape s
%      let sh-p = show-shape p
%      --return $ printf "sumOuter(%u, { %s -> %s | %s < %s})" (dim s) i b i sh-s
%      -- sumOuter(ivOuter, ivInner, e, shOuter, shInner)
%      return $ printf "sumOuter(%s, %s, %s, (%s), (%s))" i j b sh-s sh-p
%   to-sac (bin x e e₁) ρ = do
%      a ← to-sac e ρ
%      b ← to-sac e₁ ρ
%      return $ printf "(%s) %s (%s)" a (bop x) b
%   to-sac (slide {p = p} e pl e₁ su) ρ = do
%      i ← to-sac e ρ
%      a ← to-sac e₁ ρ
%      let sh-p = show-shape p
%      return $ printf "slide(%s, %s, %s)" i a sh-p
%   to-sac (backslide {r = r} e e₁ su pl) ρ = do
%      i ← to-sac e ρ
%      a ← to-sac e₁ ρ
%      let sh-sp = show-shape r
%      return $ printf "backlide(%s, %s, %s)" i a sh-sp
% 
%   to-sac (scaledown x e) ρ = do
%      a ← to-sac e ρ
%      return $ printf "(%s) / %s" a (show-nat x)
% 
%   to-sac (minus e) ρ = printf "-(%s)" <$> to-sac e ρ 
%   to-sac (logistic e) ρ = printf "logistics(%s)" <$> to-sac e ρ
% 
% 
%   -- This can be made stateful, but we are assuming that
%   -- vₛ is no need to make imap/sum index variables unique.
%   env-sac : AD.Env Γ Δ → (vars : SEnv Δ) → SEnv Γ
%   env-sac {ε} ρ σ = _
%   env-sac {Γ ▹ ix s} ρ σ = env-sac ρ σ , "--"
%   env-sac {Γ ▹ ar s} (ρ , e) σ = env-sac ρ σ , proj₁ (to-sac e σ 1)
% 
%   -- Reversed environment to list
%   env-rev-list : SEnv Γ → List String
%   env-rev-list {ε}     ρ = []
%   env-rev-list {Γ ▹ _} (ρ , x) = x ∷ env-rev-list ρ
%  
%   -- zipWith for Environments
%   zip-env : (String → String → String) → SEnv Γ → SEnv Γ → SEnv Γ
%   zip-env {ε}     f tt      tt      = tt
%   zip-env {Γ ▹ x} f (ν , n) (ρ , e) = zip-env f ν ρ , f n e
% \end{code}
% 
% \subsubsection{SaC Primitives\label{sec:sac-primitives}}
% As can be seen from the two cases of \AF{to-sac}, the extraction process is
% not complicated. In essence, we define a small snippet of SaC code for 
% each \AF{E} constructor.  Consider the \AC{imap}/\AC{sel}
% family from the code snippet.  The \AC{imap} constructor maps directly to SaC's
% tensor comprehensions~\cite{tensor-comp} expressed as: \texttt{\{ iv -> e | iv < s \}}.
% This expression constructs arrays by evaluating \texttt{e} for every array non-negative index
% vector
% \texttt{iv} whose components are element-wise smaller than the shape \texttt{s}.  The shape of the resulting
% array is concatenation of \texttt{s} and whatever the shape of \texttt{e} is.
% Selections \AC{sel} correspond to the built-in array selection using
% C-like syntax \texttt{e[iv]} where \texttt{e} is the array we are selecting
% from and \texttt{iv} is the index vector.   Shape constraints are exactly as in
% \AF{E}: if \texttt{e} is of shape \texttt{s ++ p}, and \texttt{iv} is bounded
% by \texttt{s} then \texttt{e[iv]} is of shape \texttt{p}.
% 
% Scalar versions of imap/sel require a little wrapping.  For \AC{imapₛ} we
% generate a tensor comprehension that selects inner expressions (they are
% 1-element vectors) at zero-th position.  For \AC{selₛ} we make selection into
% an array and we wrap the result in a 1-d vector:
% \begin{mathpar}
% {\begin{varwidth}{0.9\textwidth}
% \begin{lstlisting}[linewidth=.4\textwidth]
% #define IMAPS(iv, e, shp) \
%   {iv -> (e)[[0]] | iv < shp}
% \end{lstlisting}
% \end{varwidth}}
% \and
% {\begin{varwidth}{0.9\textwidth}
% \begin{lstlisting}[linewidth=.55\textwidth]
% inline float[1]
% sels(float[d:shp] x, int[d] iv)
% {
%   return [x[iv]];
% }
% \end{lstlisting}
% \end{varwidth}}
% \end{mathpar}
% When translating (\AC{imapₛ} \{ \AB{s} \} \AB{e}) we pick a fresh index variable
% \texttt{iv}, then we translate \AB{e} (in the environment extended with \texttt{iv})
% into \texttt{e'} and we generate \texttt{IMAPS(iv, e', shp)}, where \texttt{shp} is
% a translation of \texttt{s}.  On the side of SaC we expand this macro as shown
% above.  We could have expanded this macro on the Agda side, but this abstraction
% makes it possible to make adjustments in the generated code without running Agda.
% We map \AC{selₛ} into the \texttt{sels} function.  Consider the type of \texttt{sels}
% which uses the recently added feature of SaC that makes it possible to encode
% shape constraints in types~\cite{type-pattern}.  While these constraints are potentially checked at runtime,
% they are very useful for readability and they provide some confidence about the
% generated code.  The meaning of the type \texttt{float[d:shp]} is that it is
% an array of base type \texttt{float} of rank \texttt{d} and shape \texttt{shp}.
% When a variable of the same name is used within different arguments, it automatically
% triggers the equality constraint between the corresponding ranks/shapes.
% 
% \paragraph{Blocking} Implementation of \AC{selb}/\AC{imapb} pair relies on
% the notion of blocking, so we introduce the analogue to \AF{block}/\AF{unblock}
% functionality in SaC as follows:
% \begin{mathpar}
% {\begin{varwidth}{0.9\textwidth}
% \begin{lstlisting}[linewidth=.44\textwidth]
% inline float[n:s,n:p]
% block(float[n:sp] x, int[n] p)
%      | all(s*p == sp)
%      , all(p   >= 0)
% {
%   return { iv -> tile(p, iv * p, x) 
%          | iv < sp / p};
% }
% \end{lstlisting}
% \end{varwidth}}
% \and
% {\begin{varwidth}{0.9\textwidth}
% \begin{lstlisting}[linewidth=.55\textwidth]
% inline float[n:sp] 
% unblock(float[n:s,n:p] a, int[n] p)
%        | all(s*p == sp)
%        , all(p   >= 0)
% {
%   return { iv -> a[(iv / p) ++ mod (iv, p)]
%          | iv < s*p};
% }
% \end{lstlisting}
% \end{varwidth}}
% \end{mathpar}
% The type \texttt{float[n:s,n:p]} denotes an array of the shape \texttt{s ++ p}
% where \texttt{s} and \texttt{p} are of length \texttt{n}.  This is a product
% shape in terms of our array theory.  As \texttt{sp} is just a variable that
% is not related to \texttt{s} or \texttt{p}, we add two constraints (expressions
% behind the bar after the function definition) saying that: (i) \texttt{sp} is
% a point-wise product of \texttt{s} and \texttt{p}; (ii) all the elements of
% the \texttt{p}-shape are greater than zero.  Keep in mind that these are potential
% runtime constraints, they may be proved or flagged as disproved during compilation
% but they do not provide a static guarantee. The implementation of block uses the \texttt{tile}
% operation from the standard library of SaC. It selects a sub-array of the given shape at the given position.
% In \texttt{unblock} we use a division and a modulo operation to remap the indices.
% When translating \AC{selb}, we simply select into \texttt{block}-ed array.
% When translating \AC{imapb}, we use the tensor comprehension as in case of
% \AC{imap} to compute blocked array and then we call \texttt{unblock} on it.
% 
% \paragraph{Sliding} Slides and backslides are translated into calls to
% the following SaC functions:
% \begin{mathpar}
% {\begin{varwidth}{0.9\textwidth}
% \begin{lstlisting}
% inline float[d:n1] 
% slide(int[d] i, float[d:mn] x, int[d] n)       | all(n1        == n + 1)
%                                                , all(n + 1 + i <= mn)
% {
%   return { iv -> x[iv + i] | iv < n + 1 };
% }
% 
% inline float[d:mn]
% backslide(int[d] i, float[d:n1] y, int[d] mn)  | all(i < 1 + mn - n1)
% {
%   return { iv -> y[iv - i] | i <= iv < n1 + i;
%            iv -> 0f        |      iv < mn };
% }
% \end{lstlisting}
% \end{varwidth}}
% \end{mathpar}
% Shape constraints become a little bit involved here because we implicitly
% reconstruct the proof objects such as \AB{m} \AF{+} \AB{n} \AF{≈} \AB{mn}
% and \AF{suc} \AB{n} \AF{≈} \AB{n1}.  Otherwise, \texttt{slide} selects a
% sub-array of the shape (\texttt{n+1}) starting at the index \texttt{i}.
% The \texttt{backslide} populates the sub-array with the elements of
% \texttt{y} and the second partition of the tensor comprehension specifies
% that all the other indices evaluate to zero.  Translation of \AC{slide}
% and \AC{backslide} maps the arguments one-to-one, additionally providing
% the $n$-shape in case of slide and the $(m+n)$ shape in case of backslide.
% 
% \paragraph{Summation} When translating (\AC{sum} \{\AB{s}\} \AB{e}), where
% \AB{e} is of shape \AB{p} (and the index variable within the \AC{sum} is
% bounded by \AB{s}), we map these arguments into the following SaC function:
% \begin{lstlisting}
% inline float[n:p] sumOuter(float[m:s,n:p] a, int[m] s, int[n] p) {
%   return { jv -> sum({iv -> a[iv++jv] | iv < s}) | jv < p };
% }
% \end{lstlisting}
% We use SaC's builtin \texttt{sum} function that sums-up all the elements
% of the given array.
% 
% The rest of the constructions are mapped into regular arithmetic operations
% that are provided by SaC.
% 
% 
% \subsection{Local Variables}
% 
% The framework that we built so far computes derivatives of the variables in
% the context.  This means that for complex expressions in \AF{E} (such as \AF{forward}),
% all the let bindings will be inlined.  This is often not desirable both for performance
% and readability.  Here we present a mechanism that introduce local variables
% and preserves them during AD.
% \begin{code}[hide]
% module DoubleChain where
%   -- In this module I want to preserve derivatives
%   -- of the local variables in the chain (instead of inlining them)
%   open import Data.String
%   open import Text.Printf
%   open import Data.Product --using (Σ; _×_; _,_)
%   open import Data.Unit
%   open import Data.Nat as ℕ using (ℕ; zero; suc)
%   open import Data.List as L using (List; []; _∷_)
%   open Array hiding (sum; slide; backslide)
%   open Lang
%   open SubWk
%   open AD
%   open Opt
%   open BB
% 
%   Env′ : Ctx → Set
%   Env′ Γ = Env Γ Γ
% \end{code}
% 
% The key data structure that makes it possible to introduce local variables
% is called \AF{Chain} which has two constructors.  The empty chain consists
% of the names for all the variables in the context \AB{Γ}.  This represents the
% case where no local variables have been introduced.  The \AC{\_▹\_} constructor
% takes a chain in context \AB{Δ} and the array expression of shape \AB{p} in
% the same context together with the variable name.  This produces the chain
% in the context extended by two variables.  One variable is a place-holder
% for the expression and the other variable is a placeholder for the derivative
% of that expression.
% \begin{code}
%   data Chain : Ctx → Set where
%     ε    : Sac.SEnv Γ → Chain Γ
%     _▹_  : Chain Δ → (String × E Δ (ar p)) → Chain (Δ ▹ ar p ▹ ar p)
% \end{code}
% 
% The computation of the derivative in \AF{Chain}s follows the following
% simple idea.  Consider the chain with two variables $a$ and
% $b$ in the initial context \AB{Γ}, and two local variables $x$ and $y$.
% Here is what happens when we compute the derivative of some expression
% $e$ (that may depend on $a$, $b$, $x$, $y$) with some seed $s$ in the
% empty $\delta_0$ environment. 
% 
% %\begin{table}
% \begin{center}
% \begin{tabular}{cc|cccc|l}
%    $a$         &$b$         &$\partial{x}$& $x$         &$\partial{y}$&$y$       & \text{compute $\nabla\ e\ s\ \delta_0$}\\
%    \hline
%    $\delta_a$  &$\delta_b$  &-            & $\delta_x$  &-            &$\delta_y$& \text{assign $\delta_y$ to $\partial{y}$}\\
%    $\delta_a$  &$\delta_b$  &-            & $\delta_x$  &$\delta_y$   &$\delta_y$& \text{compute $\nabla\ y_e\ \partial{y}$}\\
%    $\delta'_a$ &$\delta'_b$ &-            & $\delta'_x$ &$\delta_y$   &$\delta_y$& \text{assign $\delta'_x$ to $\partial{x}$}\\
%    $\delta'_a$ &$\delta'_b$ &-            & $\delta'_x$ &$\delta_y$   &$\delta_y$& \text{compute $\nabla\ x_e\ \partial{x}$}\\
%    $\delta''_a$ &$\delta''_b$ &$\delta'_x$  & $\delta'_x$ &$\delta_y$   &$\delta_y$& \text{done}
% \end{tabular}
% \end{center}
% %\end{table}
% 
% First of all, the computation of $e$ returns the environment $\delta$ that can
% be found in the first line of the table.  Then we repeat the following steps while
% traversing the chain backwards: we copy the $y$-th position of the $\delta$-environment
% to the $\partial{y}$-th position, and we compute the expression $y_e$ that is assigned to $y$
% ($xx$ in this case) with the seed $\partial{y}$-th variable.  Just to clarify, the seed
% is the variable $\partial{y}$ and not its value.  Then we repeat the same process
% for $x$ and potentially all the other remaining local variables (not in this case) until
% we hit the beginning of the chain.
% 
% At the end of the process we obtain an environment where derivatives for $a$ and
% $b$ are expressed in terms of $\partial{x}$ and $\partial{y}$.  The remaining step
% is to collect the values of $\partial{x}$ and $\partial{y}$ which can be found
% at the corresponding positions in the $\delta$-environment.
% \begin{code}[hide]
%   data LCtx : Set where
%     []  : LCtx
%     _◃_ : IS → LCtx → LCtx
% 
%   _<><_ : Ctx → LCtx → Ctx
%   Γ <>< [] = Γ
%   Γ <>< (x ◃ Δ) = (Γ ▹ x) <>< Δ
% 
%   data LEnv : LCtx → Ctx → Set where
%     []  : LEnv [] Γ
%     _◃_ : ∀ {Δ′} → E Γ (ar s) → LEnv Δ′ Γ → LEnv (ar s ◃ Δ′) Γ
% 
%   data Postfix : Ctx → Ctx → Set where
%     done : Postfix ε Γ
%     next : Postfix Γ Δ → Postfix (Γ ▹ ar s) (Δ ▹ ar s)
% 
%   double-ctx : Ctx → Ctx
%   double-ctx ε = ε
%   double-ctx (Γ ▹ x) = double-ctx Γ ▹ x ▹ x
% 
%   chain-to-env : Chain Γ → Σ Ctx λ Δ → Env (double-ctx Δ) Γ × Postfix (double-ctx Δ) Γ
%   chain-to-env (ε x)   = ε , tt , done
%   chain-to-env (_▹_ {p = p} c (_ , x)) = let
%     Δ , ρ , po = chain-to-env c
%     in (Δ ▹ ar p) , ((env-map {Γ = double-ctx Δ} (↑↑_) ρ , zero) , (↑ ↑ x)) , (next (next po))
% 
%   pstep : ∀ {Δ′} → Postfix ((Δ ▹ ar s) <>< Δ′) Γ → Postfix (Δ <>< (ar s ◃ Δ′)) Γ
%   pstep {Δ′ = []} (next p) = next p
%   pstep {Δ′ = x ◃ Δ′} p = p
% 
%   post-var : ∀ {Δ′} → Postfix (Δ <>< Δ′) Γ → is ∈ Δ → is ∈ Γ
%   post-var {Δ′ = []} (next p) v₀ = v₀
%   post-var {Δ′ = []} (next p) (vₛ x) = vₛ (post-var {Δ′ = []} p x)
%   post-var {Δ′ = is ◃ Δ′} p x = post-var {Δ′ = Δ′} p (vₛ x)
% 
%   no-ix : ix s ∈ Δ → ¬ Postfix Δ Γ
%   no-ix v₀ = λ ()
%   no-ix (vₛ v) (next p) = no-ix v p
% 
%   post-fish : ∀ Δ′ → is ∈ Δ → is ∈ (Δ <>< Δ′)
%   post-fish [] v = v
%   post-fish (x ◃ Δ′) v = post-fish Δ′ (vₛ v)
% 
%   gradc : ∀ {Δ′} → Env (double-ctx Δ) Γ → LEnv Δ′ Γ 
%             → Postfix ((double-ctx Δ) <>< Δ′) Γ →  Env′ Γ → Env′ Γ
%   gradc {ε}        {Γ} {Δ′} ρ ρ′ p δ = δ
%   gradc {Δ ▹ ix x} {Γ} {Δ′} ρ ρ′ p δ = ⊥-elim (no-ix (post-fish Δ′ v₀) p)
%   gradc {Δ ▹ ar x} {Γ} {Δ′} ((ρ , z) , e) ρ′ p δ =
%     let
%     ve = post-var {Δ′ = Δ′} p v₀  -- variable for e in Γ
%     vz = post-var {Δ′ = Δ′} p v₁  -- variable for z in Γ
%     s  = env-ix δ ve
%     δ₁ = update δ vz (const s)    -- save s in the z's position
%     δ₂ = ∇ e (var vz) δ₁          -- use vz position as seed
%     in gradc {Δ} ρ (z ◃ (e ◃ ρ′)) (pstep {Δ′ = ar x ◃ Δ′} (pstep {Δ′ = Δ′} p)) δ₂
% 
%   chain-grad : Chain (Γ ▹ ar s) → E (Γ ▹ ar s) (ar s) → Env′ (Γ ▹ ar s)
%   chain-grad {Γ} {s} c seed = let
%     -- Well, this is a choice I suppose
%     --δ = ∇ seed one (env-imap {Γ = Γ ▹ ar s} (const zero))
%     δ = env-imap {Γ = Γ} (const zero) , seed
%     Δ , ρ , po = chain-to-env c
%     in env-map {Γ = Γ ▹ ar s} (multiopt 10) $ gradc ρ [] po δ
% 
%   chain-sac-ctx : Chain Γ → Sac.SEnv Γ
%   chain-sac-ctx (ε x) = x
%   chain-sac-ctx (c ▹ (v , _)) = chain-sac-ctx c ,, ("∂/∂" ++ v) ,, v
%   
%   filter-grad : Chain Γ → Sac.SEnv Γ → List String 
%   filter-grad (ε x)   δ = Sac.env-rev-list δ
%   filter-grad (c ▹ _) ((δ , _), x) = x ∷ filter-grad c δ
% 
%   chain-grad-sac : Chain Γ → Env′ Γ → String
%   chain-grad-sac {Γ} c δ = let
%     vars = chain-sac-ctx c
%     vals = Sac.env-sac {Γ} δ vars
%     assignments = filter-grad c $ Sac.zip-env (printf "∂/∂%s = %s;") vars vals
%     in intersperse "\n" assignments
% 
%   chain-sac-l : Chain Γ → ℕ → List String 
%   chain-sac-l (ε x) _ = []
%   chain-sac-l (c ▹ (v , e)) n = let r , n′ = Sac.to-sac (multiopt 10 e) (chain-sac-ctx c) n 
%                                 in printf "%s = %s;" v r ∷ chain-sac-l c n′
% 
%   chain-sac : Chain Γ → String
%   chain-sac c = intersperse "\n" $ L.reverse $ chain-sac-l c 1
% 
% 
%   -- test-chain : Chain _ --(ε ▹ ar (ι 3))
%   -- test-chain = ε {Γ = ε ▹ ar (ι 3)} (_ ,, "a") 
%   --            ▹ ("r" , mul-test)
%   --            ▹ ("r₁" , (var v₀) ⊠ (var v₂))
% 
%   -- test-grad : String
%   -- test-grad = chain-sac test-chain 
%   --             ++ "\n" ++ chain-grad-sac test-chain (chain-grad test-chain one)
% \end{code}
% 
% Let us consider a small example to see this in action.  We start with a little
% convenience data structure \AF{ChainCtx} that keeps the shapes and the variable names
% together.  We also define the function \AF{ce-split} that splits 
% \AF{ChainCtx} into the context and the environment with variable names in that context:
% \begin{code}
%   data ChainCtx : Set where
%     ε : ChainCtx
%     _▹_ : ChainCtx → String × S → ChainCtx
% 
%   ce-split : ChainCtx → Σ Ctx Sac.SEnv
% \end{code}
% \begin{code}[hide]
%   ce-split ε = ε , tt
%   ce-split (cx ▹ (v , s)) = let Δ , ρ = ce-split cx in (Δ ▹ ar s) , (ρ , v)
% 
%   Product : ℕ → Set → Set
%   Product 0       A = ⊤
%   Product 1       A = A
%   Product (suc n) A = A × Product n A
% 
%   Es : ∀ {Γ : Ctx} → (n : ℕ) → {Product n IS} → Set
%   Es {Γ} 0             {is} = ⊤
%   Es {Γ} 1             {is} = E Γ is
%   Es {Γ} (suc (suc n)) {is , p}  = E Γ is × Es {Γ} (suc n) {p}
% 
%   ↑↑ₙ : ∀ {Γ : Ctx} {is} n {p : Product n IS} → Es {Γ} n {p} → Es {Γ ▹ is ▹ is} n {p}
%   ↑↑ₙ 0 es = _
%   ↑↑ₙ 1 e  = ↑↑ e
%   ↑↑ₙ (suc (suc n)) (e , es) = ↑↑ e , ↑↑ₙ (suc n) es
% \end{code}
% Consider an initial environment of two 5-element vectors $a$ and $b$; local
% computations $x = ab$ and $y = xx$; and the generated code when computing derivative
% of $y$ (\AC{var v₀}) on the right.
% \begin{mathpar}
% \codeblock{\begin{code}
%   test-chain : Chain _
%   test-chain = let
%     Γ , ρ = ce-split (ε ▹ ("a" , ι 5) ▹ ("b" , ι 5))
%     a = var v₁; b = var v₀
%     C₁ = ε {Γ} ρ  ▹ ("x" , a ⊠ b)
%     x = var v₀
%     C₂ = C₁       ▹ ("y" , x ⊠ x)
%     in C₂
% \end{code}}
% \and
% {\begin{varwidth}{0.9\textwidth}
% \begin{lstlisting}[linewidth=.44\textwidth]
% x = (a) * (b);
% y = (x) * (x);
% ddy = one;
% ddx = ((ddy) * (x)) + ((ddy) * (x));
% ddb = (ddx) * (a);
% dda = (ddx) * (b);
% \end{lstlisting}
% \end{varwidth}}
% \end{mathpar}
% Let us convince ourselves that the result is correct.  Our expression is $abab = a^2b^2$,
% and its partial derivatives $\frac{\partial}{\partial a} = 2ab^2$,
% $\frac{\partial}{\partial b} = 2ba^2$.  If we fold the assignments, we get:
% \begin{eqnarray*}
%    \text{dda} &= (x + x)b = (ab + ab)b = 2ab^2\\
%    \text{ddb} &= (x + x)a = (ab + ab)a = 2ba^2
% \end{eqnarray*}
% Note that computations in $x$ and \texttt{ddx} are shared in further computations
% which was the main goal of introducing this mechanism.
% 
% There are two inconveniences in the above implementation that we would like to
% mention:
% \begin{enumerate}
% \item There is no restriction on using the placeholders for derivatives in the 
% chain expressions, so in principle, one could write expression in terms of
% variables and their derivatives.  However, this is not being handled and likely
% to generate bogus terms.  If this is a useful feature, it requires more thinking
% on how exactly it should work.  Otherwise it is easy to introduce restrictions
% that rule out such cases.
% \item If we define variables in the chain that do not contribute to the final
% expression, we may introduce extra computations.  We do not compromise correctness,
% as all inaccessible terms will get zero value.  However, direct execution of the
% resulting expressions may introduce redundant computations.
% \end{enumerate}
% Both of these are future work.  For now, we make an assumption that placeholders
% are not used in the expressions and that we do not insert bindings that do not
% contribute to the final result.
% 
% \begin{code}[hide]
%   test-chain-sac : String
%   test-chain-sac
%     = chain-sac test-chain 
%              ++ "\n" ++ chain-grad-sac test-chain (chain-grad test-chain (one))
% 
% \end{code}
% 
% We present the specification of our case study in \AF{E} using \AF{Chain}.  We start
% with the context \AF{cnn-ctx} that contains the \texttt{target} digit that
% is depicted on the image, the input image \texttt{inp} and the weights of the network.
% The definition of the chain is a one-to-one copy of the definition found in
% Section~\ref{sec:cnn}.  The only real difference is that we have to take care of
% maintaining bindings between Agda variables and the variables in \AF{E}.  Fortunately,
% let expressions in Agda make it possible to shadow the binding, which comes very
% useful in this case.
% 
% {\small
% \begin{code}
%   cnn-ctx : ChainCtx
%   cnn-ctx  = ε
%            ▹ ("target"  , ι 10 ⊗ (ι 1 ⊗ (ι 1 ⊗ (ι 1 ⊗ ι 1))))     -- 7
%            ▹ ("inp"     , ι 28 ⊗ ι 28)                            -- 6
%            ▹ ("k₁"      , ι 6 ⊗ (ι 5 ⊗ ι 5))                      -- 5
%            ▹ ("b₁"      , ι 6)                                    -- 4
%            ▹ ("k₂"      , ι 12 ⊗ (ι 6 ⊗ (ι 5 ⊗ ι 5)))             -- 3
%            ▹ ("b₂"      , ι 12)                                   -- 2
%            ▹ ("fc"      , ι 10 ⊗ (ι 12 ⊗ (ι 1 ⊗ (ι 4 ⊗ ι 4))))    -- 1
%            ▹ ("b"       , ι 10)                                   -- 0
% 
%   cnn-chain : Chain _
%   cnn-chain = let 
%       Γ , ρ = ce-split cnn-ctx 
%       inp = var v₆; k₁ = var v₅; b₁ = var v₄; k₂ = var v₃; b₂ = var v₂; fc = var v₁; b = var v₀
%       C₁ = ε {Γ} ρ ▹ ("c₁₁" , mconv (ι ⊗ ι) inp k₁ b₁ (ι ⊗ ι));        k₂ = ↑↑ k₂; b₂ = ↑↑ b₂;  fc = ↑↑ fc; b = ↑↑ b; c₁₁ = var v₀
%       C₂ = C₁ ▹ ("c₁"  , logistic c₁₁);                                k₂ = ↑↑ k₂; b₂ = ↑↑ b₂;  fc = ↑↑ fc; b = ↑↑ b; c₁ = var v₀
%       C₃ = C₂ ▹ ("s₁"  , Imap λ i → avgp₂ 12 12 (sel (↑ c₁) i));       k₂ = ↑↑ k₂; b₂ = ↑↑ b₂;  fc = ↑↑ fc; b = ↑↑ b; s₁ = var v₀
%       C₄ = C₃ ▹ ("c₂₁" , mconv (ι ⊗ (ι ⊗ ι)) s₁ k₂ b₂ (ι ⊗ (ι ⊗ ι)));                           fc = ↑↑ fc; b = ↑↑ b; c₂₁ = var v₀
%       C₅ = C₄ ▹ ("c₂"  , logistic c₂₁);                                                         fc = ↑↑ fc; b = ↑↑ b; c₂ = var v₀
%       C₆ = C₅ ▹ ("s₂"  , Imap λ i → Imap λ j → avgp₂ 4 4 (sel (sel (↑↑ c₂) (↑ i)) j));          fc = ↑↑ fc; b = ↑↑ b; s₂ = var v₀
%       C₇ = C₆ ▹ ("r₁"  , mconv (ι ⊗ (ι ⊗ (ι ⊗ ι))) s₂ fc b (ι ⊗ (ι ⊗ (ι ⊗ ι))));                r₁ = var v₀
%       C₈ = C₇ ▹ ("r"   , logistic r₁)
%       in C₈
% \end{code}
% 
% \begin{code}[hide]
%   test-cnn : String
%   test-cnn 
%     = let
%         -- 2*8 + 7 = 23
%         target = ↑↑ ↑↑ ↑↑ ↑↑ ↑↑  ↑↑ ↑↑ ↑↑ ↑↑ ↑↑  ↑↑ ↑ (var v₀)
%       in chain-sac cnn-chain 
%              ++ "\n" ++ chain-grad-sac cnn-chain (chain-grad cnn-chain (var v₀ ⊞ minus target))
% \end{code}
% }
% 
