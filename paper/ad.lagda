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

We implement automatic differentiation in reverse mode
for expressions in \AF{E}.  We focus on reverse mode because it is
of most interest in machine learning, and it is more challenging to implement.
We start with a brief introduction of the AD, for much more in-depth
explanations refer to~\cite{autodiff-survey, backprop-stlc}.   Consider differentiating
a function composition consisting of three functions:
\[ 
   y = (f \circ g \circ h)\ x
\]
rewrite it using temporary variables:
\begin{eqnarray*}
  w_0 &=& x \\
  w_1 &=& h\ w_0 \\
  w_2 &=& g\ w_1 \\
  w_3 &=& f\ w_2 = y
\end{eqnarray*}
The chain rule gives us 
$\frac{\partial y}{\partial x} 
  = \frac{\partial y}{\partial w_2}
    \frac{\partial w_2}{\partial w_1}
    \frac{\partial w_1}{\partial x}$.  The difference between the forward and reverse
    mode lies in the direction that we traverse the chain rule.  In forward mode we
    traverse the chain inside-out, and the revers mode traverses the chain outside-in
    thus computing recursive relation:
$\frac{\partial y}{\partial w_i}
  = \frac{\partial y}{\partial w_{i+1}}
    \frac{\partial w_{i+1}}{\partial w_i}$.  For our example, we compute
$\frac{\partial y}{\partial w_2}$, then $\frac{\partial w_2}{\partial w_1}$ and
finally $\frac{\partial w_1}{\partial x}$.  While there seem to be no difference for
functions of one variable, there is a big difference for functions of $n$ variables
as we can compute derivatives of all the non-dependent variables simultaneously.
Consider an example of the $z = f\ x\ y = sin(xy + x)$:
\begin{eqnarray*}
  w_0 &=& x \\
  w_1 &=& y \\
  w_2 &=& w_1w_2\\
  w_3 &=& w_2 + w_0 \\
  w_4 &=& \sin w_3 = z
\end{eqnarray*}
We compute the adjoints $\bar{w}_i = \frac{\partial y}{\partial w_i}$ using the following
rule.  If $w_i$ has successors in the computational graph, we can apply the chain rule
as follows:
\[ 
    \bar{w}_i = \sum_{j \in succ\ i} \bar{w}_j\frac{\partial w_j}{\partial w_i}
\]
For our example:
\begin{eqnarray*}
  \bar{w}_4 &=& 1 = \frac{\partial z}{\partial z} \\
  \bar{w}_3 &=& \bar{w}_4 \cos w_3\\
  \bar{w}_2 &=& \bar{w}_3 \cdot 1 \\
  \bar{w}_1 &=& \bar{w}_2 w_0 \\
  \bar{w}_0 &=& \bar{w}_3 + \bar{w}_2 w_1
\end{eqnarray*}
If we inline all the $\bar{w}_i$ definitions and inspect the values of partial derivatives
with respect to $x$ and $y$ we obtain expected results:
$\frac{\partial z}{\partial x} = \cos (xy + x)(y + 1)$ and
$\frac{\partial z}{\partial y} = \cos (xy + x)x$.


In the implementation of the AD for \AF{E} in some context \AB{Γ}, we would like to obtain
all the partial derivatives with respect to the variables in context \AB{Γ}.  Each partial
derivative is itself an expression \AF{E} in context \AF{Γ}.  Therefore, we need to define
a data type for an environment of \AB{Γ}-many expressions in context \AB{Γ}.  We call this
environment \AF{Env} defined as follows:
\begin{code}[hide]
module AD where
  open import Data.Unit
  open import Data.Product as Prod
  open Array hiding (sum; backslide; slide)
  open SubWk using (wk; ↑_; ↑↑_)
  open Lang

  -- Left-associated pairing
  infixl 4 _,,_
  _,,_ : X → Y → X × Y
  _,,_ = Prod._,′_
\end{code}
\begin{code}
  Env : Ctx → Ctx → Set
  Env ε           Δ  = ⊤
  Env (Γ ▹ ar s)  Δ  = Env Γ Δ × E Δ (ar s)
  Env (Γ ▹ ix s)  Δ  = Env Γ Δ
\end{code}
Note that \AF{Env} only keeps array expressions, as (i) derivatives for indices do
not exist; and (ii) we can always make an initial environment by populating all the
elements with \AC{zero}s.  

We define several helper operations to manipulate environments: \AF{env-zero} is 
an environment where all the values are \AC{zero}s; \AF{update} modifies the 
expression at the $v$-th position by applying $f$ to it; \AF{env-map} applies the function
$f$ from \AF{E} to \AF{E} to all the elements of the environment; and \AF{env-zipWith}
applies the binary function $f$ on two environments point-wise.  The types of these
helper functions follow.  As environments are very similar to lists, the implementation
of the above functions are straight-forward.
\begin{code}
  env-zero : Env Γ Δ
  update : Env Γ Δ → (v : ar s ∈ Γ) → (f : E Δ (ar s) → E Δ (ar s)) → Env Γ Δ
  env-map : ∀ {Γ Δ Ψ} → (f : ∀ {s} → E Δ (ar s) → E Ψ (ar s)) → Env Γ Δ → Env Γ Ψ
  env-zipWith  : ∀ {Γ Δ Ψ Ξ} → (f : ∀ {s} → E Δ (ar s) → E Ψ (ar s) → E Ξ (ar s)) 
               → Env Γ Δ → Env Γ Ψ → Env Γ Ξ
\end{code}
\begin{code}[hide]
  update {Γ ▹ ar s} (ρ , e) v₀ f = ρ , f e
  update {Γ ▹ ix s} ρ (vₛ x) f = update ρ x f
  update {Γ ▹ ar s} (ρ , e) (vₛ x) f = update ρ x f , e

  env-ix : Env Γ Δ → (ix : (ar s) ∈ Γ) → E Δ (ar s)
  env-ix {Γ ▹ ix s} ρ (vₛ x) = env-ix ρ x
  env-ix {Γ ▹ ar s} (ρ , e) v₀ = e
  env-ix {Γ ▹ ar s} (ρ , e) (vₛ x) = env-ix ρ x

  -- Update array values in the environment
  env-imap : (∀ {s} → (ar s) ∈ Γ → E Δ (ar s)) → Env Γ Δ --→ Env Γ Δ
  env-imap {Γ = ε}     f = tt
  env-imap {Γ = Γ ▹ ar s} f = env-imap (f ∘ vₛ) , f v₀
  env-imap {Γ = Γ ▹ ix s} f = env-imap (f ∘ vₛ)

  env-map {Γ = ε} f ρ = tt
  env-map {Γ = Γ ▹ ix s} f ρ = env-map {Γ = Γ} f ρ
  env-map {Γ = Γ ▹ ar s} f (ρ , e) = env-map {Γ = Γ} f ρ , f e

  env-zero {ε} = _
  env-zero {Γ ▹ ix x} = env-zero {Γ}
  env-zero {Γ ▹ ar x} = env-zero {Γ} , zero

  env-zipWith {ε} f l r = _
  env-zipWith {Γ ▹ ix x} f l r = env-zipWith {Γ} f l r
  env-zipWith {Γ ▹ ar x} f (l , e₁) (r , e₂) = env-zipWith {Γ} f l r , f e₁ e₂
\end{code}

We define the function \AF{∇} that takes an expression \AF{E} and the seed
which is the multiplier on the left of the chain, and we compute a function
from that updates the environment.
\begin{code}
  ∇ : E Δ is → (seed : E Δ is) → Env Δ Δ → Env Δ Δ

  map-sum : (e s : E (Δ ▹ ix s) ip) → Env Δ Δ → Env Δ Δ
  map-sum {Δ} e s δ = env-zipWith {Δ} _⊞_ (env-map {Δ} sum (∇ e s (env-zero {Δ}))) δ

  ∇ (zero)                 s δ = δ
  ∇ (one)                  s δ = δ
  ∇ (var {ix _} x)         s δ = δ
  ∇ (var {ar _} x)         s δ = update δ x (_⊞ s)

  ∇ (imapₛ e)              s   = map-sum e (selₛ    (↑ s) (var v₀))
  ∇ (imap e)               s   = map-sum e (sel     (↑ s) (var v₀))
  ∇ (imapb m e)            s   = map-sum e (selb m  (↑ s) (var v₀))

  ∇ (selₛ e i)             s   = ∇ e (imapₛ    (zero-but (var v₀) (↑ i) (↑ s)))
  ∇ (sel e i)              s   = ∇ e (imap     (zero-but (var v₀) (↑ i) (↑ s)))
  ∇ (selb m e i)           s   = ∇ e (imapb m  (zero-but (var v₀) (↑ i) (↑ s)))

  ∇ (zero-but i j e)       s   = ∇ e (zero-but i j s)
  ∇ (sum e)                s   = map-sum e (↑ s)

  ∇ (e ⊞ e₁)               s   = ∇ e s ∘ ∇ e₁ s
  ∇ (e ⊠ e₁)               s   = ∇ e (s ⊠ e₁) ∘ ∇ e₁ (s ⊠ e)
  ∇ (slide i pl e su)      s   = ∇ e (backslide i s su pl)
  ∇ (backslide i e su pl)  s   = ∇ e (slide i pl s su)

  ∇ (scaledown x e)        s   = ∇ e (scaledown x s)
  ∇ (minus e)              s   = ∇ e (minus s)
  ∇ (logistic e)           s   = ∇ e (s ⊠ logistic e ⊠ (one ⊞ minus (logistic e)))
\end{code}
Let us now walk through the cases.  Derivative of constants (\AC{zero} and \AC{one})
is zero, so nothing needs to be updated in the environment.  Index variables are
not stored in the environment, so no updates are needed either.  If we differentiate
the variable $x$ with some seed \AB{s}, we update the $x$-th position in the environment
by adding \AB{s} to it.  Differentiation of \AC{imap}s proceeds as follows: we
recursively apply \AF{∇} to $e$ (in the context \AB{Γ} \AC{▹} (\AC{ix} \AB{p}))
with the element of the original seed \AB{s} selected at the top variable.  This
gives us the environment in the extended context, then we map \AC{sum} to every
element of the environment to accumulate the derivatives at every index.
When differentiating selections we recurse on the array we are
selecting from with the seed that is zero everywhere except the index we were
selecting at.  Differentiating
conditional is straight-forward, as $i$ and $j$ must be in the context, we can
simply differentiate $e$ with the condition on seed.  If indices were equal, we will
compute the update, otherwise we will differentiate with seed \AC{zero} which
has no effect.  As we are operating in a total language, there is no need to worry
about pulling the expression out of conditional.  The argument of \AC{sum}
lives is in the extended context, so we apply the same rules as for the \AC{imap} family,
except we propagate the original seed to all the summands.  Addition and multiplication
rules are straight-forward application of differentiation rules.  The \AC{slide}/\AC{backslide}
pair forms a satisfying \AF{∇}-symmetry.  Finally, \AC{scaledown}, \AC{minus} and
\AC{logistic} follow the rules of differentiation.





\subsection{Optimisation\label{sec:opt}}

Our algorithm often delivers expressions that are not computationally efficient.
While we can hope for the backend to take care of this, it is relatively
easy to implement a number of rewriting rules prior to extraction.  
We constructed \AF{E} such that no computation is happening in the shape
or context positions.  As a result, dependent pattern-matching is always
applicable on \AF{E} expressions, and our optimisations can be formulated
very concisely.  We omit constant-folding like rewrites such as addition
with zero and multiplication by one and focus on less trivial cases that have
to do with selections a+nd sum.  Consider the snippet of the optimiser for
\AF{selₛ} and \AF{sum}.

\begin{code}[hide]
module Opt where
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open Lang
  open SubWk
  --open Eval using (sub; ctx-swap; ↑_; ↑↑_; eq?)
  open Array hiding (sum; slide;backslide)
  open BB
  open AD
\end{code}
\begin{code}
  opt : E Γ is → E Γ is
  opt (selₛ e e₁) with opt e | opt e₁
  ... | zero            | i = zero
  ... | one             | i = one
  ... | imapₛ e         | i = sub v₀ e i
  ... | bin op a b      | i = bin op (selₛ a i) (selₛ b i)
  ... | sum e           | i = sum (selₛ e (↑ i))
  ... | zero-but i j a  | k = zero-but i j (selₛ a k)
  ... | a               | i = selₛ a i

  opt (sum e) with opt e
  ... | zero            = zero
  ... | imap a          = imap     (sum (ctx-swap v₁ a))
  ... | imapₛ a         = imapₛ    (sum (ctx-swap v₁ a))
  ... | imapb m a       = imapb m  (sum (ctx-swap v₁ a))
  ... | zero-but (var i) (var j) a with eq? v₀ i | eq? v₀ j
  ... | eq        | eq        = sum a
  ... | neq _ i′  | eq        = sub v₀ a (var i′)
  ... | eq        | neq _ j′  = sub v₀ a (var j′)
  ... | neq _ i′  | neq _ j′  = zero-but (var i′) (var j′) (sum a)
  opt (sum e) | a = sum a
  -- ⋯
\end{code}
Selection into \AC{zero} and \AC{one} is \AF{zero} and \AC{one}, as our constants
are shape-polymorphic.  Selection into an \AF{imapₛ} is evaluation of the \AC{imapₛ}
body at the given index (this is an array version of the $\beta$-rule).  Selection
from the binary operation is a binary operation of selections.  Selection into \AC{sum}
is the \AC{sum} of selections.  Selection into conditional is the same as conditional
over selection.  Summing \AC{zero} is \AC{zero}.  Summing $s$-many $p$-shaped arrays
is the same as computing the sum of $i$-th index of every array for all $p$ indices.
If we have a sum of the conditional with the predicate is the equality of indices
$i$ and $j$ and we know that $i$ and $j$ are variables, we can compare the index
variable of the \AC{sum} with $i$ and $j$.  If they match, then conditional will
be triggered at every iteration so it can be removed.  If only one of them match,
and we are comparing variables of the same shape, there will be exactly one case
(for non-empty shapes) where this conditional will be triggered.  Therefore, all
the iterations except the one at the non-matching variable will turn to zero, and
we can simply return the expressions substituted at this variable.  If the shape
of the index variables is empty, we are in the absurd case, as we cannot possibly
create an element of an empty type.  Finally, if none of the variables match,
the iteration within the \AC{sum} do not affect the result of the predicate ---
it will be either true or false for all the iterations.  Therefore, we can lift
the conditional outside of the sum.
\begin{code}[hide]
  opt zero = zero
  opt one = one
  
  opt (var x) = var x
  
  opt (imapₛ e) = imapₛ (opt e)
  
  -- Literal copy of the above, replaing scalar versions
  -- with normal one
  opt (imap e) = imap (opt e)
  opt (sel e e₁) with opt e | opt e₁
  ... | zero | i = zero
  ... | one | i = one
  ... | imap e | i = sub v₀ e i
  --... | imapb m e | i = ?
  ... | bin op a b | i = bin op (sel a i) (sel b i)
  ... | sum e | i = sum (sel e (wk v₀ i))
  ... | zero-but i j a | k = zero-but i j (sel a k)
  ... | a | i = sel a i
  
  -- Literal copy of the above for the blocked version
  opt (imapb m e) = imapb m (opt e)
  opt (selb m e k) with opt e
  ... | zero = zero
  ... | one = one
  ... | sum e = sum (selb m e (↑ k {- var $ vₛ k-}))
  ... | zero-but i j a = zero-but i j (selb m a k)
  ... | bin op a b = bin op (selb m a k) (selb m b k)
  opt (selb m e j) | a = selb m a j
  
  
  opt (zero-but (var i) (var j) e) with opt e
  ... | a with eq? i j
  ... | eq = a
  ... | neq _ _ = zero-but (var i) (var j) a
  --opt (zero-but i j e) = zero-but i j (opt e)
  
  opt (bin plus e e₁) with opt e | opt e₁
  ... | zero | b = b
  ... | a | zero = a
  ... | (zero-but i j e) | b = zero-but i j (bin plus e b)
  ... | a | (zero-but i j e) = zero-but i j (bin plus a e)

  ... | imapₛ a | b = imapₛ (bin plus a (selₛ (↑ b) (var v₀)))
  ... | a | imapₛ b = imapₛ (bin plus (selₛ (↑ a) (var v₀)) b)
  ... | imap a | b = imap (bin plus a (sel (↑ b) (var v₀)))
  ... | a | imap b = imap (bin plus (sel (↑ a) (var v₀)) b)
  ... | imapb m a | b = imapb m (bin plus a (selb m (↑ b) (var v₀)))
  ... | a | imapb m b = imapb m (bin plus (selb m (↑ a) (var v₀)) b)

  ... | a | b = bin plus a b
  opt (bin mul e e₁) with opt e | opt e₁
  ... | zero | b = zero
  ... | a | zero = zero
  ... | one | b = b
  ... | a | one = a
  ... | (zero-but i j e) | b = zero-but i j (bin mul e b)
  ... | a | (zero-but i j e) = zero-but i j (bin mul a e)
  
  ... | imapₛ a | b = imapₛ (bin mul a (selₛ (↑ b) (var v₀)))
  ... | a | imapₛ b = imapₛ (bin mul (selₛ (↑ a) (var v₀)) b)
  ... | imap a | b = imap (bin mul a (sel (↑ b) (var v₀)))
  ... | a | imap b = imap (bin mul (sel (↑ a) (var v₀)) b)
  ... | imapb m a | b = imapb m (bin mul a (selb m (↑ b) (var v₀)))
  ... | a | imapb m b = imapb m (bin mul (selb m (↑ a) (var v₀)) b)
  
  ... | a | b = bin mul a b
  
  -- XXX: not calling opt on e, as this is index
  opt (slide i pl e su) with opt e
  ... | zero = zero
  ... | a = slide i pl a su
  opt (backslide i e su pl) with opt e
  ... | zero = zero
  ... | a = backslide i a su pl
  opt (scaledown x e) with opt e
  ... | scaledown y a = scaledown (x ℕ.* y) a
  ... | a = scaledown x a
  -- TODO: propogate minues inside of +, *, imap, etc.
  opt (minus e) with opt e
  ... | minus a = a
  ... | imapₛ a = imapₛ (minus a)
  ... | imap a = imap (minus a)
  ... | imapb m a = imapb m (minus a)
  ... | sum e = sum (minus e)
  ... | bin plus a b = bin plus (minus a) (minus b)
  ... | bin mul a b = bin plus (minus a) b
  ... | a = minus a
  opt (logistic e) with opt e
  ... | imapₛ a = imapₛ (logistic a)
  ... | imap a = imap (logistic a)
  ... | a = logistic a


  multiopt : ℕ → E Γ is → E Γ is
  multiopt zero e = e
  multiopt (suc n) e = opt (multiopt n e)

  module TryOpt where
\end{code}

Let us observe optimisation effects when computing derivatives of
the scalar dot-product defined as follows.
\begin{code}
    dotp : E Γ (ar s) → E Γ (ar s) → E Γ (ar unit)
    dotp a b = Sum λ i → selₛ (↑ a) i ⊠ selₛ (↑ b) i
\end{code}
\begin{code}[hide]
    C : Ctx 
    a : E C _ 
    b : E C _
    seed : E C _
\end{code}
We define the context \AF{C} where two top variables are of 5-element vector shape
and the last variable (\AC{v₂}) is of scalar shape.  We bind these variables to Agda
variables for convenience.
\begin{code}
    C = ε ▹  ar (ι 1)       ▹  ar (ι 5)    ▹  ar (ι 5);
             seed = var v₂  ;  a = var v₁  ;  b  = var v₀
\end{code}
\begin{code}[hide]
    ∂a     = env-ix {C} (∇ {C} (dotp a b) seed (env-zero {C})) v₁
    ∂a′    = multiopt 3 ∂a
\end{code}
We compute the derivatives of \AF{dotp a b} with seed \AF{seed} and we inspect
the $a$-th position in the returned environment that we call \AF{∂a}.  Then we repeatedly
apply \AF{opt} (three times) to \AF{∂a} and save it in \AF{∂a′}.  We force Agda to
verify that the content of the variables is as follows:
\begin{code}
    non-opt   : ∂a   ≡ (Sum λ i → zero ⊞ Imapₛ λ j → zero-but j (↑ i) (↑↑ seed ⊠ selₛ (↑↑ b) (↑ i))) ⊞ zero
    with-opt  : ∂a′  ≡ Imapₛ λ i → (↑ seed ⊠ selₛ (↑ b) i)
\end{code}
\begin{code}[hide]
    non-opt = refl
    with-opt = refl
-- open Lang
-- open SubWk
\end{code}
As it can be seen, \AF{∂a} sums-up the arrays, where only one element is non-zero at
every iteration.  Such a computation is highly inefficient when executed directly,
as it needs to compute all the inner arrays before summing them up.  However, the
optimised version correctly rewrites \AF{∂a} into \AC{imap} that multiplies
the \AB{seed} by $b$, which is the expected answer.  This reduces complexity
of the expression form squared to linear.

\subsection{Extraction}

Extraction from \AF{E} into SaC translates constructors of \AF{E} into
corresponding SaC expressions or function calls.  The translation starts with
a definition of an environment (\AF{SEnv} \AB{Γ}) that assigns SaC variable names
to all positions in \AB{Γ}.  The assumption here is that when we compile
expressions in context \AF{Γ}, variable names of the corresponding shapes are
available in SaC.

Next, we have to take care of shapes.  Array shapes in \AF{E} are binary trees,
but array shapes in SaC are 1-dimensional arrays (flattened binary trees).
When some expression in \AF{E} is of product shape, we usually have to
supply left or right subshapes of the product to SaC. These are always available
through implicit arguments of \AF{E} constructors. Assuming that by the
time we come to extraction, all the \AF{E} shapes are constants, we can
always generate shape expressions in SaC.  This is implemented in \AF{show-shape}.
Relaxing the assumption about constant shapes is possible but requires
extension of \AF{E} so that we can always bind the shapes used in \AF{E}
to some expressions in SaC.

We also need a source of fresh variables so that we can generate indices
for \AC{imap} expressions.  We define a stateful function \AF{iv} that
generates a fresh index variable.  

Extraction is given by \AF{to-sac} that translates the expression $e$ in
the environment $\rho$.  The function is stateful so that we can generate
fresh variables when needed.

The definitions of \AF{SEnv}, \AF{iv}, {\AF{show-shape}, and \AF{to-sac} follow.
\begin{code}[hide]
module Sac where
  open import Data.Unit
  open import Data.Product
  open import Data.List as L using (List; []; _∷_; _++_)
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open import Data.Nat.Show using () renaming (show to show-nat)
  open import Data.String hiding (_++_)
  open import Text.Printf
  open import Category.Monad.State --using (State; StateMonad; RawMonadState)
  open import Category.Monad using (RawMonad)
  --open RawMonad {{...}} public
  open RawMonadState {{...}} public
  open Lang
  open Array hiding (sum; slide; backslide)
  open SubWk

  instance
    -- stateMon : ∀ {S : Set} → RawMonad (State S)
    -- stateMon {S} = StateMonad S

    stateMonState : ∀ {S : Set} → RawMonadState S (State S)
    stateMonState {S} = StateMonadState S
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  SEnv : Ctx → Set
  SEnv ε         = ⊤
  SEnv (Γ ▹ is)  = SEnv Γ × String
\end{code}}
\and
\codeblock{\begin{code}
  iv : S → State ℕ String
  iv s = do  v ← get
             modify suc
             return $ printf "x%u" v
\end{code}
\begin{code}[hide]

  lookup : is ∈ Γ → SEnv Γ → String
  lookup v₀      (ρ , e) = e
  lookup (vₛ x)  (ρ , e) = lookup x ρ


  -- show-shape : S → String
  -- show-shape (ι x) = show-nat x
  -- show-shape (s S.⊗ p) = printf "⟨%s, %s⟩" (show-shape s) (show-shape p)

  fresh-var : ℕ → String
  fresh-var n = printf "x%u" n

  bop : Bop -> String
  bop plus = "+"
  bop mul = "*"

  dim : S → ℕ
  dim (ι _) = 1
  dim (s Array.⊗ p) = dim s ℕ.+ dim p

  ivl : S → State ℕ (List String)
  ivl (ι _) = do
    v ← get
    modify suc
    return $ (fresh-var v ∷ [])
  ivl (s S.⊗ p) = do
    l ← ivl s
    r ← ivl p
    return $ l L.++ r
  
  --iv s = printf "[%s]" ∘ intersperse ", " <$> ivl s
\end{code}}
\and
\codeblock{\begin{code}
  show-shape : S → String
  show-shape s = printf "[%s]" 
               $ intersperse ", " 
               $ go s
    where
      go : S → List String
      go (ι x)    = show-nat x ∷ []
      go (s ⊗ p)  = go s ++ go p
\end{code}}
\and
\codeblock{\begin{code}
  to-sac : (e : E Γ is) → (ρ : SEnv Γ) → State ℕ String
  to-sac (imap {s = s} e) ρ = do
     i ← iv s
     b ← to-sac e (ρ , i)
     return $ printf "{ %s -> %s | %s < %s }"
                     i b i (show-shape s)
  to-sac (sel e e₁) ρ = 
     printf "(%s)[%s]" <$> to-sac e ρ ⊛ to-sac e₁ ρ
  -- ⋯
\end{code}}
\end{mathpar}
\begin{code}[hide]
  to-sac zero ρ = return "zero"
  to-sac one ρ = return "one"
  to-sac (var x) ρ = return $ lookup x ρ
  to-sac (imapₛ {s = s} e) ρ = do
     i ← iv s
     b ← to-sac e (ρ , i)
     let sh = show-shape s
     --return $ printf "{ %s -> %s | %s < %s }" i b i sh
     return $ printf "IMAPS(%s, (%s), (%s))" i b sh
  to-sac (selₛ e e₁) ρ = do
     a ← to-sac e ρ
     i ← to-sac e₁ ρ
     --return $ printf "(%s)[%s]" a i
     return $ printf "sels(%s, %s)" a i

  -- Copy-paste from scalar versions

  -- Copy-paste from scalar versions
  to-sac (imapb {s = s}{p} m e) ρ = do
     i ← iv s
     b ← to-sac e (ρ , i)
     let sh-s = show-shape s
     let sh-p = show-shape p
     return $ printf "unblock({ %s -> %s | %s < %s }, %s)" i b i sh-s sh-p
  to-sac (selb {p = p} m e e₁) ρ = do
     a ← to-sac e ρ
     i ← to-sac e₁ ρ
     let sh-p = show-shape p
     return $ printf "selb(%s, %s, %s)" a i sh-p

  to-sac (zero-but i j e) ρ 
     = printf "%s == %s ? %s : zero" <$> (to-sac i ρ) ⊛ (to-sac j ρ) ⊛ (to-sac e ρ)
  to-sac (sum {s = s} {p = p} e) ρ = do
     -- outer index 
     i ← iv s
     -- inner index which is juts a fresh name
     j ← iv p
     b ← to-sac e (ρ , i)
     -- `s` is outer shape, and `p` is the inner one
     let sh-s = show-shape s
     let sh-p = show-shape p
     --return $ printf "sumOuter(%u, { %s -> %s | %s < %s})" (dim s) i b i sh-s
     -- sumOuter(ivOuter, ivInner, e, shOuter, shInner)
     return $ printf "sumOuter(%s, %s, %s, (%s), (%s))" i j b sh-s sh-p
  to-sac (bin x e e₁) ρ = do
     a ← to-sac e ρ
     b ← to-sac e₁ ρ
     return $ printf "(%s) %s (%s)" a (bop x) b
  to-sac (slide {p = p} e pl e₁ su) ρ = do
     i ← to-sac e ρ
     a ← to-sac e₁ ρ
     let sh-p = show-shape p
     return $ printf "slide(%s, %s, %s)" i a sh-p
  to-sac (backslide {r = r} e e₁ su pl) ρ = do
     i ← to-sac e ρ
     a ← to-sac e₁ ρ
     let sh-sp = show-shape r
     return $ printf "backlide(%s, %s, %s)" i a sh-sp

  to-sac (scaledown x e) ρ = do
     a ← to-sac e ρ
     return $ printf "(%s) / %s" a (show-nat x)

  to-sac (minus e) ρ = printf "-(%s)" <$> to-sac e ρ 
  to-sac (logistic e) ρ = printf "logistics(%s)" <$> to-sac e ρ


  -- This can be made stateful, but we are assuming that
  -- vₛ is no need to make imap/sum index variables unique.
  env-sac : AD.Env Γ Δ → (vars : SEnv Δ) → SEnv Γ
  env-sac {ε} ρ σ = _
  env-sac {Γ ▹ ix s} ρ σ = env-sac ρ σ , "--"
  env-sac {Γ ▹ ar s} (ρ , e) σ = env-sac ρ σ , proj₁ (to-sac e σ 1)

  -- Reversed environment to list
  env-rev-list : SEnv Γ → List String
  env-rev-list {ε}     ρ = []
  env-rev-list {Γ ▹ _} (ρ , x) = x ∷ env-rev-list ρ
 
  -- zipWith for Environments
  zip-env : (String → String → String) → SEnv Γ → SEnv Γ → SEnv Γ
  zip-env {ε}     f tt      tt      = tt
  zip-env {Γ ▹ x} f (ν , n) (ρ , e) = zip-env f ν ρ , f n e
\end{code}

\subsubsection{SaC Primitives\label{sec:sac-primitives}}
As can be seen from the two cases of \AF{to-sac}, the extraction process is
not complicated. In essence, we define a small snippet of SaC code for 
each \AF{E} constructor.  Consider the \AC{imap}/\AC{sel}
family from the code snippet.  The \AC{imap} constructor maps directly to SaC's
tensor comprehensions~\cite{tensor-comp} expressed as: \texttt{\{ iv -> e | iv < s \}}.
This expression constructs arrays by evaluating \texttt{e} for every array non-negative index
vector
\texttt{iv} whose components are element-wise smaller than the shape \texttt{s}.  The shape of the resulting
array is concatenation of \texttt{s} and whatever the shape of \texttt{e} is.
Selections \AC{sel} correspond to the built-in array selection using
C-like syntax \texttt{e[iv]} where \texttt{e} is the array we are selecting
from and \texttt{iv} is the index vector.   Shape constraints are exactly as in
\AF{E}: if \texttt{e} is of shape \texttt{s ++ p}, and \texttt{iv} is bounded
by \texttt{s} then \texttt{e[iv]} is of shape \texttt{p}.

Scalar versions of imap/sel require a little wrapping.  For \AC{imapₛ} we
generate a tensor comprehension that selects inner expressions (they are
1-element vectors) at zero-th position.  For \AC{selₛ} we make selection into
an array and we wrap the result in a 1-d vector:
\begin{mathpar}
{\begin{varwidth}{0.9\textwidth}
\begin{lstlisting}[linewidth=.4\textwidth]
#define IMAPS(iv, e, shp) \
  {iv -> (e)[[0]] | iv < shp}
\end{lstlisting}
\end{varwidth}}
\and
{\begin{varwidth}{0.9\textwidth}
\begin{lstlisting}[linewidth=.55\textwidth]
inline float[1]
sels(float[d:shp] x, int[d] iv)
{
  return [x[iv]];
}
\end{lstlisting}
\end{varwidth}}
\end{mathpar}
When translating (\AC{imapₛ} \{ \AB{s} \} \AB{e}) we pick a fresh index variable
\texttt{iv}, then we translate \AB{e} (in the environment extended with \texttt{iv})
into \texttt{e'} and we generate \texttt{IMAPS(iv, e', shp)}, where \texttt{shp} is
a translation of \texttt{s}.  On the side of SaC we expand this macro as shown
above.  We could have expanded this macro on the Agda side, but this abstraction
makes it possible to make adjustments in the generated code without running Agda.
We map \AC{selₛ} into the \texttt{sels} function.  Consider the type of \texttt{sels}
which uses the recently added feature of SaC that makes it possible to encode
shape constraints in types~\cite{type-pattern}.  While these constraints are potentially checked at runtime,
they are very useful for readability and they provide some confidence about the
generated code.  The meaning of the type \texttt{float[d:shp]} is that it is
an array of base type \texttt{float} of rank \texttt{d} and shape \texttt{shp}.
When a variable of the same name is used within different arguments, it automatically
triggers the equality constraint between the corresponding ranks/shapes.

\paragraph{Blocking} Implementation of \AC{selb}/\AC{imapb} pair relies on
the notion of blocking, so we introduce the analogue to \AF{block}/\AF{unblock}
functionality in SaC as follows:
\begin{mathpar}
{\begin{varwidth}{0.9\textwidth}
\begin{lstlisting}[linewidth=.44\textwidth]
inline float[n:s,n:p]
block(float[n:sp] x, int[n] p)
     | all(s*p == sp)
     , all(p   >= 0)
{
  return { iv -> tile(p, iv * p, x) 
         | iv < sp / p};
}
\end{lstlisting}
\end{varwidth}}
\and
{\begin{varwidth}{0.9\textwidth}
\begin{lstlisting}[linewidth=.55\textwidth]
inline float[n:sp] 
unblock(float[n:s,n:p] a, int[n] p)
       | all(s*p == sp)
       , all(p   >= 0)
{
  return { iv -> a[(iv / p) ++ mod (iv, p)]
         | iv < s*p};
}
\end{lstlisting}
\end{varwidth}}
\end{mathpar}
The type \texttt{float[n:s,n:p]} denotes an array of the shape \texttt{s ++ p}
where \texttt{s} and \texttt{p} are of length \texttt{n}.  This is a product
shape in terms of our array theory.  As \texttt{sp} is just a variable that
is not related to \texttt{s} or \texttt{p}, we add two constraints (expressions
behind the bar after the function definition) saying that: (i) \texttt{sp} is
a point-wise product of \texttt{s} and \texttt{p}; (ii) all the elements of
the \texttt{p}-shape are greater than zero.  Keep in mind that these are potential
runtime constraints, they may be proved or flagged as disproved during compilation
but they do not provide a static guarantee. The implementation of block uses the \texttt{tile}
operation from the standard library of SaC. It selects a sub-array of the given shape at the given position.
In \texttt{unblock} we use a division and a modulo operation to remap the indices.
When translating \AC{selb}, we simply select into \texttt{block}-ed array.
When translating \AC{imapb}, we use the tensor comprehension as in case of
\AC{imap} to compute blocked array and then we call \texttt{unblock} on it.

\paragraph{Sliding} Slides and backslides are translated into calls to
the following SaC functions:
\begin{mathpar}
{\begin{varwidth}{0.9\textwidth}
\begin{lstlisting}
inline float[d:n1] 
slide(int[d] i, float[d:mn] x, int[d] n)       | all(n1        == n + 1)
                                               , all(n + 1 + i <= mn)
{
  return { iv -> x[iv + i] | iv < n + 1 };
}

inline float[d:mn]
backslide(int[d] i, float[d:n1] y, int[d] mn)  | all(i < 1 + mn - n1)
{
  return { iv -> y[iv - i] | i <= iv < n1 + i;
           iv -> 0f        |      iv < mn };
}
\end{lstlisting}
\end{varwidth}}
\end{mathpar}
Shape constraints become a little bit involved here because we implicitly
reconstruct the proof objects such as \AB{m} \AF{+} \AB{n} \AF{≈} \AB{mn}
and \AF{suc} \AB{n} \AF{≈} \AB{n1}.  Otherwise, \texttt{slide} selects a
sub-array of the shape (\texttt{n+1}) starting at the index \texttt{i}.
The \texttt{backslide} populates the sub-array with the elements of
\texttt{y} and the second partition of the tensor comprehension specifies
that all the other indices evaluate to zero.  Translation of \AC{slide}
and \AC{backslide} maps the arguments one-to-one, additionally providing
the $n$-shape in case of slide and the $(m+n)$ shape in case of backslide.

\paragraph{Summation} When translating (\AC{sum} \{\AB{s}\} \AB{e}), where
\AB{e} is of shape \AB{p} (and the index variable within the \AC{sum} is
bounded by \AB{s}), we map these arguments into the following SaC function:
\begin{lstlisting}
inline float[n:p] sumOuter(float[m:s,n:p] a, int[m] s, int[n] p) {
  return { jv -> sum({iv -> a[iv++jv] | iv < s}) | jv < p };
}
\end{lstlisting}
We use SaC's builtin \texttt{sum} function that sums-up all the elements
of the given array.

The rest of the constructions are mapped into regular arithmetic operations
that are provided by SaC.


\subsection{Local Variables}

The framework that we built so far computes derivatives of the variables in
the context.  This means that for complex expressions in \AF{E} (such as \AF{forward}),
all the let bindings will be inlined.  This is often not desirable both for performance
and readability.  Here we present a mechanism that introduce local variables
and preserves them during AD.
\begin{code}[hide]
module DoubleChain where
  -- In this module I want to preserve derivatives
  -- of the local variables in the chain (instead of inlining them)
  open import Data.String
  open import Text.Printf
  open import Data.Product --using (Σ; _×_; _,_)
  open import Data.Unit
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open import Data.List as L using (List; []; _∷_)
  open Array hiding (sum; slide; backslide)
  open Lang
  open SubWk
  open AD
  open Opt
  open BB

  Env′ : Ctx → Set
  Env′ Γ = Env Γ Γ
\end{code}

The key data structure that makes it possible to introduce local variables
is called \AF{Chain} which has two constructors.  The empty chain consists
of the names for all the variables in the context \AB{Γ}.  This represents the
case where no local variables have been introduced.  The \AC{\_▹\_} constructor
takes a chain in context \AB{Δ} and the array expression of shape \AB{p} in
the same context together with the variable name.  This produces the chain
in the context extended by two variables.  One variable is a place-holder
for the expression and the other variable is a placeholder for the derivative
of that expression.
\begin{code}
  data Chain : Ctx → Set where
    ε    : Sac.SEnv Γ → Chain Γ
    _▹_  : Chain Δ → (String × E Δ (ar p)) → Chain (Δ ▹ ar p ▹ ar p)
\end{code}

The computation of the derivative in \AF{Chain}s follows the following
simple idea.  Consider the chain with two variables $a$ and
$b$ in the initial context \AB{Γ}, and two local variables $x$ and $y$.
Here is what happens when we compute the derivative of some expression
$e$ (that may depend on $a$, $b$, $x$, $y$) with some seed $s$ in the
empty $\delta_0$ environment. 

%\begin{table}
\begin{center}
\begin{tabular}{cc|cccc|l}
   $a$         &$b$         &$\partial{x}$& $x$         &$\partial{y}$&$y$       & \text{compute $\nabla\ e\ s\ \delta_0$}\\
   \hline
   $\delta_a$  &$\delta_b$  &-            & $\delta_x$  &-            &$\delta_y$& \text{assign $\delta_y$ to $\partial{y}$}\\
   $\delta_a$  &$\delta_b$  &-            & $\delta_x$  &$\delta_y$   &$\delta_y$& \text{compute $\nabla\ y_e\ \partial{y}$}\\
   $\delta'_a$ &$\delta'_b$ &-            & $\delta'_x$ &$\delta_y$   &$\delta_y$& \text{assign $\delta'_x$ to $\partial{x}$}\\
   $\delta'_a$ &$\delta'_b$ &-            & $\delta'_x$ &$\delta_y$   &$\delta_y$& \text{compute $\nabla\ x_e\ \partial{x}$}\\
   $\delta''_a$ &$\delta''_b$ &$\delta'_x$  & $\delta'_x$ &$\delta_y$   &$\delta_y$& \text{done}
\end{tabular}
\end{center}
%\end{table}

First of all, the computation of $e$ returns the environment $\delta$ that can
be found in the first line of the table.  Then we repeat the following steps while
traversing the chain backwards: we copy the $y$-th position of the $\delta$-environment
to the $\partial{y}$-th position, and we compute the expression $y_e$ that is assigned to $y$
($xx$ in this case) with the seed $\partial{y}$-th variable.  Just to clarify, the seed
is the variable $\partial{y}$ and not its value.  Then we repeat the same process
for $x$ and potentially all the other remaining local variables (not in this case) until
we hit the beginning of the chain.

At the end of the process we obtain an environment where derivatives for $a$ and
$b$ are expressed in terms of $\partial{x}$ and $\partial{y}$.  The remaining step
is to collect the values of $\partial{x}$ and $\partial{y}$ which can be found
at the corresponding positions in the $\delta$-environment.
\begin{code}[hide]
  data LCtx : Set where
    []  : LCtx
    _◃_ : IS → LCtx → LCtx

  _<><_ : Ctx → LCtx → Ctx
  Γ <>< [] = Γ
  Γ <>< (x ◃ Δ) = (Γ ▹ x) <>< Δ

  data LEnv : LCtx → Ctx → Set where
    []  : LEnv [] Γ
    _◃_ : ∀ {Δ′} → E Γ (ar s) → LEnv Δ′ Γ → LEnv (ar s ◃ Δ′) Γ

  data Postfix : Ctx → Ctx → Set where
    done : Postfix ε Γ
    next : Postfix Γ Δ → Postfix (Γ ▹ ar s) (Δ ▹ ar s)

  double-ctx : Ctx → Ctx
  double-ctx ε = ε
  double-ctx (Γ ▹ x) = double-ctx Γ ▹ x ▹ x

  chain-to-env : Chain Γ → Σ Ctx λ Δ → Env (double-ctx Δ) Γ × Postfix (double-ctx Δ) Γ
  chain-to-env (ε x)   = ε , tt , done
  chain-to-env (_▹_ {p = p} c (_ , x)) = let
    Δ , ρ , po = chain-to-env c
    in (Δ ▹ ar p) , ((env-map {Γ = double-ctx Δ} (↑↑_) ρ , zero) , (↑ ↑ x)) , (next (next po))

  pstep : ∀ {Δ′} → Postfix ((Δ ▹ ar s) <>< Δ′) Γ → Postfix (Δ <>< (ar s ◃ Δ′)) Γ
  pstep {Δ′ = []} (next p) = next p
  pstep {Δ′ = x ◃ Δ′} p = p

  post-var : ∀ {Δ′} → Postfix (Δ <>< Δ′) Γ → is ∈ Δ → is ∈ Γ
  post-var {Δ′ = []} (next p) v₀ = v₀
  post-var {Δ′ = []} (next p) (vₛ x) = vₛ (post-var {Δ′ = []} p x)
  post-var {Δ′ = is ◃ Δ′} p x = post-var {Δ′ = Δ′} p (vₛ x)

  no-ix : ix s ∈ Δ → ¬ Postfix Δ Γ
  no-ix v₀ = λ ()
  no-ix (vₛ v) (next p) = no-ix v p

  post-fish : ∀ Δ′ → is ∈ Δ → is ∈ (Δ <>< Δ′)
  post-fish [] v = v
  post-fish (x ◃ Δ′) v = post-fish Δ′ (vₛ v)

  gradc : ∀ {Δ′} → Env (double-ctx Δ) Γ → LEnv Δ′ Γ 
            → Postfix ((double-ctx Δ) <>< Δ′) Γ →  Env′ Γ → Env′ Γ
  gradc {ε}        {Γ} {Δ′} ρ ρ′ p δ = δ
  gradc {Δ ▹ ix x} {Γ} {Δ′} ρ ρ′ p δ = ⊥-elim (no-ix (post-fish Δ′ v₀) p)
  gradc {Δ ▹ ar x} {Γ} {Δ′} ((ρ , z) , e) ρ′ p δ =
    let
    ve = post-var {Δ′ = Δ′} p v₀  -- variable for e in Γ
    vz = post-var {Δ′ = Δ′} p v₁  -- variable for z in Γ
    s  = env-ix δ ve
    δ₁ = update δ vz (const s)    -- save s in the z's position
    δ₂ = ∇ e (var vz) δ₁          -- use vz position as seed
    in gradc {Δ} ρ (z ◃ (e ◃ ρ′)) (pstep {Δ′ = ar x ◃ Δ′} (pstep {Δ′ = Δ′} p)) δ₂

  chain-grad : Chain (Γ ▹ ar s) → E (Γ ▹ ar s) (ar s) → Env′ (Γ ▹ ar s)
  chain-grad {Γ} {s} c seed = let
    -- Well, this is a choice I suppose
    --δ = ∇ seed one (env-imap {Γ = Γ ▹ ar s} (const zero))
    δ = env-imap {Γ = Γ} (const zero) , seed
    Δ , ρ , po = chain-to-env c
    in env-map {Γ = Γ ▹ ar s} (multiopt 10) $ gradc ρ [] po δ

  chain-sac-ctx : Chain Γ → Sac.SEnv Γ
  chain-sac-ctx (ε x) = x
  chain-sac-ctx (c ▹ (v , _)) = chain-sac-ctx c ,, ("∂/∂" ++ v) ,, v
  
  filter-grad : Chain Γ → Sac.SEnv Γ → List String 
  filter-grad (ε x)   δ = Sac.env-rev-list δ
  filter-grad (c ▹ _) ((δ , _), x) = x ∷ filter-grad c δ

  chain-grad-sac : Chain Γ → Env′ Γ → String
  chain-grad-sac {Γ} c δ = let
    vars = chain-sac-ctx c
    vals = Sac.env-sac {Γ} δ vars
    assignments = filter-grad c $ Sac.zip-env (printf "∂/∂%s = %s;") vars vals
    in intersperse "\n" assignments

  chain-sac-l : Chain Γ → ℕ → List String 
  chain-sac-l (ε x) _ = []
  chain-sac-l (c ▹ (v , e)) n = let r , n′ = Sac.to-sac (multiopt 10 e) (chain-sac-ctx c) n 
                                in printf "%s = %s;" v r ∷ chain-sac-l c n′

  chain-sac : Chain Γ → String
  chain-sac c = intersperse "\n" $ L.reverse $ chain-sac-l c 1


  -- test-chain : Chain _ --(ε ▹ ar (ι 3))
  -- test-chain = ε {Γ = ε ▹ ar (ι 3)} (_ ,, "a") 
  --            ▹ ("r" , mul-test)
  --            ▹ ("r₁" , (var v₀) ⊠ (var v₂))

  -- test-grad : String
  -- test-grad = chain-sac test-chain 
  --             ++ "\n" ++ chain-grad-sac test-chain (chain-grad test-chain one)
\end{code}

Let us consider a small example to see this in action.  We start with a little
convenience data structure \AF{ChainCtx} that keeps the shapes and the variable names
together.  We also define the function \AF{ce-split} that splits 
\AF{ChainCtx} into the context and the environment with variable names in that context:
\begin{code}
  data ChainCtx : Set where
    ε : ChainCtx
    _▹_ : ChainCtx → String × S → ChainCtx

  ce-split : ChainCtx → Σ Ctx Sac.SEnv
\end{code}
\begin{code}[hide]
  ce-split ε = ε , tt
  ce-split (cx ▹ (v , s)) = let Δ , ρ = ce-split cx in (Δ ▹ ar s) , (ρ , v)

  Product : ℕ → Set → Set
  Product 0       A = ⊤
  Product 1       A = A
  Product (suc n) A = A × Product n A

  Es : ∀ {Γ : Ctx} → (n : ℕ) → {Product n IS} → Set
  Es {Γ} 0             {is} = ⊤
  Es {Γ} 1             {is} = E Γ is
  Es {Γ} (suc (suc n)) {is , p}  = E Γ is × Es {Γ} (suc n) {p}

  ↑↑ₙ : ∀ {Γ : Ctx} {is} n {p : Product n IS} → Es {Γ} n {p} → Es {Γ ▹ is ▹ is} n {p}
  ↑↑ₙ 0 es = _
  ↑↑ₙ 1 e  = ↑↑ e
  ↑↑ₙ (suc (suc n)) (e , es) = ↑↑ e , ↑↑ₙ (suc n) es
\end{code}
Consider an initial environment of two 5-element vectors $a$ and $b$; local
computations $x = ab$ and $y = xx$; and the generated code when computing derivative
of $y$ (\AC{var v₀}) on the right.
\begin{mathpar}
\codeblock{\begin{code}
  test-chain : Chain _
  test-chain = let
    Γ , ρ = ce-split (ε ▹ ("a" , ι 5) ▹ ("b" , ι 5))
    a = var v₁; b = var v₀
    C₁ = ε {Γ} ρ  ▹ ("x" , a ⊠ b)
    x = var v₀
    C₂ = C₁       ▹ ("y" , x ⊠ x)
    in C₂
\end{code}}
\and
{\begin{varwidth}{0.9\textwidth}
\begin{lstlisting}[linewidth=.44\textwidth]
x = (a) * (b);
y = (x) * (x);
ddy = one;
ddx = ((ddy) * (x)) + ((ddy) * (x));
ddb = (ddx) * (a);
dda = (ddx) * (b);
\end{lstlisting}
\end{varwidth}}
\end{mathpar}
Let us convince ourselves that the result is correct.  Our expression is $abab = a^2b^2$,
and its partial derivatives $\frac{\partial}{\partial a} = 2ab^2$,
$\frac{\partial}{\partial b} = 2ba^2$.  If we fold the assignments, we get:
\begin{eqnarray*}
   \text{dda} &= (x + x)b = (ab + ab)b = 2ab^2\\
   \text{ddb} &= (x + x)a = (ab + ab)a = 2ba^2
\end{eqnarray*}
Note that computations in $x$ and \texttt{ddx} are shared in further computations
which was the main goal of introducing this mechanism.

There are two inconveniences in the above implementation that we would like to
mention:
\begin{enumerate}
\item There is no restriction on using the placeholders for derivatives in the 
chain expressions, so in principle, one could write expression in terms of
variables and their derivatives.  However, this is not being handled and likely
to generate bogus terms.  If this is a useful feature, it requires more thinking
on how exactly it should work.  Otherwise it is easy to introduce restrictions
that rule out such cases.
\item If we define variables in the chain that do not contribute to the final
expression, we may introduce extra computations.  We do not compromise correctness,
as all inaccessible terms will get zero value.  However, direct execution of the
resulting expressions may introduce redundant computations.
\end{enumerate}
Both of these are future work.  For now, we make an assumption that placeholders
are not used in the expressions and that we do not insert bindings that do not
contribute to the final result.

\begin{code}[hide]
  test-chain-sac : String
  test-chain-sac
    = chain-sac test-chain 
             ++ "\n" ++ chain-grad-sac test-chain (chain-grad test-chain (one))

\end{code}

We present the specification of our case study in \AF{E} using \AF{Chain}.  We start
with the context \AF{cnn-ctx} that contains the \texttt{target} digit that
is depicted on the image, the input image \texttt{inp} and the weights of the network.
The definition of the chain is a one-to-one copy of the definition found in
Section~\ref{sec:cnn}.  The only real difference is that we have to take care of
maintaining bindings between Agda variables and the variables in \AF{E}.  Fortunately,
let expressions in Agda make it possible to shadow the binding, which comes very
useful in this case.

{\small
\begin{code}
  cnn-ctx : ChainCtx
  cnn-ctx  = ε
           ▹ ("target"  , ι 10 ⊗ (ι 1 ⊗ (ι 1 ⊗ (ι 1 ⊗ ι 1))))     -- 7
           ▹ ("inp"     , ι 28 ⊗ ι 28)                            -- 6
           ▹ ("k₁"      , ι 6 ⊗ (ι 5 ⊗ ι 5))                      -- 5
           ▹ ("b₁"      , ι 6)                                    -- 4
           ▹ ("k₂"      , ι 12 ⊗ (ι 6 ⊗ (ι 5 ⊗ ι 5)))             -- 3
           ▹ ("b₂"      , ι 12)                                   -- 2
           ▹ ("fc"      , ι 10 ⊗ (ι 12 ⊗ (ι 1 ⊗ (ι 4 ⊗ ι 4))))    -- 1
           ▹ ("b"       , ι 10)                                   -- 0

  cnn-chain : Chain _
  cnn-chain = let 
      Γ , ρ = ce-split cnn-ctx 
      inp = var v₆; k₁ = var v₅; b₁ = var v₄; k₂ = var v₃; b₂ = var v₂; fc = var v₁; b = var v₀
      C₁ = ε {Γ} ρ ▹ ("c₁₁" , mconv (ι ⊗ ι) inp k₁ b₁ (ι ⊗ ι));        k₂ = ↑↑ k₂; b₂ = ↑↑ b₂;  fc = ↑↑ fc; b = ↑↑ b; c₁₁ = var v₀
      C₂ = C₁ ▹ ("c₁"  , logistic c₁₁);                                k₂ = ↑↑ k₂; b₂ = ↑↑ b₂;  fc = ↑↑ fc; b = ↑↑ b; c₁ = var v₀
      C₃ = C₂ ▹ ("s₁"  , Imap λ i → avgp₂ 12 12 (sel (↑ c₁) i));       k₂ = ↑↑ k₂; b₂ = ↑↑ b₂;  fc = ↑↑ fc; b = ↑↑ b; s₁ = var v₀
      C₄ = C₃ ▹ ("c₂₁" , mconv (ι ⊗ (ι ⊗ ι)) s₁ k₂ b₂ (ι ⊗ (ι ⊗ ι)));                           fc = ↑↑ fc; b = ↑↑ b; c₂₁ = var v₀
      C₅ = C₄ ▹ ("c₂"  , logistic c₂₁);                                                         fc = ↑↑ fc; b = ↑↑ b; c₂ = var v₀
      C₆ = C₅ ▹ ("s₂"  , Imap λ i → Imap λ j → avgp₂ 4 4 (sel (sel (↑↑ c₂) (↑ i)) j));          fc = ↑↑ fc; b = ↑↑ b; s₂ = var v₀
      C₇ = C₆ ▹ ("r₁"  , mconv (ι ⊗ (ι ⊗ (ι ⊗ ι))) s₂ fc b (ι ⊗ (ι ⊗ (ι ⊗ ι))));                r₁ = var v₀
      C₈ = C₇ ▹ ("r"   , logistic r₁)
      in C₈
\end{code}

\begin{code}[hide]
  test-cnn : String
  test-cnn 
    = let
        -- 2*8 + 7 = 23
        target = ↑↑ ↑↑ ↑↑ ↑↑ ↑↑  ↑↑ ↑↑ ↑↑ ↑↑ ↑↑  ↑↑ ↑ (var v₀)
      in chain-sac cnn-chain 
             ++ "\n" ++ chain-grad-sac cnn-chain (chain-grad cnn-chain (var v₀ ⊞ minus target))
\end{code}
}

