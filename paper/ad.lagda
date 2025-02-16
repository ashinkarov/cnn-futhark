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


\todo[inline]{Old text}
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
  open WkSub
  open Lang
\end{code}
\begin{code}
  data Env : Ctx → Ctx → Set where
    ε    : Env ε Γ
    skip : Env Γ Δ → Env (Γ ▹ ix s) Δ
    _▹_  : Env Γ Δ → E Δ (ar s) → Env (Γ ▹ ar s) Δ

  data EE : Ctx → Ctx → Set where
    env : Env Γ Δ → EE Γ Δ
    let′ : E Δ (ar s) → EE Γ (Δ ▹ ar s) → EE Γ Δ 
\end{code}
Note that \AF{Env} only keeps array expressions, as (i) derivatives for indices do
not exist; and (ii) we can always make an initial environment by populating all the
elements with \AC{zero}s.  

\todo[inline]{Old text}
We define several helper operations to manipulate environments: \AF{env-zero} is 
an environment where all the values are \AC{zero}s; \AF{update} modifies the 
expression at the $v$-th position by applying $f$ to it; \AF{env-map} applies the function
$f$ from \AF{E} to \AF{E} to all the elements of the environment; and \AF{env-zipWith}
applies the binary function $f$ on two environments point-wise.  The types of these
helper functions follow.  As environments are very similar to lists, the implementation
of the above functions are straight-forward.
\begin{code}
  ee-wk       : Δ ⊆ Ψ → EE Γ Δ → EE Γ Ψ
  ee-wk-zero  : EE Γ Δ → Γ ⊆ Ψ → EE Ψ Δ
  ee-tail     : EE (Γ ▹ is) Δ → EE Γ Δ
  zero-ee     : EE Γ Δ
  ee-plus     : (ρ ν : EE Γ Δ) → EE Γ Δ
  ee-map-sum  : EE Γ (Δ ▹ ix s) → EE Γ Δ
  ee-update+ : EE Γ Δ → (v : ar s ∈ Γ) (t : E Δ (ar s)) → EE Γ Δ
  _▹𝟘 : EE Γ Δ → EE (Γ ▹ ar s) (Δ ▹ ar s)
\end{code}
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

  zero-ee = env (zero-env)

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
  ee-plus (env ρ) (env ν) = env (env-plus ρ ν)
  ee-plus (env ρ) (let′ x ν) = let′ x (ee-plus (ee-wk (skip ⊆-eq) (env ρ)) ν)
  ee-plus (let′ x ρ) ν = let′ x (ee-plus ρ (ee-wk (skip ⊆-eq) ν))

  δ ▹𝟘 = ee-push-zero $ ee-wk (skip ⊆-eq) δ
\end{code}

We define the function \AF{∇} that takes an expression \AF{E} and the seed
which is the multiplier on the left of the chain, and we compute a function
from that updates the environment.
\begin{code}
  {-# TERMINATING #-}
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
  ∇ (logistic e)           s   = ∇ e (let′ (logistic e) ((s ↑) ⊠ var v₀ ⊠ (one ⊞ minus (var v₀))))
  
  ∇ (let′ e e₁)            s   = λ δ → ∇ₗ e (let′ e (∇ e₁ (s ↑) (δ ▹𝟘)))

  ∇Σ e s δ = ee-plus δ $ ee-tail $ ee-map-sum (∇ e s zero-ee)

  ∇ₗ e (env (ρ ▹ x))  = ee-tail $ let′ x (∇ (e ↑) (var v₀) (env ρ ▹𝟘))
  ∇ₗ e (let′ x ρ)     = let′ x (ee-tail $ ∇ₗ (e ↑) (ee-wk-zero ρ (keep (skip ⊆-eq))))
\end{code}
\todo[inline]{Old text}
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

\todo[inline]{Replace the old text, explain that we are semantically-preserving now}
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
\subsection{Compilation}

We had two reasons to define the embedded langauge \AF{E}.
Firstly, \AF{E} makes it possible to implement automatic differention
within Agda, as we described in the previous section.
Secondly, we compile expressions in \AF{E} into
a programming langauge that can produce efficient code.  This
section describes extraction process into Futhark.

Futhark is a functional language with automatic memory management and
built-in type for arrays.  Futhark provides key array combinators such as
map and reduce, which makes translation process straight-forward.  
There are two non-trivial aspects of the process that we describe below.

\paragraph{Static Ranks} In Futhark, array rnaks are static. This means that
it is not possible to translate any expression in \AF{E} into Futhark.
We assume that all the ranks are known statically, which is true for
many numerical applications including our running example.


\paragraph{Normalisation} Consider translating an expression like
\AC{sel} (\AC{imap} λ i → \AB{e}) \AB{u}.  If you were to treat arrays
as functions and selections as applications, then the above expression
can be normalised into $e[i := u]$.  One could hope that Furhark could do
such a $\beta$-reduction on the generated code, but this is not the case.
The intuition for this choice is that in Futhark arrrays are tabulated
functions, and inlnining arbitrary evaluation of array elements may
have a significant performance cost.  For example, in the expression
\texttt{let a = imap \textbackslash i -> }$e$ \texttt{in imap \textbackslash j -> a[f j]}, Futhark
allocates memory for $a$ and computes all the values, an within the
body of the let, selection actually looks up the elements.  If we were
to inline $a$ by replacing $a[f\ j]$ with $e[i := f\ j]$, we loose sharing
by potentially recomputing $e$ much more often than needed
(e.g. assume that $i$ ranges over 10 elements, but $j$ over $10^5$).
Resolving when such inlining is beneficial for perfoamance is non-trivial,
therefore Futhark (and many other array languages) do not inline 
computation of array elements.  For our running example, naive translation
results in too many cases when arrays are constructed just to select
an element from them.  Therefore, we need some notion of normalisation
prior extraction.


We are going to combine normalisation and extraction in a single step,
resulting in something similar to normalisation by evaluation.
We model Futhark arrays as Agda functions space which makes it
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
  open Array hiding (_++_; Ix)
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
is simply a list of strings (the name of the index) per dimension:
\begin{code}
  data Ix : S → Set where 
    []  : Ix []
    _∷_ : String → Ix s → Ix (n ∷ s)
\end{code}
The \AF{Sem} function gives an interpretation to types of \AF{E} expressions.
Indices are just interpreted as \AF{Ix} of the corresponding shape.  Array
types are morally functions fro indices to strings.  However, in the definition
the type is a little more complicated:
\begin{code}
  Sem : IS → Set
  Sem (ar s) = (Ix s → State ℕ ((String → String) × String))
  Sem (ix s) = Ix s
\end{code}
Let us explain the complexity of the array type.  First of all, the codomain
of the array is wrapped into a state monad which gives a source of fresh variable
names.  Within the monad we have a pair we have a functoin which represents
a context for the actual array computation which is the second argument.
This context is needed because of the interplay between let bindings and
imaps.  Consider for a moment that we do not have explicit context in the
type for \AC{ar} and we are compiling an expression
\AF{Let} z \AF{:=} \AC{zero} \AF{in} \AF{Imaps} λ i → z which can result in
somehing like:
\begin{code}
  f : Ix s → State ℕ String
  f i = return ("let z = 0 in " ++ (λ j → "z") i)
\end{code}
If we selct into this array (by applying it to some index expression)
or compose it with other functions, this works as expected.  However,
at a certain point we may need to turn this experssion into the actual
array, which looks something like \AS{"imap λ i → "} \AF{++} f \AS{"i"}.
However, this expression evaluates to \AS{"imap λ i → let z = 0\ in z"},
but this inlines computation of let binding in the body of the imap,
which may have a serious performance impact if let binds a non-trivial
computation.  By introducing contexts in \AF{Sem}, we just control where
the imap code is injected.  Generally speaking, our strategy here is to
preserve sharing that is introduced by let bidings, yet normalise
bound expressions and bodies.

For the actual extraction we define the environment of Futhar values
called \AF{FEnv}.  Two functions that actually do the translation are
\AF{to-fut} which computest the \AF{Sem} value, and \AF{to-str} that
calls \AF{to-fut} and wraps the result with \AF{imap} as we described
above.
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

  
  bop : Bop -> String
  bop plus = "F.+"
  bop mul = "F.*"

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
Consider two cases of \AF{to-fut} for \AC{imap} an \AC{sel}.
In both cases the array we are constructing or selecting from is
of shape $s ++ p$.  We use two helper functions \AF{ix-curry}
and \AF{ix-uncurry} that translate between funtions of type
\AD{Ix (s ++ p)} → X and \AD{Ix} s → \AD{Ix p} → X.  In the
\AC{imap} case we generate a function keeping potential let
chains within the imap expression.  In case of \AF{sel}, we
are computing the value of the array we are slecting from (i.e. $a$)
and within the returned expression we apply $a$ to the correspoinding
indices --- this is normalisation step.
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
