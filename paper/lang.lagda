\begin{code}[hide]
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List using (List; []; _∷_)
open import Data.Empty
open import Function

-- Our local files.
open import arrays
module _ where
\end{code}
\section{Embedded DSL}

Any implementation of automatic differentiation has to decide which operations
are supported.  Surely, it does not make sense to compute derivatives
of a function that opens a file.  This choice, no matter how it is implemented,
can be seen as a definition of an embedded language.
Once we accept to identify an embedded language, the idea of embedding it in a way
that facilitates extraction actually appears rather naturally and thus advances
the approach that we propose in this paper.

Coming back to our example, we have to choose the primitives that the embedded language
should support. They need to be sufficient to express AD as well as to define CNNs.
The main trade-off here is the choice of the level of abstraction of these primitives:
low-level primitives are easier to differentiate, but they make the overall expressions
more complex which also adds to the challenge of optimising code.
Making this choice is difficult and, most likely, requires quite some adjustment 
when striving for performance.
Here we see a key benefit of the approach we propose in this paper:
the use of a single framework for the embedding, the optimisation, and the extraction
makes the implementation comparatively small, allowing for quick adjustments in the
level of abstraction, code optimisation and its extraction.
We start with a pragmatic approach; we include the primitives that are either shared
by the model and the back-end
or that can be easily implemented in the back-end language.

It turns out that it is possible to choose the primitives in a way that the derivatives 
can be expressed in the very same embedded language. 
While this at first glance may just seem to be just a nice coincidence, it turns out
that this has several tangible benefits: high-order derivatives can be computed 
by the same transformation and we can share all optimisations between the code itself
and its derivatives.
\begin{code}[hide]
module Lang where
  open Array hiding (sum; slide; backslide)
  open import Data.Nat using (ℕ; zero; suc)
  infixl 15 _▹_
\end{code}

As we operate within a dependently-typed proof-assistant, we can easily make our
embedded language well-scoped and intrinsically typed (shaped in our case).  Our
context \AF{Ctx} is a snoc-list of shapes where each shape has a tag indicating whether
it is an index or an array.  We use de Bruijn variables given by the relation
\AF{\_∈\_} in the usual way.  We also define variables \AB{v₁}, \AB{v₂}, \etc{}
by iteratively applying \AC{vₛ} to \AC{v₀} (definition not shown).
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
Note that while our contexts are non-dependent (\ie{} the shapes do not depend on the
terms), we use non-trivial shape dependencies within the constructors.  The embedded
language does not have a notion of shape as a value, therefore all the shape dependencies
are handled by Agda, keeping our language simply typed (shaped).  This separation is
very helpful when it comes to writing embedded programs.% XXX: more explanation? 
\begin{code}[hide]
  --pattern v₀ = v₀
  pattern v₁ = vₛ v₀
  pattern v₂ = vₛ v₁
  pattern v₃ = vₛ v₂
  pattern v₄ = vₛ v₃
  pattern v₅ = vₛ v₄
  pattern v₆ = vₛ v₅
  pattern v₇ = vₛ v₆
  pattern v₈ = vₛ v₇
  pattern v₉ = vₛ v₈

  infixl 10 _⊞_
  infixl 15 _⊠_
\end{code}
We start with two helper definitions: a singleton shape that we call \AF{unit}
and the type for binary operations that we support (for now only addition and
multiplication).
\begin{mathpar}
\codeblock{\begin{code}
  unit : S
  unit = ι 1
\end{code}}
\and
\codeblock{\begin{code}
  data Bop : Set where
    plus mul : Bop
\end{code}}
\end{mathpar}

The embedded language \AF{E} includes: variables \AC{var}; constants 0 and 1 given
by \AC{zero} and \AC{one} correspondingly; three flavours of array constructor/eliminator
pairs given by \AC{imapₛ}/\AC{selₛ}, \AC{imap}/\AC{sel} and \AC{imapb}/\AC{selb};
summation \AC{sum}; conditional \AC{zero-but} where the predicate is fixed to equality
of two indices and the else branch is zero; \AC{slide} and \AC{backslide} exactly
as described before; and numerical operations.  The latter includes \AC{logistic},
plus and multiplication, division by a constant \AC{scaledown}, and unary \AC{minus}.
The definition of the embedded language \AF{E} follows.  We also introduce the
syntax for infix plus and multiplication denoted \AC{⊞} and \AC{⊠} correspondingly.
%\begin{mathpar}
%\codeblock{
\begin{code}
  data E : Ctx → IS → Set where
    var        : is ∈ Γ → E Γ is
    zero       : E Γ (ar s)
    one        : E Γ (ar s)

    imapₛ      : E (Γ ▹ ix s) (ar unit) → E Γ (ar s)
    selₛ       : E Γ (ar s) → E Γ (ix s) → E Γ (ar unit)

    imap       : E (Γ ▹ ix s) (ar p) → E Γ (ar (s ⊗ p))
    sel        : E Γ (ar (s ⊗ p)) → E Γ (ix s) → E Γ (ar p)

    imapb      : s * p ≈ q → E (Γ ▹ ix s) (ar p) → E Γ (ar q)
    selb       : s * p ≈ q → E Γ (ar q) → E Γ (ix s) → E Γ (ar p)

    sum        : E (Γ ▹ ix s) (ar p) → E Γ (ar p)
    zero-but   : E Γ (ix s) → E Γ (ix s) → E Γ (ar p) → E Γ (ar p)

    slide      : E Γ (ix s) → s + p ≈ r → E Γ (ar r) → suc p ≈ u → E Γ (ar u)
    backslide  : E Γ (ix s) → E Γ (ar u) → suc p ≈ u → s + p ≈ r → E Γ (ar r)

    logistic   : E Γ (ar s) → E Γ (ar s)
    bin        : Bop → E Γ (ar s) → E Γ (ar s) → E Γ (ar s)
    scaledown  : ℕ → E Γ (ar s) → E Γ (ar s)
    minus      : E Γ (ar s) → E Γ (ar s)


  pattern _⊠_ a b = bin mul a b
  pattern _⊞_ a b = bin plus a b
\end{code}
%}
%\end{mathpar}


\subsection{Evaluation}
\begin{code}[hide]
module Eval where
  open Lang
  open Array
  open import Data.Float as F renaming (Float to ℝ) hiding (⌊_⌋)
  open import Data.Unit
  open import Data.Product using (_×_; proj₁; proj₂; _,_)
  open import Data.Fin using (Fin; zero; suc; #_)
  open import Relation.Nullary.Decidable
  open import Data.Bool
\end{code}

We define the interpretation \AF{⟦\_⟧} for (\AF{E} \AB{Γ} \AB{is}) into the value
(\AF{Val} \AB{is}) in the environment (\AF{Env} \AB{Γ}).  The values are either
arrays or positions of the corresponding shape.  Environments for the given context
\AB{Γ} are tuples of values of the corresponding shapes.  The \AF{lookup} function
translates variables within the context into variables within the environment.
\begin{mathpar}
\codeblock{\begin{code}
  Val : IS → Set
  Val (ar s)  = Ar s ℝ
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

In the definition of \AF{⟦\_⟧} we wrap the environment argument into double braces.
This is an Agda-specific syntax for instance arguments\footnote{%
  For more details on instance arguments see:
  \url{https://agda.readthedocs.io/en/v2.6.3/language/instance-arguments.html}}
which behave similarly to hidden arguments, but they have a more powerful resolution
algorithm.  As a result we can omit mentioning the environment in recursive calls
when it is passed unchanged.
\begin{code}
  ⟦_⟧ : E Γ is → ⦃ Env Γ ⦄ → Val is
  ⟦ var x                ⟧ ⦃ ρ ⦄  = lookup x ρ
  ⟦ zero                 ⟧ ⦃ ρ ⦄  = K 0.0
  ⟦ one                  ⟧ ⦃ ρ ⦄  = K 1.0
  ⟦ imapₛ e              ⟧ ⦃ ρ ⦄  = λ i → ⟦ e ⟧ ⦃ ρ , i ⦄ (ι (# 0))
  ⟦ selₛ e e₁            ⟧ ⦃ ρ ⦄  = K $ ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ imap e               ⟧ ⦃ ρ ⦄  = unnest λ i → ⟦ e ⟧ ⦃ ρ , i ⦄
  ⟦ sel e e₁             ⟧ ⦃ ρ ⦄  = nest ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ imapb m e            ⟧ ⦃ ρ ⦄  = CNN.unblock m $ unnest λ i → ⟦ e ⟧ ⦃ ρ , i ⦄
  ⟦ selb m e e₁          ⟧ ⦃ ρ ⦄  = nest (CNN.block m ⟦ e ⟧) ⟦ e₁ ⟧
  ⟦ zero-but i j e       ⟧ ⦃ ρ ⦄  = if ⌊ ⟦ i ⟧ ≟ₚ ⟦ j ⟧ ⌋ then ⟦ e ⟧ else K 0.0
  ⟦ sum e                ⟧ ⦃ ρ ⦄  = Array.sum (zipWith _+_) (K 0.0) λ i → ⟦ e ⟧ ⦃ ρ , i ⦄
  ⟦ e ⊞ e₁               ⟧ ⦃ ρ ⦄  = Array.zipWith _+_ ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ e ⊠ e₁               ⟧ ⦃ ρ ⦄  = Array.zipWith _*_ ⟦ e ⟧ ⟦ e₁ ⟧
  ⟦ slide i pl e su      ⟧ ⦃ ρ ⦄  = Array.slide ⟦ i ⟧ pl ⟦ e ⟧ su
  ⟦ backslide i e su pl  ⟧ ⦃ ρ ⦄  = Array.backslide ⟦ i ⟧ ⟦ e ⟧ su 0.0 pl
  ⟦ scaledown n e        ⟧ ⦃ ρ ⦄  = Array.map (_÷ fromℕ n) ⟦ e ⟧
  ⟦ minus e              ⟧ ⦃ ρ ⦄  = Array.map (-_) ⟦ e ⟧
  ⟦ logistic e           ⟧ ⦃ ρ ⦄  = CNN.logistic ⟦ e ⟧
\end{code}
With the above definition we can better explain the choices of language constructors.
The most important question to clarify is why do we have three array
constructors/eliminators.  As the only conceptual datatype of our language is
an array (of some shape), we do not have any direct way to talk about array elements.
Therefore, we model the type of array elements (scalars) as arrays of a singleton shape.
As can be seen, scalar selection \AC{selₛ} returns a singleton array
(application of \AF{K}) where all the element(s) are equal to the element we are
selecting.  The corresponding array constructor \AC{imapₛ} makes sure that if we
compute \AB{s} elements of the shape \AF{unit}, we produce an array of shape \AB{s}
(and not \AB{s} \AC{⊗} \AF{unit}).  This soves the problem of constructing arays
from scalars, but how do we construct an array of a product shape?  Given that we
have an expression in the context (\AB{Γ} \AC{▹} \AC{ix} \AB{s} \AC{▹} \AC{ix} \AB{p}),
we need to produce an array of \AB{s} \AC{⊗} \AB{p}.  There are several ways how to
solve this (\eg{} introducing nest/unnest or projections and pairing on indices),
but it is clear that we need something more than just an \AC{imapₛ}.
This is the reason to introduce \AC{imap}/\AC{sel} pair which operates on arrays
of product shapes.  As average pooling operates on blocked arrays, we need
a construction to express this in \AF{E}.  One could introduce explicit 
\AF{block}/\AF{unblock}, but we merge blocking/unlocking action with
imap/sel obtaining \AC{imapb}/\AC{selb}.  Our \AC{sum} constructor 
gets an argument in the extended context which is summation index, so 
conceptually we generate the values at every summation index before
summing these values together.  As a result, we only need
one instance of \AC{sum} which makes our expressions a little tidier.




\subsection{Weakening and Substitution}

As our language has explicit de Bruin variables (as opposed to HOAS~\cite{hoas} approaches),
we need the means to do weakening and substitution when we optimise expressions in \AF{E}.
Our language is intrinsically typed(shaped) which
makes the definition of both operations challenging.  However, this problem has
been well-understood, and we adopt the solution from~\cite{subst}.  We only show the
basic mechanisms of the definition, for full details refer to~\cite{subst}.

The key structure that gives rise to weakening and substitution is a function that
computes the context \AB{Γ} \emph{without} the variable \AB{v} 
(denoted \AB{Γ} \AF{/} \AB{v}).  Then we define the weakening for
variables (\AF{wkv}) and expressions (\AF{wk}) that take a variable or expression
in the context without the variable \AF{v} and return this variable or expression
in the context where \AB{v} is present.
\begin{code}[hide]
module SubWk where
  open Lang
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  _/_ : (Γ : Ctx) → is ∈ Γ → Ctx
  (Γ ▹ x) / v₀    = Γ
  (Γ ▹ x) / vₛ v  = (Γ / v) ▹ x
\end{code}}
\and
\codeblock{\begin{code}  
  wkv  : (v : is ∈ Γ) → ip ∈ (Γ / v) → ip ∈ Γ
  wk   : (v : is ∈ Γ) → E (Γ / v) ip → E Γ ip
\end{code}}
\end{mathpar}
We give ourselves a nicer syntax for common cases when expressions
are lifted into the context with extra one or two variables:
\begin{code}[hide]
  infixr 18 ↑_
  infixr 18 ↑↑_
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  ↑_ : E Γ is → E (Γ ▹ ip) is
  ↑_ = wk v₀
\end{code}}
\and
\codeblock{\begin{code}
  ↑↑_ : E Γ is → E (Γ ▹ ip ▹ iq) is
  ↑↑_ = ↑_ ∘ ↑_
\end{code}}
\end{mathpar}
\begin{code}[hide]
  wkv v₀ w = vₛ w
  wkv (vₛ v) v₀ = v₀
  wkv (vₛ v) (vₛ w) = vₛ (wkv v w)
  
  wk v (var x) = (var (wkv v x))
  wk v zero = zero
  wk v one = one
  
  wk v (imapₛ e) = imapₛ (wk (vₛ v) e)
  wk v (selₛ e e₁) = selₛ (wk v e) (wk v e₁)
  --wk v (zero-butₛ idx e) = zero-butₛ (wk v idx) (wk v e)
  
  -- Copy-paste from scalar versions
  wk v (imap e) = imap (wk (vₛ v) e)
  wk v (sel e e₁) = sel (wk v e) (wk v e₁)
  --wk v (zero-but idx e) = zero-but (wk v idx) (wk v e)
  
  wk v (zero-but i j e) = zero-but (wk v i) (wk v j) (wk v e)
  wk v (sum e) = E.sum (wk (vₛ v) e)
  wk v (bin x e e₁) = bin x (wk v e) (wk v e₁)
  wk v (slide i pl e su) = E.slide (wk v i) pl (wk v e) su
  wk v (backslide i e su pl) = E.backslide (wk v i) (wk v e) su pl
  
  wk v (scaledown x e) = scaledown x (wk v e)
  wk v (minus e) = minus (wk v e)
  wk v (logistic e) = logistic (wk v e)
  --wk v (block x e) = block x (wk v e)
  --wk v (unblock x e) = unblock x (wk v e)
  wk v (imapb m e) = imapb m (wk (vₛ v) e)
  wk v (selb m e e₁) = selb m (wk v e) (wk v e₁)
  --wk v (zero-butb m e e₁) = zero-butb m (wk v e) (wk v e₁)
\end{code} 

A prerequisite for substitution is decidable equality
of variables which will be also useful during optimisations.  The code below
is a copy-paste from~\cite{subst}, but we reiterate its wonderfully mind-twisting
mechanics here.  The relation for variable equality is given by the type \AD{Eq}
which has two constructors.  In case variables are equal (\AC{eq} constructor)
they literally have to match.  In case variables $x$ and $y$ are different
(\AC{neq} constructor), we would like to know where to find $y$ in the context
without $x$.  After that, \AF{eq?} shows that variable equality is decidable.
The substitution \AF{sub} explains how to substitute the variable $v$ in the
expression $e$ with the expression $e₁$. 
\begin{mathpar}
\codeblock{\begin{code}
  data Eq : is ∈ Γ → ip ∈ Γ → Set where
    eq   : {x : is ∈ Γ} → Eq x x
    neq  : (x : is ∈ Γ) → (y : ip ∈ (Γ / x))
         → Eq x (wkv x y)

  sub : (v : is ∈ Γ) (e : E Γ ip) (e₁ : E (Γ / v) is)
      → E (Γ / v) ip
\end{code}}
\and
\codeblock{\begin{code}
  eq? : (x : is ∈ Γ) → (y : ip ∈ Γ) → Eq x y
  eq? v₀      v₀      = eq
  eq? v₀      (vₛ y)  = neq v₀ y
  eq? (vₛ x)  v₀      = neq (vₛ x) v₀
  eq? (vₛ x)  (vₛ y) with eq? x y
  ... | eq        = eq
  ... | neq .x y  = neq (vₛ x) (vₛ y)
\end{code}}
\end{mathpar}
% A common case of substituting the top variable
% can be defined as follows:
% \begin{code}
%   sub₀ : E (Γ ▹ is) ip → E Γ is → E Γ ip
%   sub₀ e e₁ = sub v₀ e e₁
% \end{code}
\begin{code}[hide]
  sub-var : (v : is ∈ Γ) → ip ∈ Γ → E (Γ / v) is → E (Γ / v) ip
  sub-var x y e with eq? x y
  ... | eq = e
  ... | neq .x y = var y
  
  sub v zero e₂ = zero
  sub v one e₂ = one
  
  sub v (var x) e₂ = sub-var v x e₂
  sub v (imapₛ e₁) e₂ = imapₛ (sub (vₛ v) e₁ (wk v₀ e₂))
  sub v (selₛ e₁ e₃) e₂ = selₛ (sub v e₁ e₂) (sub v e₃ e₂)
  
  sub v (imap e₁) e₂ = imap (sub (vₛ v) e₁ (wk v₀ e₂))
  sub v (sel e₁ e₃) e₂ = sel (sub v e₁ e₂) (sub v e₃ e₂)
  
  sub v (zero-but i j e) e₂ = zero-but (sub v i e₂) (sub v j e₂) (sub v e e₂)
  sub v (sum e₁) e₂ = E.sum (sub (vₛ v) e₁ (wk v₀ e₂))
  sub v (bin x e₁ e₃) e₂ = bin x (sub v e₁ e₂) (sub v e₃ e₂)
  sub v (slide i pl e su) e₂ = E.slide (sub v i e₂) pl (sub v e e₂) su
  sub v (backslide i e su pl) e₂ = E.backslide (sub v i e₂) (sub v e e₂) su pl
  
  sub v (scaledown x e) e₂ = scaledown x (sub v e e₂)
  sub v (minus e) e₂ = minus (sub v e e₂)
  sub v (logistic e) e₂ = logistic (sub v e e₂)
  
  sub v (imapb m e) e₂ = imapb m (sub (vₛ v) e (wk v₀ e₂))
  sub v (selb m e e₁) e₂ = selb m (sub v e e₂) (sub v e₁ e₂)
\end{code}

As our context do not encode explicit dependencies between the variables,
we can define the operation that swaps two consequent variables at any given
position in the context.  Similarly to (\AB{Γ} \AF{/} \AB{v}), we define the
function \AF{SwapAt} that computes the context where $x$ and its successor are
swapped.  Then we define the operation \AF{ctx-swap} that translates the expression
$e$ into the context where $x$ is swapped with its successor.
\begin{code}
  SwapAt : (Γ : Ctx) → is ∈ Γ → Ctx
  SwapAt (Γ ▹ is)       v₀           = Γ ▹ is
  SwapAt (Γ ▹ ip ▹ is)  v₁           = Γ ▹ is ▹ ip
  SwapAt (Γ ▹ ip ▹ is)  (vₛ (vₛ x))  = SwapAt (Γ ▹ ip) (vₛ x) ▹ is
  
  ctx-swap : (x : is ∈ Γ) (e : E Γ ip) → E (SwapAt Γ x) ip
\end{code}
\begin{code}[hide]
  var-swap : (x : is ∈ Γ) → ip ∈ Γ → ip ∈ SwapAt Γ x
  var-swap v₀ y = y
  var-swap v₁ v₀ = v₁
  var-swap v₁ v₁ = v₀
  var-swap v₁ (vₛ (vₛ y)) = vₛ (vₛ y)
  var-swap (vₛ (vₛ x)) v₀ = v₀
  var-swap (vₛ (vₛ x)) (vₛ y) = vₛ (var-swap (vₛ x) y)
  
  ctx-swap x zero = zero
  ctx-swap x one = one
  
  ctx-swap x (var y) = var (var-swap x y)
  ctx-swap v₀ (imapₛ e) = imapₛ e
  ctx-swap (vₛ x) (imapₛ e) = imapₛ (ctx-swap (vₛ (vₛ x)) e)
  ctx-swap x (selₛ e e₁) = selₛ (ctx-swap x e) (ctx-swap x e₁)
  ctx-swap v₀ (imap e) = imap e
  ctx-swap (vₛ x) (imap e) = imap (ctx-swap (vₛ (vₛ x)) e)
  ctx-swap x (sel e e₁) = sel (ctx-swap x e) (ctx-swap x e₁)
  ctx-swap v₀ (imapb m e) = imapb m e
  ctx-swap (vₛ x) (imapb m e) = imapb m (ctx-swap (vₛ (vₛ x)) e)
  ctx-swap x (selb m e e₁) = selb m (ctx-swap x e) (ctx-swap x e₁)
  ctx-swap x (zero-but e e₁ e₂) = zero-but (ctx-swap x e) (ctx-swap x e₁) (ctx-swap x e₂)
  ctx-swap v₀ (sum e) = E.sum e
  ctx-swap (vₛ x) (sum e) = E.sum (ctx-swap (vₛ (vₛ x)) e)
  ctx-swap x (bin op e e₁) = bin op (ctx-swap x e) (ctx-swap x e₁)
  ctx-swap x (slide e x₁ e₁ x₂) = E.slide (ctx-swap x e) x₁ (ctx-swap x e₁) x₂
  ctx-swap x (backslide e e₁ x₁ x₂) = E.backslide (ctx-swap x e) (ctx-swap x e₁) x₁ x₂
  ctx-swap x (scaledown x₁ e) = scaledown x₁ (ctx-swap x e)
  ctx-swap x (minus e) = minus (ctx-swap x e)
  ctx-swap x (logistic e) = logistic (ctx-swap x e)
\end{code}


\paragraph{Building Blocks}
Now we implement the remaining building blocks in \AD{E} that are needed
to define our CNN.
\begin{code}[hide]
module BB where
  open import Data.Nat as ℕ using (ℕ; zero; suc)
  open Array hiding (sum; slide; backslide)
  open Lang
  open SubWk using (wk; ↑_; ↑↑_)

  --_⊞_ _⊠_ : (a b : E Γ (ar s)) → E Γ (ar s)
  Imapₛ : (E (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar unit)) → E Γ (ar s)
  Imap : (E (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p)) → E Γ (ar (s ⊗ p))
  Sum : (E (Γ ▹ ix s) (ix s) → E (Γ ▹ ix s) (ar p)) → E Γ (ar p)
\end{code}
We start with a several convenience functions that wrap \AC{imap}s and \AC{sum}
such that when we write (\AF{Imap} \AB{λ} \AB{i} \AB{→} \AB{⋯}), Agda's variable
$i$ is mapped to the \AF{E}'s variable \AC{v₀}.
\begin{mathpar}
\codeblock{\begin{code}
  Imapₛ f = imapₛ (f (var v₀))
\end{code}}
\and
\codeblock{\begin{code}
  Imap f = imap (f (var v₀))
\end{code}}
\and
\codeblock{\begin{code}
  Sum f = sum (f (var v₀))
\end{code}}
\end{mathpar}

The remaining operations are \AF{conv}, \AF{mconv} and \AF{avgp₂} which
can be defined as functions on \AF{E} as follows.
\begin{code}
  conv : E Γ (ar r) → s + p ≈ r → E Γ (ar s) → suc p ≈ u → E Γ (ar u)
  conv f sp g su = Sum λ i → slide i sp (↑ f) su ⊠ Imapₛ λ _ → selₛ (↑↑ g) (↑ i)

  mconv : s + p ≈ r → (inp : E Γ (ar r)) (we : E Γ (ar (u ⊗ s))) (b : E Γ (ar u))
        → suc p ≈ w → E Γ (ar (u ⊗ w))
  mconv sp inp we b su = Imap λ i → conv (↑ inp) sp (sel (↑ we) i) su ⊞ Imapₛ λ _ → selₛ (↑↑ b) (↑ i)

  avgp₂ : ∀ m n → (a : E Γ (ar (ι (m ℕ.* 2) ⊗ ι (n ℕ.* 2)))) → E Γ (ar (ι m ⊗ ι n))
  avgp₂ m n a = Imapₛ λ i → scaledown 4 $ Sum λ j → selₛ (selb (ι ⊗ ι) (↑↑ a) (↑ i)) j

\end{code}
Note that these definitions are not very different from those found in
Section~\ref{sec:array-theory}.  Some operations such as \AF{nest} and \AF{unnest}
got inlined into \AF{E}'s operators, and all we really have to take care of is 
weakening of the expressions whenever we go under binders.

