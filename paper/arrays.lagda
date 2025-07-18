\section{Array Theory\label{sec:array-theory}}

\begin{code}[hide]
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List using (List; []; _∷_)
open import Data.Empty
open import Function

module _ where
module Array where
  open import Data.Nat using (zero; suc; ℕ; _+_; _*_; _≤_; s≤s; z≤n; _<_)
  open import Data.Nat.Properties using (+-mono-≤; ≤-step; ≤-pred; _≟_; +-comm; +-suc)
  open import Data.Fin as F using (zero; suc; Fin; combine; remQuot; fromℕ<; inject+; splitAt)
  open import Data.Fin.Properties using (suc-injective; toℕ<n; splitAt-inject+)
  --open import Fin2 using (Fin; #_; combine; remQuot; zerof; sucf; _⊕_; _⊝_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product as Prod hiding (map; zipWith) -- using (∃; ∃[_]_; _,_; _×_; uncurry)
\end{code}



\begin{wrapfigure}{r}{.6\linewidth}
\begin{lstlisting}[caption=SaC implementation of the CNN from~\cite{cnn-array},%
  label=fig:sac-code]
float [10,1,1,1,1] 
forward (float [28,28] I, float [6,5,5] k1,
         float [6] b1, float [12,6,5,5] k2,
         float [12] b2, float [10,12,1,4,4] k3,
         float [10] b) {
  c1 = logisitc (mconv(I, k1, b1));
  s1 = avgpool (c1);
  c2 = logisitc (mconv(s1, k2, b2 ));
  s2 = avgpool (c2);
  return logisitc (mconv(s2, k3, b));
}
\end{lstlisting}
\end{wrapfigure}
The running example that we use throughout this paper is the implementation of
a classical convolutional neural network that recognises hand-written digits.
Consider an implementation of the forward part of the network in the array 
language SaC~\cite{sac2}
from~\cite{cnn-array} which is presented in Listing~\ref{fig:sac-code}.
This is a function
that takes the image $I$, the weights $k_i$, biases $b_i$, and it computes
a vector of probabilities indicating which digit was depicted on that image.
The language does not provide any built-in CNN-specific operations, so all the
combinators such as \texttt{mconv}, \texttt{avgpool} and \texttt{logistic}
are defined as functions within the language.  The function that adjusts
the weights and biases based on data constitutes training process.  It is
defined manually in~\cite{cnn-array}, but in this paper we
will derive it automatically in later sections.

The above specification is concise
because all the combinators are defined\footnote{We omit the
definition for spaces reasons, but all the details can be found in~\cite{cnn-array}.}
\emph{rank-polymorphically}, which means that they can operate
on arrays of \emph{arbitrary ranks}.  

The goal of this section is to define a minimalist theory of multi-dimensional
arrays (ML calls them \emph{tensors}), which is well-suited for
specifying numerical applications such as the above example.
We also require our array theory to allow rank polymorphic definitions
which distinguishes it from most existing approaches.
The work in the rest of the paper is presented in Agda, with which we assume some
familiarity.
For gentle introductions to Agda we refer to one of the tutorials that are freely available
online.\footnote{See \url{https://agda.readthedocs.io/en/v2.7.0.1/getting-started/tutorial-list.html}.}

The central consideration when working with dependent types is how to represent data.
Some encodings are better suited for reasoning, others are more efficient
at runtime.  Due to our two-language setup, our choice of
representation is driven by proof considerations only --- low-level
details will be handled in the backend.
This is why we represent arrays as functions from indices to values.

Another goal of this development is to guarantee absence of out-of-bound errors,
meaning that all array indices fall within the shapes of the arrays that
they are selecting from.  The shape of an array describes the extent of each
of its axes.  

Let us consider a 1-dimensional representation of the $n$-element array
$X^n$.  The shape of such array is a natural number (\AB{n} : \AD{ℕ}).
Positions (indices) into this array are given by
(\AB{i} : \AD{Fin} \AB{n}), which ensures bounds safety for indexing operations.
Recall that the type (\AF{Fin} $n$) represents natural numbers bounded by $n$.
The data of the array is given by a function of type (\AD{Fin} \AB{n} → \AB{X}). 
When generalising to higher dimensions: the shape is not a single natural number,
but a list of natural numbers (\AB{s} : \AF{S}); positions are lists
of corresponding \AF{Fin} elements (\AB{i} : \AF{P} \AB{s}); and the
array data is given by function as before.  This approach to defining
data structure through shapes, positions and a function from positions
to elements is known as container~\cite{cont1,cont2,ix-containers}.
Our array type can be defined by means of the
(\AF{List ℕ} \AF{◃} \AF{All} \AF{Fin}) container.
More explicit formal definitions of \AF{S}, \AF{P} and \AF{Ar} are as follows.
\begin{mathpar}
\codeblock{\begin{code}
  data S : Set where
    []   : S
    _∷_  : ℕ → S → S
\end{code}
\begin{code}[hide]
  variable
    m n k : ℕ
    s p q r u w : S
    X Y Z : Set
\end{code}}
\and
\codeblock{\begin{code}
  data P : S → Set where
    []   : P []
    _∷_  : Fin n → P s → P (n ∷ s)
\end{code}}
\and
\codeblock{\begin{code}
  Ar : S → Set → Set
  Ar s X = P s → X
\end{code}}
\end{mathpar}

The type of shapes \AD{S} has two constructors. The \AC{[]} shape describes
an array of
rank zero (rank is the length of shape) that contains exactly one
element. Arrays of empty shape are often called \emph{scalars} and we use this
terminology in the rest of the paper.
The cons operation\footnote{
Note on the notation: underscores in \AC{\_∷\_} specify positions where
arguments go, turning \AC{∷} into an infix binary operation.}%
\AC{\_∷\_} prepends a new axis to the left of the shape.

Array positions (indices) are given by the dependent type \AD{P} which
is indexed by shapes \AD{S}.  A position within an array of shape \AB{s}
is a list of natural numbers of the same length as $s$ where all elements
are less than the corresponding elements of $s$.

Arrays are given by the type \AF{Ar} \AB{s} \AB{X} where $s$ is a shape of the
array and $X$ is the type of array elements. Once again, arrays of empty shapes
represents scalars.  Another way to look at \AF{Ar} is through tensor product:
\AF{Ar} $[]$ $X$ = $X$, and \AF{Ar} $[n_1, \dots, n_k]$ $X$ represents
components of a tensor $X^{n_1} \otimes \cdots \otimes X^{n_k}$.  

As arrays are functions, selection (indexing) is function applications,
the array constructor is a function definition (\eg{} via $\lambda$-abstraction).
Note that the \AF{Ar} definition could have pattern-matched on the shape,
in which case (\AF{Ar} [] $X$ = $X$) would hold definitionally.
We chose not to do this as we would need to introduce constructors
for array creation and selection, and we would lose
definitional array fusion (\AF{map} $f$ \AF{∘} \AF{map} $g$ = \AF{map} (f ∘ g))
which would make further proofs a bit more verbose.



\paragraph{Array Combinators} It is helpful to invest a little time
in defining array combinators.  While arrays have a lot of categorical structure,
here we only present the parts that are essential for our running example.
Firstly, we can observe that \AD{Ar} of
a fixed shape is an applicative functor~\cite{applicative}, so we can trivially derive:
\AF{K}\ \AB{x} to produce a constant array; \AF{map}\ \AB{f}\ \AB{a}
to apply \AB{f} to all the elements of \AB{a}; and \AF{zipWith}\ \AB{f}\ \AB{a}\ \AB{b} to point-wise apply the binary operation 
\AB{f} to \AB{a} and \AB{b} (note that \AF{zipWith} can be generalised
to the $n$-ary case as well).
\begin{mathpar}
\codeblock{\begin{code}
  K : X → Ar s X
  K x i = x
\end{code}}
\and
\codeblock{\begin{code}
  map : (X → Y) → Ar s X → Ar s Y
  map f a i = f (a i)
\end{code}}
\and
\codeblock{\begin{code}
  zipWith : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
  zipWith f a b i = f (a i) (b i)
\end{code}}
\end{mathpar}

Array shapes can be concatenated as lists.  We call this operation
\emph{shape product} and we denote it with \AF{\_⊗\_} (because this
corresponds to the shape of tensor product).  Positions of sub-shapes
can be joined into a position of a product shape using the \AF{\_⊗ₚ\_}
operation.  Dually, positions of a product shape can be split into
positions of the corresponding subshapes using \AF{split}.  The types
of these three operations are as follows.
\begin{mathpar}
\codeblock{\begin{code}
  _⊗_ : S → S → S
\end{code}}
\and
\codeblock{\begin{code}
  _⊗ₚ_ : P s → P p → P (s ⊗ p)
\end{code}}
\and
\codeblock{\begin{code}
  split : P (s ⊗ p) → P s × P p
\end{code}}
\end{mathpar}
\begin{code}[hide]
  [] ⊗ p = p
  (n ∷ s) ⊗ p = n ∷ (s ⊗ p)

  [] ⊗ₚ jv = jv
  (i ∷ iv) ⊗ₚ jv = i ∷ (iv ⊗ₚ jv)

  split {s = []}    is = [] , is
  split {s = x ∷ s} (i ∷ is) = Prod.map₁ (i ∷_) (split is)

  _≟ₚ_ : (i j : P s) → Dec (i ≡ j)
  _≟ₚ_ {[]} [] [] = yes refl
  _≟ₚ_ {x ∷ s} (i ∷ is) (j ∷ js) with i F.≟ j
  ... | no ¬p = no λ { refl → ¬p refl }
  ... | yes refl with is ≟ₚ js
  ... | no ¬q = no λ { refl → ¬q refl }
  ... | yes refl = yes refl
\end{code}

Arrays are homogeneously nested, \ie{} the shapes of all the sub-arrays
have to be the same.  Therefore, we can switch between the array of a product
shape and the nested array (array of arrays).  This operation is very similar
to currying except it happens at the level of shapes.  The combinators that
achieve this are named \AF{nest} and \AF{unnest} and their definitions are:
\begin{mathpar}
\codeblock{\begin{code}
  nest : Ar (s ⊗ p) X → Ar s (Ar p X)
  nest a i j = a (i ⊗ₚ j)
\end{code}}
\and
\codeblock{\begin{code} 
  unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
  unnest a i = uncurry a (split i)
\end{code}}
\end{mathpar}

One helpful categorical view on the above definition is:
\AF{Ar} is a monoidal functor between monoidal categories (\AF{S}, \AF{⊗}, \AC{[]})
and (\AF{Set} → \AF{Set}, \AF{∘}, \AF{id}), which is ensured
by \AF{nest} and \AF{unnest}.


\paragraph{Reduction} We implement reduction of the binary operations
over arrays in two steps.  Firstly, we define\footnote{
We define a \emph{pattern} \AF{ι} for singleton shapes.  Patterns are
definitions that can appear in pattern-matching
cases, such as in the definition of \AF{ιsuc}.  For more details, see
\url{https://agda.readthedocs.io/en/v2.7.0.1/language/pattern-synonyms.html}.
} 1-d reductions  that
we call \AD{sum₁} which is similar to right fold on lists.
Arrays of higher ranks iterate \AF{sum₁} bottom-up.  The definition
of the primitives are as follows:
\begin{mathpar}
\codeblock{\begin{code}
  pattern ι n = n ∷ []

  ιsuc : P (ι n) → P (ι (suc n))
  ιsuc (ι i) = ι (suc i)
\end{code}}
\and
\codeblock{\begin{code}
  sum₁ : (X → X → X) → X → Ar (ι n) X → X
  sum₁ {n = zero}   f ε a = ε
  sum₁ {n = suc n}  f ε a = f (a (ι zero)) (sum₁ f ε (a ∘ ιsuc))
\end{code}}
\and
\codeblock{\begin{code}
  sum : (X → X → X) → X → Ar s X → X
  sum {s = []}     f ε a = a []
  sum {s = x ∷ s}  f ε a = sum₁ f ε $ map (sum f ε) (nest a)
\end{code}}
\end{mathpar}

While \AF{sum} resembles \texttt{foldr}, its behaviour differs from that of a
conventional \texttt{foldr} over a free monad of a foldable functor.
Intuitively, rather than
selecting an order for the elements and reducing them, \AF{sum} reduces
lower-dimensional sub-arrays (conceptually in parallel) and subsequently
reduces the result. For instance, if we fix the binary operation \AB{f} and the
neutral element \AB{ε} (for example, \AF{σ} = \AF{sum} \AB{f} \AB{ε}), we can
demonstrate that \AF{σ} (\AF{map} \AF{σ} \AB{a}) \AF{≡} \AF{σ} (\AF{unnest}
\AB{a}) for all arrays \(a\). This property simplifies some of the proofs;
however, this subtlety becomes irrelevant when we operate within a monoid where
\AB{f} is the binary operation and \AB{e} is the neutral element.

It is also important to note that \AF{sum} enforces the types of the arguments
of the binary operation to be identical, which distinguishes it from the
conventional definitions of \texttt{foldr}. Although this generality is not
necessary for the purposes of this paper, it is noteworthy that the standard
behaviour can be recovered\footnote{We recover the regular fold behaviour by
applying \AD{sum} over function composition:
\begin{code}
  sum′ : (X → Y → Y) → Y → Ar s X → Y
  sum′ f ε a = sum _∘′_ id (map f a) ε
\end{code}
} through reduction of function composition.

% \paragraph{Reshaping}
% One common operation on arrays is element-preserving change of shape.  We call
% such an operation \AF{reshape}.  It is clear that array elements can be preserved only in
% cases when the number of elements in the original array and the reshaped one
% is the same.  We define an inductive relation \AF{Reshape} that relates
% only those shapes that preserve the number of array elements.  
% \begin{code}[hide]
%   infixr 5 _∙_
%   --infixl 10 _,_
% \end{code}
% \begin{mathpar}
% \codeblock{\begin{code}
%   data Reshape : S → S → Set where
%     eq      : Reshape s s
%     _∙_     : Reshape p q → Reshape s p → Reshape s q
%     _,_     : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
%     split   : Reshape (ι (m * n)) (ι m ⊗ ι n)
%     flat    : Reshape (ι m ⊗ ι n) (ι (m * n))
%     swap    : Reshape (s ⊗ p) (p ⊗ s)
%     assocl  : Reshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)
%     assocr  : Reshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))
% \end{code}}
% \end{mathpar}
% Any expression $r$ of
% the type (\AF{Reshape} \AB{s} \AB{p}) comes with a straight-forward action on
% indices that we denote \AF{\_⟨\_⟩} (its definition is omitted).
% Such a (contravariant) action translates
% the index within the shape \AB{p} into the index within the shape \AB{s}.
% Given this translation, we can easily define \AF{reshape} as shown below.
% \AF{Reshape} is constructed such that if $s$ and $p$ are related, then 
% $p$ and $s$ are related too.  This fact is given by the function \AF{rev}
% (its definition is omitted) and it immediately implies that all the
% actions on indices as well as array \AF{reshape}s are invertible.
% 
% Note that two shapes can be related by \AF{Reshape} in more than
% one way, which results in different array reshapes.  
% For example, consider \AF{Reshape} (\AC{ι} 5 \AC{⊗} \AC{ι} 4) (\AC{ι} 5 \AC{⊗} \AC{ι} 4)
% given by \AC{swap} or through (\AC{split} \AC{∙} \AC{flat}).  While the former transposes 
% the array elements, the latter does not.
% \begin{mathpar}
% \codeblock{\begin{code}
%   _⟨_⟩ : P p → Reshape s p → P s
% \end{code}}
% \and
% \codeblock{\begin{code}
%   reshape : Reshape s p → Ar s X → Ar p X
%   reshape r a = λ ix → a (ix ⟨ r ⟩)
% \end{code}}
% \and
% \codeblock{\begin{code}
%   rev : Reshape s p → Reshape p s
% \end{code}}
% \end{mathpar}
% From the perspective of category theory, if \AF{S} is an object then \AF{Reshape}
% is a Hom set, where \AC{eq} is identity and \AC{\_∙\_} is a composition with
% the expected properties.  In the language of containers~\cite{ix-containers}, \AF{Ar} is
% a container and \AF{Reshape} is an inductive subset of cartesian container morphisms.
% 


% \begin{code}[hide]
%   i ⟨ eq ⟩ = i
%   (i ⊗ j) ⟨ r , r₁ ⟩ = (i ⟨ r ⟩) ⊗ (j ⟨ r₁ ⟩)
%   i ⟨ r ∙ r₁ ⟩ = i ⟨ r ⟩ ⟨ r₁ ⟩
%   (ι i ⊗ ι j) ⟨ split ⟩ = ι (combine i j)
%   ι i ⟨ flat ⟩ = let a , b = remQuot _ i in ι a ⊗ ι b
%   (i ⊗ j) ⟨ swap ⟩ = j ⊗ i
%   ((i ⊗ j) ⊗ k) ⟨ assocl ⟩ = i ⊗ (j ⊗ k)
%   (i ⊗ (j ⊗ k)) ⟨ assocr ⟩ = (i ⊗ j) ⊗ k
%   
%   
%   rev eq = eq
%   rev (r , r₁) = rev r , rev r₁
%   rev (r ∙ r₁) = rev r₁ ∙ rev r
%   rev split = flat
%   rev flat = split
%   rev swap = swap
%   rev assocl = assocr
%   rev assocr = assocl
% \end{code}


\section{CNN Building Blocks\label{sec:cnn}}

Using the array theory and combinators from the previous section we
define the primitives that are needed for the CNN.

\subsection{One-dimensional convolution}
We start with plus and minus operations for 1-d indices which are
prerequisites for defining convolution.  Consider the definition of plus
(denoted \AF{⊕}) which adds two bounded indices $i$ and $j$ ---
we have the Agda implementation on the left hand side, and the information
about bounds on the right hand side.
\begin{code}[hide]
  inject-left : Fin (suc m) → Fin (suc (n + m))
  inject-left {m} {n} i rewrite +-comm n m  = inject+ _ i
  
  split-inj₁ : (i : Fin (m + n)) (k : Fin m) → splitAt m i ≡ inj₁ k → inject+ _ k ≡ i
  split-inj₁ {suc m} zero .zero refl = refl
  split-inj₁ {suc m} (suc i) zero p with splitAt m i | inspect (splitAt m) i
  split-inj₁ {suc m} (suc i) zero () | inj₁ x | [ r ]
  split-inj₁ {suc m} (suc i) zero () | inj₂ y | [ r ]
  split-inj₁ {suc m} (suc i) (suc k) p with splitAt m i | inspect (splitAt m) i
  split-inj₁ {suc m} (suc i) (suc .x) refl | inj₁ x | [ r ] = cong suc (split-inj₁ i x r)
  
  inj₁₂ : {A B : Set}{x : A}{y : B} → inj₁ x ≡ inj₂ y → ⊥
  inj₁₂ ()
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  _⊕_ : Fin m → Fin (1 + n) → Fin (m + n)
  zero   ⊕ j = inject-left j
  suc i  ⊕ j = suc (i ⊕ j)
\end{code}}
\and
\codeblock{\[
 \inferrule*
    {i < m \and j < 1 + n}
    {i+j < m + n}
  \and
\]}
\end{mathpar}
Recall that the type \AF{Fin} $n$ is a type for natural numbers $i$ that
are bounded by $n$ (\ie{} $i < n$).  The type of \AF{⊕} carries non-trivial
information about the index bounds.  We
add indices $i < m$ and $j < 1 + n$ as natural numbers, and the result of
addition is bound by $m + n$.  While this might be a little surprising, this
indeed holds for natural numbers.  Readers may convince themselves by
recalling that $j < 1 + n$ is the same as $j \le n$, or by considering
maximal values that $i$ and $j$ could possibly take.
Note that as indices $i$ and $j$ are added as natural numbers, there seem to be
no easy way to define \AF{⊕} in terms of (\AD{Fin} $(m + n)$ $\cong$
\AD{Fin} $m$ $⊎$ \AD{Fin} n) isomorphism, hence we use a direct definition.

While \AF{⊕} is a non-injective operation, we can define \emph{partial}
inverses which give rise to left and right subtraction.\footnote{
For the given $a$ and $b$, \emph{left} subtraction ($a -_{l} b$) means that we
solve $b + x = a$ for $x$, whereas \emph{right} subtraction ($a -_{r} b$)
means that we solve $x + b = a$ for $x$.
}
In the paper we consider left subtraction (denoted \AF{⊝}) --- its
Agda definition is given on the left hand side, and the information about
bounds on the right hand side.
\begin{mathpar}
\codeblock{\begin{code}
  _⊝_ : (i : Fin (m + n)) (j : Fin m)
      → Dec (∃[ k ] j ⊕ k ≡ i)
\end{code}}
\and
\codeblock{\[
   \inferrule*
    {r < m + n \and j < m}
    {\exists (k < 1 + n). j + k = r}
\]}
\end{mathpar}
\begin{code}[hide]
  _⊝_ {suc m} {n} i zero rewrite +-comm m n with splitAt (suc n) i | inspect (splitAt (suc n)) i
  ... | inj₁ k | [ r ] = yes (k , split-inj₁ i k r)
  ... | inj₂ k | [ r ] = no reason
    where
      reason : _
      reason (k , refl) rewrite splitAt-inject+ (suc n) m k = inj₁₂ r
  zero ⊝ suc j = no λ { (k , ()) }
  suc i ⊝ suc j with i ⊝ j
  ... | yes (k , p) = yes (k , cong suc p)
  ... | no ¬p = no λ { (k , p) → ¬p (k , suc-injective p) } 

  inject-left-zero : inject-left {m} {n} zero ≡ zero
  inject-left-zero {m} {n} rewrite +-comm n m = refl

  suc-not-zero : {i : Fin m} → _≡_ {A = Fin (suc m)} (suc i) zero → ⊥
  suc-not-zero ()

  inject-left-suc : ∀ (i : Fin m) → inject-left {m} {n} (suc i) ≡ zero → ⊥
  inject-left-suc {m} {n} i p rewrite +-comm n m = suc-not-zero p

  zero-suc-⊥ : ∀ {i : Fin n} → _≡_ {A = Fin (suc n)} zero (suc i) → ⊥
  zero-suc-⊥ ()

  -- TODO: this is annoying to do inductively on Fin, it is easier to
  --       implement this via Fin n = Σ ℕ (_< n) representation
  -- minusx : (i : Fin (m + n)) → (j : Fin (suc n)) → Dec (∃ λ k → k ⊕ j ≡ i)
  -- minusx {zero} i zero = no λ { (() , _) }
  -- minusx {suc m} {n} zero zero = yes (zero , inject-left-zero {n} {m})
  -- minusx {suc m} {n} (suc i) zero with minusx {m} i zero
  -- ... | yes (j , p) = yes (suc j , cong suc p)
  -- ... | no ¬p = no λ { (zero , p) → let rr = trans (sym $ inject-left-zero {n} {m}) p 
  --                                   in zero-suc-⊥ rr
  --                    ; (suc j , p) → ¬p (j , suc-injective p) }

  -- minusx {zero} i (suc j) = no λ { (() , p) }
  -- minusx {suc m} zero (suc j) = no λ { (zero , p) → inject-left-suc j p
  --                                    ; (suc k , ()) }
  -- minusx {suc m} {suc n} (suc i) (suc j) = ? 
\end{code}
The return type of \AF{⊝} says that there exists a decision procedure
(\AF{Dec} A = A \AF{⊎} \AF{¬} A) for finding a dependent pair\footnote{%
The \AF{∃} syntax makes it possible to omit the type of $k$, and it is
expands to \AF{Σ} (\AF{Fin} (\AB{n} + 1)) λ k → j \AF{⊕} k \AF{≡} i. 
}
where the first projection is the result of subtraction of type
\AF{Fin} (1 + \AB{n}) (that we bind to $k$), and the second projection
is a proof that $k$ is an inverse of \AF{⊕}.  The pair is needed to
ensure that if the index is returned it is actually the inverse.
The \AF{Dec} type serves two purposes.  Firstly, it ensures that the
function is partial (we could have achieved this with \AF{Maybe}).
Secondly, if the function does not return a result, it provides a
proof that the result could not possibly exist.  The latter guarantees,
thanks to dependent types,  that partial inverse is implemented correctly,
and the function does not return \AC{nothing} when there is actually
something.

% In some sense \AF{Dec} is similar to \AF{Maybe} type, except it forces one
% to prove why the value does not exist as opposed to just returning \AC{nothing}.
% For example, if we were to evaluate $i ⊝ j$ where $i = 1 < 3 + 5$ and $j = 2 < 3$,
% we will get a proof that there is no natural number $k < 1 + 5$ such that $2 ⊕ k ≡ 1$.
% Here dependent types come very useful, as we eliminate the possibility of
% introducing off-by-one errors in the definition of \AF{⊝}.


Now we are ready to define a 1-dimensional convolution.
A side note for mathematically inclined readers: we use the term
\emph{convolution} in the way it is used in machine learning.  Technically,
we compute a cross-correlation, because the array of weights is not flipped.
However, in practice this is not a problem, as we assume that weights are
stored flipped in memory.

We define type synonyms \AF{Vec} and \AF{Ix} which are 1-dimensional versions
of \AF{Ar} and \AF{P}.  We introduce the \AF{slide₁} primitive that selects a $(1+n)$-element vector
from the $(m+n)$-element vector starting at the offset $i$.  
\begin{mathpar}
\codeblock{\begin{code}
  Vec : ℕ → Set → Set
  Vec m X = Ar (ι m) X
\end{code}}
\and
\codeblock{\begin{code}
  Ix : ℕ → Set
  Ix m = P (ι m)
\end{code}}
\and
\codeblock{\begin{code}
  slide₁ : Ix m → Vec (m + n) X → Vec (1 + n) X
  slide₁ (ι i) v (ι j) = v (ι (i ⊕ j))
\end{code}}
\end{mathpar}
Then,
following~\cite{cnn-array}, we compute $m$-element array of slides
and then sum it up.
\begin{mathpar}
\codeblock{\begin{code}
  conv₁ : Vec (m + n) ℕ → Vec m ℕ → Vec (1 + n) ℕ
  conv₁ a w = sum₁ (zipWith _+_) (K 0) (λ i → map (w i *_) (slide₁ i a))
\end{code}}
\end{mathpar}
Note that in the definition of \AF{conv₁} we use a standard array language
trick --- we pull summation to the outside.  For example, for $m = 3$, $n = 2$,
a straight-forward way to compute (\AF{conv₁} $[a_1, a_2, a_3, a_4, a_5]$
$[w_1, w_2, w_3]$) would be $[a_1w_1 + a_2w_2 + a_3w_3, a_2w_1 + a_3w_2 +
a_4w_3,\dots]$.  However, the above definition proceeds as $w_1[a_1,a_2,a_3] +
w_2[a_2,a_3,a_4] + w_3[a_3,a_4,a_5]$ which computes the same result.  Such
definition makes it easy to replace the implementation of slide, obtaining
other versions of convolution such as the one with constant or cyclic
boundaries.  As we demonstrate in the next section, this pattern generalises
nicely to higher ranks.



\subsection{Generalisation\label{sec:general-ix-ops}}
We now generalise the 1-dimensional slide for arrays of higher ranks.
This requires generalising vector shapes $m + n$ and $1 + n$ for the cases
when $m$ and $n$ are arbitrary shapes.  
We do not define these operations as computations on shapes, because
we want to maintain the same arguments in the definition of the
generalised slide and the corresponding constructor in the
embedded DSL that we define in Section~\ref{sec:edsl}, and computations
in the type indices of the DSL constructors do not behave nicely.
Instead, we introduce relations.  In case of addition, we define a three-way
relation \AF{\_+\_≈\_}.  That is, the type \AB{p} \AF{+} \AB{q} \AF{≈} \AB{r}
says that
$p$ and $q$ have the same length and that $r$ is a point-wise addition
of $p$ and $q$.  A similar relation \AF{suc\_≈\_} is introduced for $1 + n$
case, and \AF{\_*\_≈\_} witnesses point-wise
multiplication that will be needed for blocking.  We define these relations
in two steps.  
Firstly we define \AF{Pw₂} and \AF{Pw₃} which lift a relation on
two (or three) natural numbers into corresponding pointwise relations on
two (or three) lists of natural numbers:\footnote{
This could be generalised even further by lifting relations over
types $X$ and $Y$ into relation of lists of $X$ and $Y$, but this
is not needed for the paper.}
\begin{mathpar}
\codeblock{\begin{code}
  data Pw₂ (R : (a b : ℕ) → Set) 
       : (a b : S) → Set where instance
      []    : Pw₂ R [] []
      cons  : ⦃ R m n ⦄ → ⦃ Pw₂ R s p ⦄
            → Pw₂ R (m ∷ s) (n ∷ p) 
\end{code}}
\and
\codeblock{\begin{code}
  data Pw₃ (R : (a b c : ℕ) → Set) 
       : (a b c : S) → Set where instance
      []    : Pw₃ R [] [] []
      cons  : ⦃ R m n k ⦄ → ⦃ Pw₃ R s p q ⦄
            → Pw₃ R (m ∷ s) (n ∷ p) (k ∷ q)
\end{code}}
\end{mathpar}
While the definition is straight-forward, note that we mark constructors
with the keyword \AK{instance} and we wrap the arguments of \AC{cons}
with \AF{⦃} \AF{⦄} brackets, turning them into instance arguments.\footnote{See \url{https://agda.readthedocs.io/en/v2.7.0.1/language/instance-arguments.html} for more details.}  These arguments
behave like the hidden arguments, except Agda will apply an instance
search when solving them.  This allows us to omit these proofs in
a larger number of cases than if we were to use hidden arguments.
This becomes useful in the definition of \AF{forward} at the end of
Section~\ref{sec:ar-cnn-prim}.

\begin{code}[hide]
  infix 5 _+_≈_
  infix 5 suc_≈_
  infix 5 _*_≈_
  infixl 8 _⊝ₚ_
\end{code}

The second step is to define\footnote{
Recall that the type of propositional equality \AF{\_≡\_} is ($X$ → $X$ → \AF{Set}).
In this particular case, $X$ is \AF{ℕ}.}
the actual relations.  With the help of two composition
combinators ($f$ \AF{∘} $g$ = λ $x$ → $f$ ($g$ $x$)) and 
($f$ \AF{∘₂} $g$ = λ $x$ $y$ → $f$ ($g$ $x$ $y$)),
the definitions are as follows.
\begin{mathpar}
\codeblock{\begin{code}
  _+_≈_ : (s p q : S) → Set
  _+_≈_ = Pw₃ (_≡_ ∘₂ _+_)
\end{code}}
\and
\codeblock{\begin{code}
  _*_≈_ : (s p q : S) → Set
  _*_≈_ = Pw₃ (_≡_ ∘₂ _*_)
\end{code}}
\and
\codeblock{\begin{code}
  suc_≈_ : (s p : S) → Set
  suc_≈_ = Pw₂ (_≡_ ∘ suc)
\end{code}}
\end{mathpar}

With these relations in place, we could define generalised convolution
similarly to \AF{sum} where we recurse over the shape, performing one
operation at a time.  However, there is a good point made
in~\cite{cnn-array} about shifting the shape recursion into index computation.
% Talk about mental model of runtime where arrays are flat and indices are offsets
Therefore we define \AF{\_⊕ₚ\_} and \AF{\_⊝ₚ\_} which generalise \AF{\_⊕\_} and
\AF{\_⊝\_} for higher ranks.  Once again, the \AD{Dec} type forces \AF{⊝ₚ} to justify
the cases when the inverse does not exist.
\begin{mathpar}
\codeblock{\begin{code}
  _⊕ₚ_ : P s → P u → suc p ≈ u → s + p ≈ r → P r
  _⊝ₚ_ : (i : P r) (j : P s) (su : suc p ≈ u) (sp : s + p ≈ r) → Dec (∃[ k ] (j ⊕ₚ k) su sp ≡ i)
\end{code}}
\end{mathpar}
The implementations of \AF{⊕ₚ} and \AF{⊝ₚ} (both elided for brevity) simply apply \AF{⊕} and \AF{⊝}.
In the \AF{⊝} case a little plumbing is required when constructing the
proof of (non-)existence of the inverse.
\begin{code}[hide]
  (i ⊕ₚ j) [] [] = j
  ((i ∷ is) ⊕ₚ (j ∷ js)) (cons ⦃ refl ⦄ ⦃ sp ⦄) (cons ⦃ refl ⦄ ⦃ s+p ⦄)
    = (i ⊕ j) ∷ (is ⊕ₚ js) sp s+p

  ([] ⊝ₚ j) [] [] = yes ([] , refl)
  ((i ∷ is) ⊝ₚ (j ∷ js)) (cons ⦃ refl ⦄ ⦃ sp ⦄) (cons ⦃ refl ⦄ ⦃ s+p ⦄) 
        with i ⊝ j
  ... | no ¬p = no λ { ((k ∷ _) , refl) → ¬p (k , refl) }
  ... | yes (k , p) with (is ⊝ₚ js) sp s+p
  ... | no ¬q = no λ { ((_ ∷ xs) , refl) → ¬q (xs , refl) }
  ... | yes (ks , q) = yes (k ∷ ks , cong₂ _∷_ p q)
\end{code}

Generalised \AF{slide} looks very similar to its 1-dimensional
counterpart, except that \AF{⊕} is replaced with \AF{⊕ₚ}
We also introduce a section\footnote{
If we apply \AF{slide} after \AF{backslide} we get the same array back.
Formally, we prove: ∀ $j$ → \AF{slide} $i$ $sp$ (\AF{backslide}
$i$ $a$ $su$ $e$ $sp$) $su$ $j$ \AF{≡} $a$ $j$.
}
of \AF{slide} that we call \AF{backslide}.
It embeds a $(1+p)$-dimensional array into a $(s+p)$-dimensional
one at the offset $i$ using \AB{def} to fill the outer region.
\begin{mathpar}
\codeblock{\begin{code}
  slide : P s → s + p ≈ r → Ar r X → suc p ≈ u → Ar u X
  slide i pl a su j = a ((i ⊕ₚ j) su pl)

  backslide : P s → Ar u X → suc p ≈ u → (def : X) → s + p ≈ r → Ar r X
  backslide i a su def pl j with ((j ⊝ₚ i) su pl)
  ... | yes (k , _)  = a k
  ... | _            = def
\end{code}}
\end{mathpar}
\begin{code}[hide]
  -- Here we prove that slide i (backslide i a) ≡ a
  inject-+-inj : ∀ n (i j : Fin m) → inject+ n i ≡ inject+ n j → i ≡ j
  inject-+-inj n zero zero p = refl
  inject-+-inj n (suc i) (suc j) p = cong suc (inject-+-inj n i j (suc-injective p))

  inject-left-inj : (i j : Fin (suc m)) 
                  → inject-left {n = n} i ≡ inject-left j
                  → i ≡ j
  inject-left-inj {m = m}{n} i j pf rewrite +-comm n m = inject-+-inj _ _ _ pf

  thm₁ : (i : Fin m) (j k : Fin (suc n))
      → (i ⊕ k) ≡ (i ⊕ j)
      → k ≡ j
  thm₁ zero j k pf = inject-left-inj _ _ pf
  thm₁ (suc i) j k pf = thm₁ i j k (suc-injective pf) 

  ∷-eq₁ : ∀ {i j : Fin n}{xs ys : P s} →  i ∷ xs ≡ j ∷ ys → i ≡ j
  ∷-eq₁ refl = refl 
  ∷-eq₂ : ∀ {i j : Fin n}{xs ys : P s} →  i ∷ xs ≡ j ∷ ys → xs ≡ ys 
  ∷-eq₂ refl = refl 

  thm : (i : P s) (j k : P u) (su : suc p ≈ u) (sp : s + p ≈ r)
      → (i ⊕ₚ k) su sp ≡ (i ⊕ₚ j) su sp
      → k ≡ j
  thm i j k [] [] pf = pf
  thm (x ∷ i) (x₁ ∷ j) (x₂ ∷ k) (cons ⦃ refl ⦄ ⦃ su ⦄) (cons ⦃ refl ⦄ ⦃ sp ⦄) pf 
    = cong₂ _∷_ (thm₁ x _ _ (∷-eq₁ pf)) (thm _ _ _ _ _ (∷-eq₂ pf)) 

  slide-back : ∀ (i : P s) (sp : s + p ≈ r) a (su : suc p ≈ u) (e : X)
             → ∀ j → slide i sp (backslide i a su e sp) su j ≡ a j
  slide-back {s = s}{p}{r}{u} i sp a su e j 
      with ((i ⊕ₚ j) su sp ⊝ₚ i) su sp
  ... | yes (k , pf) rewrite thm i j k _ _ pf = refl
  ... | no ¬p = ⊥-elim (¬p (j , refl))
\end{code}
Note that we keep explicit shape relations in the type signature of
\AF{slide}/\AF{backslide}, as we intend to introduce builtin operations
of that type in the embedded DSL in Section~\ref{sec:edsl}.

\paragraph{Remark on indexing} We would like to address a general remark that
is often made by functional programmers that index-oriented definitions such as
\AF{slide} and \AF{backslide} should be replaced by some construction that uses
algebraic data types.  While this is of course a matter of taste, here are
important points that justify our choice. Firstly, array computations that use
explicit indices are easier to compile into efficient code. At runtime, arrays
will be represented as flat regions of memory without cons cells or other
pointer-connected structures. Index computations will be turned into offset
computations that are efficient on most architectures.  Secondly, many
rank-polymorphic operations on arrays are easier to express via index
manipulation (our indices have non-trivial structure) rather than via
traversals of algebraic data structures.  For example, consider a data
structure for a rank-polymorphic array similar to \AD{Ar}.  One needs something
like a free monad over a \AD{Vec} type, which can be easily defined.  Now,
consider defining a generalised transpose on such representation.  Transpose of
an \AD{Ar} array is simply a selection on a reversed index: λ ix → a
(\AF{reverse} ix). In case of free monads, this is a significantly more
complicated recursive expression.

%Finally, when arrays are
%functions, fusion equalities (\eg{} map f ∘ map g $\cong$ map (f ∘ g))
%come for free through normalisation, which makes formal reasoning easier.





\subsection{CNN primitives\label{sec:ar-cnn-prim}}
Here we implement CNN-specific primitives that are needed for our running example.
All these primitives operate on arrays of reals.  We use builtin Agda floats in
the rest of the section that we refer to as \AD{ℝ}.  The only reason for this
is the ability to evaluate our specification with concrete values.
Later we are going to abstract over concrete implementation of \AD{ℝ}.

Generalised convolution is given by \AF{conv}, and it is almost identical to its
1-dimensional counterpart (except it uses \AF{slide} instead of \AF{slide₁}).
The \AF{mconv} runs a batch of $u$ \AF{conv}s (conceptually in parallel) and then it adds a
corresponding bias from the array $b$ (of shape $u$) to each convolution.
Note that \AF{conv}/\AF{mconv} are generic in a semiring structure on \AD{ℝ},
and \AF{conv₁} can be seen as a 1-dimensional version of \AF{conv} in terms
of the semiring on \AD{ℕ}.

\begin{code}[hide]
module CNN where
  open import Data.Nat as ℕ using (ℕ)
  open import Data.Float as F using (_+_; _*_; _÷_; e^_; -_; fromℕ) renaming (Float to ℝ)
  open import Data.Product as Prod using ()
  open import Data.Fin as F using (zero; suc; Fin; combine; remQuot; fromℕ<; inject+; splitAt)
  open Array
\end{code}

\begin{code}
  conv : s + p ≈ r → Ar r ℝ → Ar s ℝ → suc p ≈ u → Ar u ℝ
  conv sp a w su = sum (zipWith _+_) (K 0.0) λ i → map (w i *_) (slide i sp a su)

  mconv : ⦃ s + p ≈ r ⦄ → Ar r ℝ → Ar (u ⊗ s) ℝ → Ar u ℝ → ⦃ suc p ≈ q ⦄ → Ar (u ⊗ q) ℝ
  mconv ⦃ sp ⦄ inp w b ⦃ su ⦄ = unnest λ i → map (b i +_) (conv sp inp (nest w i) su)
\end{code}
The logistic function computes ${1}/(1 + e^{-x})$ for every element in the array.
\begin{mathpar}
\codeblock{\begin{code}
  logistic : Ar s ℝ → Ar s ℝ
  logistic = map λ x → 1.0 ÷ (1.0 + e^ (- x))
\end{code}}
\end{mathpar}

\paragraph{Average Pooling}
One of the layers of the CNN is average pooling which
splits an array into sub-blocks and computes the average for every such
block.  Implementing this pattern generally is tricky as we have to
preserve the local neighbourhood within the blocks.  Working with a
blocked array would be inconvenient as the blocked shape
does not go well with \AF{slides}.  We solve this by introducing
blocked selections \AF{selb} into arrays of shape $(s * p)$ as well
as blocked array constructor \AF{imapb} that builds an array of
shape $(s * p)$ out of $s$ blocks of shape $p$.  Defining these
operations we require pairing and projections of the blocked indices
which is achieved by applying division and modulo operation on the
components.  The types of these operations are as follows:
\begin{mathpar}
\codeblock{\begin{code}
  ix-div : P q → s * p ≈ q → P s
\end{code}}
\and
\codeblock{\begin{code}
  ix-mod : P q → s * p ≈ q → P p
\end{code}}
\and
\codeblock{\begin{code}
  ix-combine : P s → P p → s * p ≈ q → P q
\end{code}}
\end{mathpar}
\begin{code}[hide]
  ix-div is [] = is
  ix-div (i ∷ is) (cons ⦃ refl ⦄ ⦃ pf ⦄) 
    = Prod.proj₁ (F.remQuot _ i) ∷ ix-div is pf

  ix-mod is [] = is
  ix-mod (i ∷ is) (cons {m = m} ⦃ refl ⦄ ⦃ pf ⦄)
    = Prod.proj₂ (F.remQuot {m} _ i) ∷ ix-mod is pf

  ix-combine i j [] = j
  ix-combine (i ∷ is) (j ∷ js) (cons ⦃ refl ⦄ ⦃ ps ⦄) 
    = F.combine i j ∷ ix-combine is js ps
\end{code}
With these operations, definitions of \AF{selb} and \AF{imapb}
are:

\begin{mathpar}
\codeblock{\begin{code}
  selb : Ar q X → s * p ≈ q → Ar s (Ar p X)
  selb a p i j = a (ix-combine i j p)
\end{code}}
\and
\codeblock{\begin{code}
  imapb : Ar s (Ar p X) → s * p ≈ q → Ar q X
  imapb a p i = a (ix-div i p) (ix-mod i p)
\end{code}}
\end{mathpar}
We define an average pooling that is specialised to
2-dimensional cases as needed per our running example.
\begin{mathpar}
\codeblock{\begin{code}
  avgp₂ : (m n : ℕ) → Ar (m ℕ.* 2 ∷ n ℕ.* 2 ∷ []) ℝ → Ar (m ∷ n ∷ []) ℝ
  avgp₂ m n a = map ((_÷ fromℕ 4) ∘ sum _+_ 0.0) (selb a it)
\end{code}}
\end{mathpar}
Note that \AF{avgp₂} forces a programmer to provide explicit sizes
of the blocked array, and it will not admit arrays of shape such as
$2 * m \times 2 * n$, because $m * 2$ is not definitionally equal to $2 * m$.

With these primitives we implement a forward part of the CNN using
Listing~\ref{fig:sac-code} as a blueprint.
The \AB{inp} argument is the image of a hand-written digit, all
the other arguments are weights, and the function returns the 10-element vector
containing a probability for each digit. Note that type annotations in 
\AK{let}s\footnote{
We use \AK{let} instead of \AK{where} so that the definition of \AF{forward}
can be easily translated to the embedded DSL which only has lets.  While Agda's
lets are always inlined, which might be inefficient, we never intend to
run this particular code.
}
are purely for documentation --- Agda infers them automatically and these lines
can be removed.  Note also that all the \AF{mconv} applications do not require
explicit proofs as Agda can compute them from the shape information provided
in types. 
\begin{mathpar}
\codeblock{
\begin{code}
  forward : (inp  :  Ar (28 ∷ 28 ∷ []) ℝ) → (k₁ : Ar (6 ∷ 5 ∷ 5 ∷ []) ℝ)
          → (b₁   :  Ar (6  ∷ []) ℝ)      → (k₂ : Ar (12 ∷ 6 ∷ 5 ∷ 5 ∷ []) ℝ)
          → (b₂   :  Ar (12 ∷ []) ℝ)      → (fc : Ar (10 ∷ 12 ∷ 1 ∷ 4 ∷ 4 ∷ []) ℝ)
          → (b    :  Ar (10 ∷ []) ℝ)      → Ar (10 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []) ℝ
  forward inp k₁ b₁ k₂ b₂ fc b = let
      c₁ : Ar (6 ∷ 24 ∷ 24 ∷ []) ℝ
      c₁ = logistic $ mconv inp k₁ b₁ 

      s₁ : Ar (6 ∷ 12 ∷ 12 ∷ []) ℝ
      s₁ = unnest {s = 6 ∷ []} $ map (avgp₂ 12 12) (nest c₁)

      c₂ : Ar (12 ∷ 1 ∷ 8 ∷ 8 ∷ []) ℝ
      c₂ = logistic $ mconv  s₁ k₂ b₂ 

      s₂ : Ar (12 ∷ 1 ∷ 4 ∷ 4 ∷ []) ℝ
      s₂ = unnest {s = 12 ∷ 1 ∷ []} $ map (avgp₂ 4 4) (nest c₂)

      r = logistic $ mconv s₂ fc b 
    in r
\end{code}
}
\end{mathpar}

