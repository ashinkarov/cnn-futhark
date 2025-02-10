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
  open import Data.Fin using (zero; suc; Fin; combine; remQuot; fromℕ<; inject+; splitAt)
  open import Data.Fin.Properties using (suc-injective; toℕ<n; splitAt-inject+)
  --open import Fin2 using (Fin; #_; combine; remQuot; zerof; sucf; _⊕_; _⊝_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (∃; _,_)
\end{code}

The central data structures of our case study are multi-dimensional
arrays.  This section is dedicated to defining a minimalist array theory
in Agda which is well-suited for a specification of CNNs.

We assume that the reader is sufficiently familiar with Agda's syntax.
For gentle introductions we refer to one of the tutorials that are freely available
online\footnote{See \url{https://agda.readthedocs.io/en/v2.6.3/getting-started/tutorial-list.html}.}.

The conciseness of the specification
in~\cite{cnn-array} relies on rank-polymorphism, which is the ability to operate
on arrays of arbitrary rank.  We capture this feature in in our array theory.
The central consideration when working with dependent types is how to represent data.
Some encodings are better suited for reasoning, others are more efficient
at runtime.  Due to our two-language setup, our choice of representation is
driven by proof considerations only.
This enables us to represent arrays as functions from indices to values.

An absence of out-of-bound errors requires that all array indices fall within
the shapes of the arrays that they are selecting from.
The shape of an array describes the extent of each of its axes.  We represent shapes
as binary trees of natural numbers using the data type \AD{S}.
Leaves of the shape tree are constructed with \AC{ι} which takes one
argument.  The \AC{\_⊗\_} constructor makes a tree of two sub-trees.
Note that underscores in \AC{\_⊗\_} specify the position where arguments
go, therefore \AC{⊗} is an infix binary operation.

Array positions (indices) are given by the dependent type \AD{P} which
is indexed by shapes.  A position within an array of shape \AB{s} has exactly the
same tree structure as \AB{s}, but the leaves are natural numbers that
are bounded by the corresponding shape elements.

Arrays are given by the data type \AF{Ar} which is indexed by a shape
and an element type.  The formal definitions of \AF{S}, \AF{P} and \AF{Ar} are
as follows:
\begin{mathpar}
\codeblock{\begin{code}
  data S : Set where
    ι    : ℕ → S
    _⊗_  : S → S → S
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
    ι    : Fin n → P (ι n)
    _⊗_  : P s → P p → P (s ⊗ p)
\end{code}}
\and
\codeblock{\begin{code}
  Ar : S → Set → Set
  Ar s X = P s → X
\end{code}}
\end{mathpar}
As arrays are functions, selections are function applications and
array construction is a function definition (\eg{} via $\lambda$-abstraction).

\paragraph{Array Combinators} It is helpful to invest a little time
in defining array combinators.  First, we can observe that \AD{Ar} of
a fixed shape is an applicative functor~\cite{applicative}, so we can trivially derive:
\AF{K}\ \AB{x} to produce a constant array; \AF{map}\ \AB{f}\ \AB{a}
to apply \AB{f} to all the elements of \AB{a}; and \AF{zipWith}\ \AB{f}
\ \AB{a}\ \AB{b} to point-wise apply the binary operation 
\AB{f} to \AB{a} and \AB{b}.
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

Arrays are homogeneously nested, \ie{} the shapes of all the sub-arrays
have to be the same.  Therefore, we can switch between the array of a product
shape and the nested array (array of arrays).  This operation is very similar
to currying except it happens at the level of shapes.  The combinators that
achieve this are named \AF{nest} and \AF{unnest} and their definitions are:
\begin{mathpar}
\codeblock{\begin{code}
  nest : Ar (s ⊗ p) X → Ar s (Ar p X)
  nest a i j = a (i ⊗ j)
\end{code}}
\and
\codeblock{\begin{code} 
  unnest : Ar s (Ar p X) → Ar (s ⊗ p) X
  unnest a (i ⊗ j) = a i j
\end{code}}
\end{mathpar}


\paragraph{Reduction} We implement reduction of the binary operations
over arrays in two steps.  Firstly, we define 1-d reductions  that
we call \AD{sum₁} which is very similar to right fold on lists.
The arrays of higher ranks iterate \AF{sum₁} bottom-up.  The definition
of the primitives are as follows:
\begin{mathpar}
\codeblock{\begin{code}
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
  sum {s = ι n}    f ε a = sum₁ f ε a
  sum {s = s ⊗ p}  f ε a = sum f ε $ map (sum f ε) (nest a)
\end{code}}
\end{mathpar}

Note that our reduction forces the types of the arguments of the binary
operation to be the same, which is different from the usual foldr definition.
While we do not need this functionality for our example,
it is worth noting that the standard behaviour can be recovered\footnote{
We recover regular fold behaviour by running \AD{sum} over function composition:
\begin{code}
  sum′ : (X → Y → Y) → Y → Ar s X → Y
  sum′ f ε a = sum _∘′_ id (map f a) ε
\end{code}
} through reduction of function composition.

\paragraph{Reshaping}
One common operation on arrays is element-preserving change of shape.  We call
such an operation \AF{reshape}.  It is clear that array elements can be preserved only in
cases when the number of elements in the original array and the reshaped one
is the same.  We define an inductive relation \AF{Reshape} that relates
only those shapes that preserve the number of array elements.  
\begin{code}[hide]
  infixr 5 _∙_
  --infixl 10 _,_
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  data Reshape : S → S → Set where
    eq      : Reshape s s
    _∙_     : Reshape p q → Reshape s p → Reshape s q
    _,_     : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
    split   : Reshape (ι (m * n)) (ι m ⊗ ι n)
    flat    : Reshape (ι m ⊗ ι n) (ι (m * n))
    swap    : Reshape (s ⊗ p) (p ⊗ s)
    assocl  : Reshape (s ⊗ (p ⊗ q)) ((s ⊗ p) ⊗ q)
    assocr  : Reshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))
\end{code}}
\end{mathpar}
Any expression $r$ of
the type (\AF{Reshape} \AB{s} \AB{p}) comes with a straight-forward action on
indices that we denote \AF{\_⟨\_⟩} (its definition is omitted).
Such a (contravariant) action translates
the index within the shape \AB{p} into the index within the shape \AB{s}.
Given this translation, we can easily define \AF{reshape} as shown below.
\AF{Reshape} is constructed such that if $s$ and $p$ are related, then 
$p$ and $s$ are related too.  This fact is given by the function \AF{rev}
(its definition is omitted) and it immediately implies that all the
actions on indices as well as array \AF{reshape}s are invertible.

Note that two shapes can be related by \AF{Reshape} in more than
one way, which results in different array reshapes.  
For example, consider \AF{Reshape} (\AC{ι} 5 \AC{⊗} \AC{ι} 4) (\AC{ι} 5 \AC{⊗} \AC{ι} 4)
given by \AC{swap} or through (\AC{split} \AC{∙} \AC{flat}).  While the former transposes 
the array elements, the latter does not.
\begin{mathpar}
\codeblock{\begin{code}
  _⟨_⟩ : P p → Reshape s p → P s
\end{code}}
\and
\codeblock{\begin{code}
  reshape : Reshape s p → Ar s X → Ar p X
  reshape r a = λ ix → a (ix ⟨ r ⟩)
\end{code}}
\and
\codeblock{\begin{code}
  rev : Reshape s p → Reshape p s
\end{code}}
\end{mathpar}
From the perspective of category theory, if \AF{S} is an object then \AF{Reshape}
is a Hom set, where \AC{eq} is identity and \AC{\_∙\_} is a composition with
the expected properties.  In the language of containers~\cite{containers}, \AF{Ar} is
a container and \AF{Reshape} is an inductive subset of cartesian container morphisms.



\begin{code}[hide]
  i ⟨ eq ⟩ = i
  (i ⊗ j) ⟨ r , r₁ ⟩ = (i ⟨ r ⟩) ⊗ (j ⟨ r₁ ⟩)
  i ⟨ r ∙ r₁ ⟩ = i ⟨ r ⟩ ⟨ r₁ ⟩
  (ι i ⊗ ι j) ⟨ split ⟩ = ι (combine i j)
  ι i ⟨ flat ⟩ = let a , b = remQuot _ i in ι a ⊗ ι b
  (i ⊗ j) ⟨ swap ⟩ = j ⊗ i
  ((i ⊗ j) ⊗ k) ⟨ assocl ⟩ = i ⊗ (j ⊗ k)
  (i ⊗ (j ⊗ k)) ⟨ assocr ⟩ = (i ⊗ j) ⊗ k
  
  
  rev eq = eq
  rev (r , r₁) = rev r , rev r₁
  rev (r ∙ r₁) = rev r₁ ∙ rev r
  rev split = flat
  rev flat = split
  rev swap = swap
  rev assocl = assocr
  rev assocr = assocl
\end{code}


\section{CNN Building Blocks\label{sec:cnn}}

With the array theory from the previous section we can define the actual primitives 
that are required for our case study.

\subsection{One-dimensional convolution}
We start with plus and minus operations for 1-d indices which will
be used in the definition of convolution:
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
\codeblock{\begin{code}
  _⊝_ : (i : Fin (m + n)) (j : Fin m)
      → Dec (∃ λ k → j ⊕ k ≡ i)
\end{code}}
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
While the definitions look very innocent, their types carry non-trivial
information.  Consider \AF{\_⊕\_} which is addition of bounded $i$ and $j$.
However, the type says:
\begin{mathpar}
  \inferrule*
    {i < m \and j < 1 + n}
    {i+j < m + n}
\end{mathpar}
This looks a little surprising, but this indeed holds for natural numbers.
A reader may convince herself by considering the maximum value that $i$ and $j$
can possibly take.  The \AF{\_⊕\_} have partial inverses making it possible
to define left and right subtraction.  We consider left subtraction \AF{\_⊝\_}.
Its type says that there exists a decision procedure for finding $k$ of type
\AF{Fin} (1 + \AB{n}) together with the proof that $k$ is an inverse.
In some sense \AF{Dec} is similar to \AF{Maybe} type, except it forces one
to prove why the value does not exist as opposed to just returning \AC{nothing}.
This happens to be very useful, as it is really easy to introduce off-by-one
errors otherwise.


With the above definitions we can define convolution for 1-dimensional
cases.  A side note for mathematically inclined readers.  We use the term
\emph{convolution} in the way it is used in machine learning.  Technically,
we compute a cross-correlation, because the array of weights is not flipped.
However, in practice this is not a problem, as we assume that weights are
stored flipped in memory.

We define a handy shortcut \AF{Vec} and \AF{Ix} which are \AF{Ar} and \AF{P}
for 1-dimensional cases.\begin{mathpar}
\codeblock{\begin{code}
  Vec : ℕ → Set → Set
  Vec m X = Ar (ι m) X
\end{code}}
\and
\codeblock{\begin{code}
  Ix : ℕ → Set
  Ix m = P (ι m)
\end{code}}
\end{mathpar}
We introduce the \AF{slide₁} primitive that selects a $(1+n)$-element vector
from the $(m+n)$-element vector starting at the offset $i$.  Then,
following~\cite{cnn-array}, we compute $m$-element array of slides
and then sum it up.
\begin{mathpar}
\codeblock{\begin{code}
  slide₁ : Ix m → Vec (m + n) X → Vec (1 + n) X
  slide₁ (ι i) v (ι j) = v (ι (i ⊕ j))
  
  conv₁ : Vec (m + n) ℕ → Vec m ℕ → Vec (1 + n) ℕ
  conv₁ a w = sum (zipWith _+_) (K 0) (λ i → map (w i *_) (slide₁ i a))
\end{code}}
\end{mathpar}

\subsection{Generalisation\label{sec:general-ix-ops}}
We want to define convolution for arrays of higher ranks.  The first thing
to do is to express $m + n$ and $1 + n$ where $m$ and $n$ become arbitrary
shape trees.  In case of addition, we need a witness that both arguments
have the same tree structure.  If they do, we can simply add their nodes point-wise.
We define the three-way relation \AF{\_+\_≈\_} that combines the witness and
the action.  That is, the type \AB{p} \AF{+} \AB{q} \AF{≈} \AB{r} says that
$p$ and $q$ have the same tree structure and that $q$ is a point-wise addition
of $p$ and $q$.  We introduce a similar relation \AF{suc\_≈\_} for $1 + n$
case, and we introduce the relation \AF{\_*\_≈\_} that witnesses point-wise
multiplication that will be needed for blocking.
\begin{code}[hide]
  infix 5 _+_≈_
  infix 5 suc_≈_
  infix 5 _*_≈_
  infixl 8 _⊝ₚ_
  
  ι-injective : {i j : Fin n} → _≡_ {A = P (ι n)} (ι i) (ι j) → i ≡ j
  ι-injective refl = refl
  
  ⊗-fst-≡ : {i i′ : P s}{j j′ : P p} → _≡_ {A = P (s ⊗ p)} (i ⊗ j) (i′ ⊗ j′) → i ≡ i′
  ⊗-fst-≡ refl = refl
  
  ⊗-snd-≡ : {i i′ : P s}{j j′ : P p} → _≡_ {A = P (s ⊗ p)} (i ⊗ j) (i′ ⊗ j′) → j ≡ j′
  ⊗-snd-≡ refl = refl
  
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  data _+_≈_ : S → S → S → Set where
    ι    : ι m + ι n ≈ ι (m + n)
    _⊗_  : s + q ≈ u → p + r ≈ w 
         → s ⊗ p + q ⊗ r ≈ u ⊗ w
\end{code}}
\and
\codeblock{\begin{code}
  data suc_≈_ : S → S → Set where
    ι    : suc (ι n) ≈ ι (suc n)
    _⊗_  : suc s ≈ u → suc p ≈ w 
         → suc (s ⊗ p) ≈ u ⊗ w
\end{code}}
\and
\codeblock{\begin{code}
  data _*_≈_ : S → S → S → Set where
    ι    : ι m * ι n ≈ ι (m * n)
    _⊗_  : s * q ≈ u → p * r ≈ w → (s ⊗ p) * (q ⊗ r) ≈ u ⊗ w
\end{code}}
\end{mathpar}

With these relations in place, how do we define generalised convolution?  One
possible way is to use the \AF{sum} approach where we recurse over the shape
tree and perform one operation at a time.  However, there is a good point made
in~\cite{cnn-array} that we can shift the shape recursion into index computation.
% Talk about mental model of runtime where arrays are flat and indices are offsets
Therefore we define \AF{\_⊕ₚ\_} and \AF{\_⊝ₚ\_} which generalise \AF{\_⊕\_} and
\AF{\_⊝\_} for higher ranks.  Once again, \AD{Dec} type forces \AF{⊝ₚ} to justify
the cases when the inverse does not exist.
\begin{code}[hide]
--   XXX this implementation is needed if we switch to irrelevant Fin from the code.
--   data _≈ₚ_ : P s → P s → Set where
--     ι : ∀ {i j : Fin n} → Fin.index i ≡ Fin.index j → ι i ≈ₚ ι j
--     _⊗_ : ∀ {i k : P s}{j l : P p} → i ≈ₚ k → j ≈ₚ l → (i ⊗ j) ≈ₚ (k ⊗ l) 

--   _⊝ₚ_ : (i : P r) (j : P s) (su : suc p ≈ u) (sp : s + p ≈ r) 
--        → Dec (∃ λ k → (j ⊕ₚ k) su sp ≈ₚ i)
--   (ι i ⊝ₚ ι j) ι ι with i ⊝ j
--   ... | yes  (k , p)   = yes (ι k , ι p)
--   ... | no   ¬p        = no λ { (ι k , ι p) → ¬p (k , p) }
--   ((i ⊗ i′) ⊝ₚ (j ⊗ j′)) (su ⊗ su′) (sp ⊗ sp′) with (i ⊝ₚ j) su sp
--   ... | no   ¬p        = no λ { (k ⊗ k′ , p ⊗ p′) → ¬p (k , p)}
--   ... | yes  (k ,  p)  with (i′ ⊝ₚ j′) su′ sp′
--   ... | no   ¬p        = no λ { (k ⊗ k′ , p ⊗ p′) → ¬p (k′ , p′)}
--   ... | yes  (k′ , p′) = yes (k ⊗ k′ , p ⊗ p′)


  -- data _≈ₚ_ : P s → P s → Set where
  --   ι : {i j : Fin n} → i ≡ j → ι i ≈ₚ ι j
  --   _⊗_ : {i k : P s}{j l : P p} → i ≈ₚ k → j ≈ₚ l → (i ⊗ j) ≈ₚ (k ⊗ l) 

  p-eq-proj₁ : ∀ {i j k l} → _≡_ {A = P (s ⊗ p)} (i ⊗ j) (k ⊗ l) → i ≡ k
  p-eq-proj₁ refl = refl
  
  p-eq-proj₂ : ∀ {i j k l} → _≡_ {A = P (s ⊗ p)} (i ⊗ j) (k ⊗ l) → j ≡ l
  p-eq-proj₂ refl = refl

  _≟ₚ_ : (i j : P s) → Dec (i ≡ j)
  ι i ≟ₚ ι j with i Data.Fin.≟ j
  ... | yes p = yes (cong ι p)
  ... | no ¬p = no λ p → ¬p (ι-injective p)
  (i ⊗ j) ≟ₚ (i′ ⊗ j′) with i ≟ₚ i′ | j ≟ₚ j′
  ... | yes p | yes q = yes (cong₂ _⊗_ p q)
  ... | yes p | no ¬q = no λ r → ¬q (p-eq-proj₂ r)
  ... | no ¬p | _     = no λ r → ¬p (p-eq-proj₁ r)

\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  _⊕ₚ_ : P s → P u → suc p ≈ u → s + p ≈ r → P r
  (ι i       ⊕ₚ ι j)       ι         ι         = ι (i ⊕ j)
  ((a ⊗ a₁)  ⊕ₚ (b ⊗ b₁))  (s ⊗ s₁)  (p ⊗ p₁)  = (a ⊕ₚ b) s p ⊗ (a₁ ⊕ₚ b₁) s₁ p₁
  
  _⊝ₚ_ : (i : P r) (j : P s) (su : suc p ≈ u) (sp : s + p ≈ r) → Dec (∃ λ k → (j ⊕ₚ k) su sp ≡ i)
\end{code}}
\end{mathpar}
We do not show the implementation of the \AF{⊝ₚ}, but it very much follows the
structure of \AF{⊕ₚ}: we apply \AF{⊝} on the leaves and we recurse on the product
shape with a little bit plumbing to construct the proof of (non-)existence of the
inverse.
\begin{code}[hide]
  (ι i ⊝ₚ ι j) ι ι with i ⊝ j
  ... | yes  (k , p)   = yes (ι k , cong ι p)
  ... | no   ¬p        = no λ { (ι k , p) → ¬p (k , ι-injective p) }
  ((i ⊗ i′) ⊝ₚ (j ⊗ j′)) (su ⊗ su′) (sp ⊗ sp′) with (i ⊝ₚ j) su sp
  ... | no   ¬p        = no λ { (k ⊗ k′ , p) → ¬p (k , ⊗-fst-≡ p)}
  ... | yes  (k ,  p)  with (i′ ⊝ₚ j′) su′ sp′
  ... | no   ¬p        = no λ { (k ⊗ k′ , p) → ¬p (k′ , ⊗-snd-≡ p)}
  ... | yes  (k′ , p′) = yes (k ⊗ k′ , cong₂ _⊗_ p p′)
\end{code}

Our generalised \AF{slide} looks very much the same as its 1-dimensional
counterpart.  All the difference lies in the index computation.  We also
introduce a section of the slide that we call \AF{backslide} which embed
a $(1+p)$-dimensional array into a $(s+p)$-dimensional one at offset $i$
using some the provided default element \AB{def}.
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

\subsection{Remaining primitives}
In the rest of this section we implement the remaining CNN-specific primitives.
We are going to use the builtin Float type that we call \AD{ℝ} so that we can
run our specification with concrete values.  However, all we require from \AD{R}
is a set of standard arithmetic operations.  Therefore, \AD{ℝ} can be abstracted
out as a parameter.

Generalised convolution is given by \AF{conv}, and it is almost identical to its
1-dimensional counterpart (except it used \AF{slide} instead of \AF{slide₁}).
The \AF{mconv} runs $u$ \AF{conv}s adds biases to each of them from the array $b$.
\begin{code}[hide]
module CNN where
  open import Data.Nat as ℕ using (ℕ)
  open import Data.Float as F using (_+_; _*_; _÷_; e^_; -_; fromℕ) renaming (Float to ℝ)
  open Array
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  conv : s + p ≈ r → Ar r ℝ → Ar s ℝ → suc p ≈ u → Ar u ℝ
  conv sp a w su = sum (zipWith _+_) (K 0.0) λ i → map (w i *_) (slide i sp a su)
\end{code}}
\and
\codeblock{\begin{code}
  mconv : s + p ≈ r → (inp : Ar r ℝ) (w : Ar (u ⊗ s) ℝ) (b : Ar u ℝ)
        → suc p ≈ q → Ar (u ⊗ q) ℝ
  mconv sp inp w b su = unnest λ i → map (b i +_) (conv sp inp (nest w i) su)
\end{code}}
\end{mathpar}
The logistic function computes ${1}/(1 + e^{-x})$ for every element in the array.
\begin{mathpar}
\codeblock{\begin{code}
  logistic : Ar s ℝ → Ar s ℝ
  logistic = map λ x → 1.0 ÷ (1.0 + e^ (- x))
\end{code}}
\end{mathpar}

\paragraph{Average Pooling}
One of the steps of the machine learning algorithm is average pooling which
splits an array into sub-blocks and computes the average for every such
block.  While this sounds almost trivial, implementing this generally is
quite tricky.  In the proposed framework it is
not straight-forward to block an array of shape (\AC{ι} 12 \AC{⊗} \AC{ι} 12)
into an array of shape  ((\AC{ι} 6 \AC{⊗} \AC{ι} 6) \AC{⊗} (\AC{ι} 2 \AC{⊗} \AC{ι} 2)).
The difficulty is in preserving local neighbourhood within the blocks (for example
it would be wrong to flatten the array and then reshape it into the desired shape
as the local neighbourhood will be lost).  At the same time, it would be inconvenient
to block arrays beforehand as this does not go well with \AF{slides}.  Therefore
we introduce the mechanism to \AF{block} and \AF{unblock} arrays of shape $(s * p)$
and ($s$ \AF{⊗} $p$).

The key to array blocking is a reshaping operation that turns arrays
of shape (($s$ \AC{⊗} $p$) \AC{⊗} ($q$ \AC{⊗} $r$)) into arrays of shape 
(($s$ \AC{⊗} $q$) \AC{⊗} ($p$ \AC{⊗} $r$)), by swapping $p$ and $q$.
We express a \AF{Reshape} relation, and as it follows from the type
this reshape is a self inverse, as can be also seen from the theorem below:
\begin{mathpar}
\codeblock{\begin{code}
  rblock : Reshape ((s ⊗ p) ⊗ (q ⊗ r)) ((s ⊗ q) ⊗ (p ⊗ r))
  rblock = assocl ∙ eq , (assocr ∙ swap , eq ∙ assocl) ∙ assocr

  rblock-selfinv : ∀ i → i ⟨ rev (rblock {s} {p} {q} {r}) ⟩ ≡ i ⟨ rblock ⟩
  rblock-selfinv ((i ⊗ j) ⊗ (k ⊗ l)) = refl
\end{code}}
\end{mathpar}

With this primitive we define \AF{block} and \AF{unblock} as follow:
\begin{mathpar}
\codeblock{\begin{code}
  block : s * p ≈ q → Ar q X → Ar (s ⊗ p) X
  block ι          = reshape split
  block (l ⊗ r)    = reshape rblock ∘ unnest ∘ block l ∘ map (block r) ∘ nest
 
  unblock : s * p ≈ q → Ar (s ⊗ p) X → Ar q X
  unblock ι        = reshape flat
  unblock (l ⊗ r)  = unnest ∘ unblock l ∘ map (unblock r) ∘ nest ∘ reshape rblock
\end{code}}
\end{mathpar}
\begin{code}[hide]  
  block₂ : ∀ {X} → (m n : ℕ) → Ar (ι (m ℕ.* 2) ⊗ (ι (n ℕ.* 2))) X
         → Ar ((ι m ⊗ ι n) ⊗ (ι 2 ⊗ ι 2)) X
  block₂ m n = reshape (rblock ∙ (split {m} , split {n}))
\end{code}
We specialise average pooling to the 2-dimensional case, that is needed in
our running example.
\begin{mathpar}
\codeblock{\begin{code}
  avgp₂ : (m n : ℕ) → Ar (ι (m ℕ.* 2) ⊗ (ι (n ℕ.* 2))) ℝ → Ar (ι m ⊗ ι n) ℝ
  avgp₂ m n a = map ((_÷ fromℕ 4) ∘ sum _+_ 0.0) (nest $ block (ι ⊗ ι) a)
\end{code}}
\end{mathpar}

We are now ready to provide the implementation of the forward part of the CNN
as follows.  The \AB{inp} argument is the image of a hand-written digit, all
the other arguments are weights, and the function returns the 10-element vector
with probabilities which digit that is.
\begin{mathpar}
\codeblock{\begin{code}
  forward : (inp  :  Ar (ι 28 ⊗ ι 28) ℝ)         → (k₁   :  Ar (ι 6 ⊗ (ι 5 ⊗ ι 5)) ℝ)
          → (b₁   :  Ar (ι 6) ℝ)                 → (k₂   :  Ar (ι 12 ⊗ (ι 6 ⊗ (ι 5 ⊗ ι 5))) ℝ)
          → (b₂   :  Ar (ι 12) ℝ)                → (fc   :  Ar (ι 10 ⊗ (ι 12 ⊗ (ι 1 ⊗ (ι 4 ⊗ ι 4)))) ℝ)
          → (b    :  Ar (ι 10) ℝ)                → Ar (ι 10 ⊗ (ι 1 ⊗ (ι 1 ⊗ (ι 1 ⊗ ι 1)))) ℝ
  forward inp k₁ b₁ k₂ b₂ fc b = let
      c₁ : Ar (ι 6 ⊗ (ι 24 ⊗ ι 24)) ℝ
      c₁ = logistic $ mconv (ι ⊗ ι) inp k₁ b₁ (ι ⊗ ι)

      s₁ : Ar (ι 6 ⊗ (ι 12 ⊗ ι 12)) ℝ
      s₁ = unnest $ map (avgp₂ 12 12) (nest c₁)

      c₂ : Ar (ι 12 ⊗ (ι 1 ⊗ (ι 8 ⊗ ι 8))) ℝ
      c₂ = logistic $ mconv (ι ⊗ (ι ⊗ ι)) s₁ k₂ b₂ (ι ⊗ (ι ⊗ ι))

      s₂ : Ar (ι 12 ⊗ (ι 1 ⊗ (ι 4 ⊗ ι 4))) ℝ
      s₂ = unnest $ map (unnest ∘ map (avgp₂ 4 4) ∘ nest) (nest c₂)

      r = logistic $ mconv (ι ⊗ (ι ⊗ (ι ⊗ ι))) s₂ fc b (ι ⊗ (ι ⊗ (ι ⊗ ι)))
    in r
\end{code}}
\end{mathpar}


\begin{code}[hide]
module Tests where
  open import Data.String
  open import Data.Nat.Show renaming (show to shownat)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.Fin using (Fin; zero; suc; toℕ; #_)
  --open import Fin2 using (Fin; #_; combine; remQuot; zerof; sucf; _⊕_; _⊝_)
  open import Data.Product using (Σ; _,_; proj₁)
  open Array

  tab : ∀ {X} → Vec m X → List X
  tab {m = zero}  f = []
  tab {m = suc m} f = f (ι (# 0)) ∷ tab (f ∘ ιsuc)

  ListNest : S → Set → Set
  ListNest (ι _) = List
  ListNest (s ⊗ p) = ListNest s ∘ ListNest p

  atab : Ar s X → ListNest s X
  atab {ι _} a = tab a
  atab {s ⊗ p} a = atab (Array.map atab $ nest a)

  viota : (n : ℕ) → Vec n ℕ
  viota n (ι i) = toℕ i

  size : S → ℕ
  size (ι n) = n
  size (s ⊗ p) = size s * size p

  iota : Ar s ℕ
  iota {s = ι n} = viota n
  iota {s = s ⊗ p} = unnest (Array.map (λ i → Array.map (λ j → i * size p + j) iota) iota)

  test-block : _
  test-block = atab $ CNN.block₂ 2 2 iota

  _ : test-block 
      ≡ (((0 ∷ 1 ∷ []) ∷ (4 ∷ 5 ∷ []) ∷ []) ∷
         ((2 ∷ 3 ∷ []) ∷ (6 ∷ 7 ∷ []) ∷ []) ∷ [])
        ∷
        (((8 ∷ 9 ∷ []) ∷ (12 ∷ 13 ∷ []) ∷ []) ∷
         ((10 ∷ 11 ∷ []) ∷ (14 ∷ 15 ∷ []) ∷ []) ∷ [])
        ∷ []
  _ = refl

  _ : tab (slide₁ {m = 1}{n = 0} (ι (# 0)) iota) ≡ 0 ∷ []
  _ = refl
  
  _ : tab (slide₁ {m = 2}{n = 0} (ι (# 1)) iota) ≡ 1 ∷ []
  _ = refl

  
  backslide₁ : Ix m → Vec (suc n) X → X → Vec (m + n) X
  backslide₁ (ι i) v e (ι j) with j ⊝ i
  ... | yes (k , _) = v (ι k)
  ... | no _ = e

  test-⊕ = _⊕_ {m = 3} {n = 4} (# 1) (# 2)
  test-⊝ = _⊝_ {m = 3} {n = 4} (# 3) (# 1)

  _ : test-⊕ ≡ # 3
  _ = refl

  _ : test-⊝ ≡ yes (# 2 , refl)
  _ = refl

  test-backslide = tab $ backslide₁ {m = 3} {n = 4} (ι (# 2)) (viota 5) 121

  _ : test-backslide ≡ 121 ∷ 121 ∷ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  _ = refl

\end{code}








