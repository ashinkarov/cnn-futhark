# Major changes

* We rewrote the beginning of Section 5, which fixed some unfortunate
typos, and addressed the following comments of the reviewers:

> (A) 
> l702-735: Why so much white space? This seems like a perfect place to insert some diagrams/graphs!

> (C)
> - Is the terminology adjoint standard? I've seen "partials" or "1-forms" for these objects.

> (D)
> - l696ff This section may offer opportunities for salvaging some space if you are struggling with the page limit:
>   it feels things are spaced out much more generously than in the other sections.
> - Section 5: There is a drop in quality in the exposition of this section.  It deserves some serious polishing.
> 
> - l717 Having to juggle with the aliases $y = w₃$ and $x = w₀$ obstructs the pattern.
> 
> - l720 What role is served by $f x y$ here?  Why not simply $z = \sin(xy + x)$.
> 
> - l737ff I am totally lost here.  Please provide more calculation steps for each line.
>          You got plenty of unused horizontal space here!
> 
> - l746 "If we inline all the $\bar{w}ᵢ$ definitions"  Again more steps please.
>     If I do this myself, I am left with $\bar{w}₀ = \cos w₃ + (\cos w₃)²·x$ which isn't close to the results you report.


* We explained the difference between sum and foldr combinators, and we fixed the
definition in the Agda code, as suggested by reviewers D and E so that sum and sum₁
compute the same result on 1-d arrays.  This addresses the following comments:

> (A)
> l136: why call this a sum rather than a fold? this is particularly confusing as later sum is just a sum.

> (D)
> - l137ff What is called `sum` is really a `fold`, even if you only use it with addition later.
> 
> - l142 Why is the base case not simply `sum {s = []} f ε a = a []`?
>   I tried this out with your Agda artifact and it works, one can simplify some proofs.
> 
>   An array of zero dimensions is a single scalar.  A combination of all its elements is thus just this one scalar.
>   I think your starting point was the `foldr` intuition where the result always in corporates the neutral element,
>   but maybe thinking in terms of non-empty folds (`fold1`) is more appropriate here.

> (E)
> * why go the trouble of defining 1-dimensional versions of `sum`
>   etc. and end up with definitions which are mismatched/off-by-one
>   between the 1-dimensional and general cases? Eg. the definitions of
>   `sum₁ : (A → A → A) → A → Vec n A → A` and `sum : (A → A → A) → A →
>   Ar s A → A` do *not* agree in the case `s = ι n`, ie. `sum₁ {n = n}
>   f e` and `sum {s = ι n} f e` are *not* extensionally equal unless
>   `f e` is the identity function. Did you intend this? If so, please
>   explain why.

* We changed the title of the paper, as suggested by the reviewer E:

> p.1
> This perhaps does mean you can get away with some of the more
> rhetorical flourishes in the Introduction, but I think that the title
> is a bit misleading ("Correctness meets Performance: from Agda to
> Futhark" seems as though it would be a slightly more honest version?
> the second paragraph of the introduction makes that pipeline/trade-off
> more explicit), and the Abstract reads a bit flat in the context of
> the more dramatic Intro.

* We added the example in SaC in section two, as proposed bu reviewer E,
  thus resolving:

> p.2
> The 'running example' of the SAC implementation of a CNN in fact only
> appears eventually on p.7, and it might be better to at least show the
> original code (or fragments) before diving into Agda; few readers will
> be expert in both, possibly neither, so some handholding would help,
> not least to prime the reader to accept that the eventual Agda
> implementation is indeed faithful to the original.

* Rewrote the way we introduce `Ar` datatype, providing more intuition
  and referring to containers.  This resolves:

> (A)
> l102: It would be helpful to say here what the intended semantics of Ar [n1, ..., nk] is, i.e. R^{n1 x ... x nk} = R^{n1} (x) ... (x) R^{nk}.
> 
> (C)
> - l99 Maybe add a footnote to the extend that `S ▷ P` is a container (I guess that motivated the letters `S` and `P`).
>   However, I agree with your choice to not overload the paper with technical terms that do not help understanding.
>
> (E)
> You introduce the fundamental representation of higher-rank tensors
> (arrays) as a container type, in terms of 'shapes' and 'positions',
> without any mention of the pioneering work in this area by Abbott et
> al. ("Categories of Containers", 2003), or that of Joyal et al. at
> UQAM on combinatorial species.
>
> Similarly, you launch into the discussion of the Agda representation
> without taking the small amount of space to explain that a
> 1-dimensional array (vector) $X^n$ can be represented in terms of the
> shape (dimension) `n : ℕ`, positions (indices) `i : Fin n` (thereby
> ensuring bounds safety for indexing operations), as a function `Fin n
> → X`, and that your `Ar` construction then generalises this to
> higher-rank via *lists* of such dimensions. For the non-Agda
> specialist, this little bit of hand-holding might go a long way!

* We added a comment about categorical structure of combinators,
  which resolves:

> (A)
> l111: maybe note that you can define n-ary zipWith's even.
>
> (C)
> - 130: this is another "X is just Y" of the highest order, but I suppose one can remark that `nest`
>   and `unnest` ensure that `Ar - X` is a monoidal functor from `Shape` to `Type → Type` (with the
>   latter monoidal product coming from composition). Hardly the a pressing issue, but I found it
>   neat.
> (E)
> l.109 Rather than merely consider `Ar s` for fixed `s` to be an
> Applicative functor, wouldn't it be better to say that `Ar` is a
> *graded* applicative, graded with respect to the monoid structure on
> ranks-as-lists of dimensions? Not only that, but the `nest`/`unnest`
> isomorphism exhibit a corresponding 'linear'/'monoidal closed' structure (scare
> quotes because I'm not even sure what the correct terminology is here
> for graded functors)

* We motivated our choice why we do not define `Ar [] X = X`,
  hopefully resolving:

> (C)
> 
>  - 86: I'm a little confused, should an array of rank 0 not be simply the trivial vector
>    space/module? The space of scalars is dimension 1, not 0 in standard mathematics in my
>    experience.
> 
> (E)
> * given that you define `Ar s X = P s → X`, presumably to take
>   advantage in the back-end of arrays as 'purely functional', why do
>   you not discuss the trade-offs (esp. wrt elimination of those
>   iterated products defining `P`, including the troublesome case `s =
>   []`, introducing a redundant unit type representation) between this
>   version and a direct *recursive* implementation such as
>   
>   Ar : S → Set → Set
>   Ar [] X = X
>   Ar (n ∷ s) X = Fin n → Arr s X
>   
>   which would have the advantage(s) of:
>   
>   - avoiding having to distinguish scalars, at shape `[]`, from
>     functions from `P []` to scalars; similarly in the 1-dimensional
>     (vector) case
>   
>   - avoiding the marshalling/unmarshalling of iterated products of
>     positions via your `nest`/`unnest` operations, in favour of
>     iterated function composition
> 
>   - avoiding most, if not all, of the explicit operations on
>     positions, `_⊗ₚ_`, `split` etc. in favour of direct implementation
>     on the `Ar s X` types themselves (more on this later)

* Rewrote explanation about + and - for indices, resolving:

> (A)
> l160: "Dec" -- Just give the definition! It is not that hard and your current description is not enough to understand what it does.
> 
> l160: "\exists" -- Explain. Contrast with "\Sigma". Does the choice matter here?
> 
> l172-l180:  This is currently super unclear and should probably be rewritten.
>
> (C)
> - l169 I think the surprise goes away if the second hypothesis is written as $j ≤ n$ rather than $j + 1 < n$.
>
> (E)
> p.4
> I don't see the need for *decidability* of the `_⊖_` operation (and
> those which build on it later, etc.), rather than simply returning a
> `Maybe` option type, as the `slide` function (and subsequent friends)
> are going to use the `nothing` case to return a default, so full
> decidability, while impressive, seems like overkill.
>
> Similarly, the discussion of the type isomorphism seems muddled, when
> what is really going seems to be that are going to some lengths to
> skilfully avoid having to negotiate the equality `m + suc n ≡ suc (m +
> n)` in the type of positions?

* Explained pattern synonyms, resolving:

> (A)
> l136: "pattern" -- quickly recall pattern syntax for readers less familiar with Agda
>
> (C)
>
> - 136: I think one should briefly explain what "pattern" does in Agda, since this sort of syntax is
>   a bit more Agda-specific than what has come before. I think it can be guessed from context, but a
>   footnote or just a description of what to search in the Agda docs might be helpful.
>

* Rewrote explanation of generalised slide, resolving comments:

> (A)
> 
> l224: Explain instance argument syntax {{}} here.
> 
> l220-225: Say in prose what these relations do/capture.
> 
> l235: Remind readers of Agda's notation for identity types.
>
> (C)
> 
>  - 221: Incidentally, why is this specialized to natural numbers? Surely this works fine for an
>    arbitrary type A.
> 
> (E)
> Section 3.2
> ...

  While I attempted to do some suggested inlining, the overall result did look
  uglier (in my opinion) and took more space.  Therefore, I left the structure,
  but I tried to clarify all the concerns raised in the reviews.

* Introduced a proof that backslide is a section of slide, resolving:

> (A)
> l258: Equations relating slide and backslide?


