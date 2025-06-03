This is a reply to the reviewer E which is written as a part of rebuttal.
As the review came after the rebuttal period was over, we are writing it
as a separate response.

Thank you for your excitement and very in-depth comments, we found them
tremendously helpful.

Before answering your questions, I'd like to make a general remark that
relate to a number of your comments.  I suppose that you are a kind of
reader who approaches problems through categorical, type-theoretical or
other foundational constructions.  This is great, I also like to do this.
Unfortunately, I have been criticised too many times for this.  I was
told that instead of getting straight to the point, I introduce too many
abstractions that are not necessary.  Therefore, the mindset I had when
writing this paper was: expose just enough constructions so that the
key ideas are well-defined and non-ambiguous.  I might have gone too
far with this, and I'd be more than happy to introduce more abstract
notions into new revision, but finding a good balance is difficult.


> Review #55E
> ===========================================================================
> 
> Overall merit
> -------------
> A. Good paper, I will champion it
> 
> Reviewer expertise
> ------------------
> 4. Expert
> 
> Reviewer confidence
> -------------------
> 3. High
> 
> Paper summary
> -------------
> This paper displays a synthesis of multiple techniques in 'modern' FP,
> targeted at the specimen application/running example of the MNIST
> benchmark in machine learning. It showcases the use of advanced type
> systems in FP, in this case, that of the Agda implementation of type
> theory, as well as that of the Futhark language for high-performance
> computation.
> 
> Specifically, the authors
> 
> * develop a rank- and bounds- safe language of rank-polymorphic tensor
>   algebra, including sums and convolutions necessary for purely
>   functional implementations of convolutional neural networks (CNN;
>   such as those required in the MNIST example)
> 
> * develop a scope-, type-, and rank- safe embedded *differentiable*
>   DSL for writing CNNs, paying careful attention to issues of
>   differentiability, sharing of subcomputations (eg. induced by
>   `let`), and impedance matching against the eventual chosen Futhark
>   backend for program extraction; together with the rudiments of a
>   semantically-justified theory of optimisation of DSL programs;
>   by analogy with LINQ, this is 'language-integrated gradient' computation?
> 
> * exhibit extraction to Futhark, with some specimen performance
>   comparison of the extracted code against the SOTA PyTorch and
>   TensorFlow frameworks
> 
> Comments for authors
> --------------------
> I really liked this paper... even though I think there are (very) many
> things that I think you could, and probably should, do to improve it
> if it ends up being accepted. The summary above captures the broad
> picture of what your paper achieves, and that alone is impressive.
> 
> I particularly appreciate how the paper demonstrates how advanced
> techniques in FP really do seem now to be available for end-use
> applications such as implementing CNNs to run on the MNIST example
> problem, and the end-to-end from Agda through to Futhark seems very
> convincing, despite each being very niche languages.
> 
> Detailed comments

> p.2
> The 'running example' of the SAC implementation of a CNN in fact only
> appears eventually on p.7, and it might be better to at least show the
> original code (or fragments) before diving into Agda; few readers will
> be expert in both, possibly neither, so some handholding would help,
> not least to prime the reader to accept that the eventual Agda
> implementation is indeed faithful to the original.

My reasoning here was that (a) SaC is quite an esoteric language for the
ICFP audience, and (b) the full code listing is relatively big, so I
decided to skip the SaC code entirely.  I agree with you regarding handholding,
and I am happy to summarise the SaC code before diving into Agda.
 
> You introduce the fundamental representation of higher-rank tensors
> (arrays) as a container type, in terms of 'shapes' and 'positions',
> without any mention of the pioneering work in this area by Abbott et
> al. ("Categories of Containers", 2003), or that of Joyal et al. at
> UQAM on combinatorial species.

I should definitely mention this.  I didn't want to introduce too much
theoretical constructions here, but I will definitely reference this work
which I am perfectly aware of.

> Similarly, you launch into the discussion of the Agda representation
> without taking the small amount of space to explain that a
> 1-dimensional array (vector) $X^n$ can be represented in terms of the
> shape (dimension) `n : ℕ`, positions (indices) `i : Fin n` (thereby
> ensuring bounds safety for indexing operations), as a function `Fin n
> → X`, and that your `Ar` construction then generalises this to
> higher-rank via *lists* of such dimensions. For the non-Agda
> specialist, this little bit of hand-holding might go a long way!

Good idea, thanks, will do.

> p.3
> You do a lot of heavy lifting here for the non-specialist, while not
> really discussing trade-offs in the details of the representation:
> 
> * why define the Shape type `S` directly as a `data` type definition,
>   and not simply in terms of Agda's `List` type constructor? (more
>   generally: what/how much could you simplify your implementation by
>   using off-the-shelf constructions in Agda's standard library?)

My reasoning here was as follows:  these definitions are fundamental to
the story, and they can be specified very shortly, so I thought I would
write them directly avoiding making assumptions about reader's familiarity
with Agda's standard library.  Otherwise, you are absolutely right, I
am working with a `List ℕ ◃ All Fin` container.  I do mention that
`S` is a list of ℕ in line 86, I can stress this harder.

As for simplifications from using `List` from the standard library,
I wouldn't say that too many things would become simpler.  You can see
that our `Ar` module is about 250 lines of code.  A small part of it
could be replaced with constructions from stdlib, but this is not a
significant gain.

> * why define the Positions type family `P` directly as a `data` type
>   definition, rather than as a definition by recursion on `S`, as an
>   iterated product type?

You can pattern-match on indices directly, which sometimes look nicer.
Otherwise there isn't much difference.

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

This is a good point, and I should add this discussion.  However, I would
like to note that the mentioned benefits are only achieved when working
with statically-known ranks/shapes.  Most of the interesting combinators are
defined rank-polymorphically, e.g. quantifying over `s` and `p` shapes.
In this case, we still need nest/unnest (or transport over the equality)
and split-like operations for the shapes `s ++ p`.

With the proposed definition, one has to pattern match on shapes more
than we do now.  For example, one needs to introduce selection separately,
whereas now it is just function application.  Another somewhat important
point is that with the proposed definition we will loose definitional
fusion: `map f (map g a) ≡ map (f ∘ g) a` which holds currently and
makes some of the proofs nicer.

> l.109 Rather than merely consider `Ar s` for fixed `s` to be an
> Applicative functor, wouldn't it be better to say that `Ar` is a
> *graded* applicative, graded with respect to the monoid structure on
> ranks-as-lists of dimensions? Not only that, but the `nest`/`unnest`
> isomorphism exhibit a corresponding 'linear'/'monoidal closed' structure (scare
> quotes because I'm not even sure what the correct terminology is here
> for graded functors)

This terminological confusion that you describe was exactly the motivation
to avoid this discussion entirely.  If we fix element types then I would
call `Ar - X` a monoidal functor.  I am happy to mention this.

> p.4
> I don't see the need for *decidability* of the `_⊖_` operation (and
> those which build on it later, etc.), rather than simply returning a
> `Maybe` option type, as the `slide` function (and subsequent friends)
> are going to use the `nothing` case to return a default, so full
> decidability, while impressive, seems like overkill.

Actually, I tend to disagree.  The trouble is that Maybe (specifically
in this case) can actually introduce off-by-one errors.  One can return
`nothing` in the case where the value actually exists.  We did find a
bug while translating the implementation of this particular function
from another language.  Therefore, while it is a bit of an overkill,
this is a useful safety measure.  I am happy to motivate this a little
bit more in the text.
 
> Similarly, the discussion of the type isomorphism seems muddled, when
> what is really going seems to be that are going to some lengths to
> skilfully avoid having to negotiate the equality `m + suc n ≡ suc (m +
> n)` in the type of positions?

It is a bit more subtle, as for `i : Fin m`, `j : Fin (1 + n)` their sum
(when using`+` from Fin's) is `i + j : Fin (toℕ i + suc n)`, but we need
`Fin (m + n)`.  As for the discussion about isomorphism, this is me literally
replying to the one of the reviewer's comment from the previous submission
attempt who said: your definition of `⊕` is overly complicated, surely
you can simplify this through the mentioned isomorphism...   I am happy
to have another go at explaining this bit.

> Section 3.2
> 
> This seems needlessly over-elaborate, at the potential cost of losing
> readers who are not Agda experts:
> 
> * the use of `instance`s, and instance resolution, for the sake of
>   optimising certain definitions seems a marginal gain, at the cost of
>   a clear exposition (and is really an Agda-dependent implementation
>   artefact, rather than part of your story about representation within
>   a dependently-typed language)

Well, one benefit is that I do not have to construct any pointwise proofs
in the definition of `forward`.  My thinking was: I am going to use instances
anyway to do syntactical wrappers for the DSL, so maybe I could make the
definitions nicer.  I am happy to take another go and see whether removing
instances adds a lot of proof obligations, but as far as I remember it did.

> * the use of the 3-place pointwise relation type former makes sense,
>   although as it is only used in two cases, I would be tempted simply
>   to inline one use (for addition), and indicate that multiplication
>   is similar
> 
> * similarly, as far as I could tell, you do not at any point exploit
>   the full generality of the `cons` constructor in maintaining the
>   invariant `R m n k`, when in the two uses you make, these could be
>   inlined simply with `k = m + n`/`k = m * n` *definitionally*

I arrived at this definition in attempt to keep my presentation compact.
However, I am happy to try some inlining.

> * moreover: the one use of the 2-place pointwise construction, for the
>   case of the `suc` function, completely obscures, via the relational
>   version `suc p ≈ q`, that in all such uses, any such `q` is
>   *definitionally* equal to `sucₛ p = List.map suc p`, and as such, would
>   considerably simplify the types of functions which make use of a
>   combination of this and the `p + q ≈ r` invariant (see below)

`suc` is kept as equation on purpose because I literally translate these
combinators into constructors of `E`.  It is helpful when we keep as
little computations in type indices as possible.  This is not so relevant
for the definitions within Agda, but I thought this consistency makes
it easier for the readers to grasp constructors of E.

> p.6
> The "little plumbing" required for rank-safe 'subtraction' is
> considerably simplified if you only require a `Maybe` option type to
> be returned (see above)!

I agree, but I would use the same argument here --- `Maybe` does not prevent
me from saying `nothing` where there is actually something.
 
> The types of `slide` and `backslide` I found to be very difficult to
> read, combining as they do, in two different argument orders, appeal
> to both the `p + q ≈ r` and `suc p ≈ q` invariants. Moreover, here, as
> later with `conv` and `mconv`, there is an explicit mention of the
> function space arrow `P s → ...` when it seems as though this should
> simply be folded into the type, given the central `Ar s X`
> abstraction, namely to give the following types to the operations:
> 
> slide     : p +ₛ q ≈ r → Ar r A → Ar p (Ar (sucₛ q) A)
> backslide : p +ₛ q ≈ r → A → Ar (sucₛ q) A → Ar p (Ar r A)
> conv      : p +ₛ q ≈ r → Arr r R → Arr p R → Arr (sucₛ q) R
> mconv     : p +ₛ q ≈ r → Arr r R → Arr s R → Arr s (Arr p R) → Arr s (Arr (sucₛ q) R)
> 
> (systematically identifying `Arr s (Arr p X)` with `Arr (s ⊗ p) X` via
> the `nest`/`unnest` isomorphisms)

Your definitions do look nice, but as I was saying, I was trying to keep
computations out of array indices.  I'd have to think whether there is
a good way to introduce something like `sucₛ` that expands to a point-wise
equation and the array.

> NB. the `conv` and `mconv` constructions are moreover generic in any
> particular (semi)ring structure on `R`, so that `conv₁` can (should?)
> be seen in terms of the semiring instance for `R = ℕ` etc.

Yes, this is true, I am happy to mention this, but I didn't want to add
extra level of abstraction, parametrising the entire construction by a
semiring.  I can certainly mention this in the text or in the footnote.
 
> p.7
> The "running example" finally makes an appearance, but without ever
> having been explicitly mentioned (nor the role that the `forward`
> function plays in its development/implementation)... some more words
> earlier, and here, would help make that bridge.

Sure, happy to expand.

> The definition of `forward` is given in terms of Agda's `let`
> construct, when it might be smoother simply to give a definition using
> `where` clauses, not least because Agda's `let` actually gives rise to
> inlined substitution in the typechecked code, and thus potentially a
> loss of sharing upfront.

One reason why I used `let` instead of `where` is because it rhymes
better with the definition of `cnn` in line 670.  Also, we are not too
interested in performance of shallowly-embedded `forward` here, and this
is something that I am happy to mention.

> Section 4 The embedded DSL
> 
> p.8
> 
> While this now might be regarded as 'standard', or 'folklore', the use
> of dependent types to ensure type- and scope- safe embedding of DSLs
> into Agda ought to have associated citation(s); anticipating 4.3, the
> ICFP/JFP papers of Allais et al. could/should be cited here.

Sure, happy to add this.

> The introduction of `unit` as a synonym for shape `[]` seems
> excessive, and pointless, here, compared to other approaches sketched
> above for dealing with scalar types as an instance of the fundamental
> `Ar` type.

While I agree with your observation that `Ar [] X` can be defined as
`X` in case of shallow embedding, in case of deep embedding it does
not seem that elegant.  Note that the types used in `E` distinguish
between arrays and indices of some shape, yet they do not have a notion of a base
type (scalar).  It is a typical trick of array languages which has some
beauty in it: all we have is `ar s` and `ix s` where `s` is a shape.
Things are defined rank-polymorphically: e.g. binary operations accept
arrays of any matching shape (including scalars); `sum` operates on
arrays of arrays and scalars, etc.  If we were to add more distinct
cases in the definition of `IS`, we'd probably have to add even more
constructors, maybe fix a type of reals (or add add it as a parameter),
or index with something larger than `IS`.  Given that we want to define
generic constructs in `E` that abstract over shapes `s` and `p` it is not
obvious to me which type encoding is the best.

> Similarly, why postpone the introduction of syntax for `bin plus` and
> `bin mul` to p.9 ll.423--4, when they would make more sense to be
> introduced when the `Bop` type is introduced? Better still, why waste
> a `pattern` synonym, when you could write smart constructors to build
> in optimisation for the cases of addition of 0, or multiplication by
> 1, which you both allude to (indirectly) later, and which make use of
> these units being part of the *syntax* of the language (and hence
> matchable on, IIUC?)

I agree, we used to have more primitive operations, but we got rid of them
for the sake of brevity.  We can surely inline these now.

> p.9
> 
> The definition of `data E` would surely look better (at the cost of
> some space, perhaps?) as a Figure, rather than inlined?

Sure, I can do this.

> Similar remarks apply here to the types of the DSL analogues of
> `slide`, `backslide` etc. wrt the use of the complex shape invariants

The same answer as before applies :)

> It seems a shame that you can't/don't permit a type structure for `E`
> which supports the `nest`/`unnest` isomorphisms. Perhaps this is now an
> artefact of extraction towards Futhark, but if so, this merits a bit
> more discussion, esp. given that you subsequently consider
> 'normalisation' of `E` programs before extraction, so that you might
> (and the reader, this one included) consider a richer DSL type
> structure, with restrictions to 'Futhark-conformant' types a later
> phase in the extraction pipeline.

I look at this as `nest/unnest` is now accessed through `imap` (and not
`imaps`).  In the shallow embedding you would write something like
`unnest λ i → f (nest a i)` whereas now you (conceptually) write
`imap f a`.  This doesn't have much to do with Futhark extraction,
as I could turn both nested arrays and arrays of product shapes into
Futhark expressions as long as ranks are static.  After all, nest/unnest
isomorphism establishes that there is no difference between nested
arrays and arrays of product shapes, so we simply chose to add one
representation in the types of our DSL.  I am more than happy to add
this discussion in the text.

 
> p.10
> 
> The specifics of the axiomatisation of a `Real` type, with suitable
> primitives, and their derivatives, seems something which doesn't
> require this level of detail; or rather, it's a level of detail which
> could be more economically explained in terms of standard library
> constructs such as `Ring` or `Semiring`, extended with `logistic`/RelU
> as an abstract operation... together with its derivative, rather than
> having to litigate the sharing problems associated with its concrete
> definition?

Sure, but doesn't relying on stdlib excludes the readers that are not familiar
with it?  That was my motivation to inline the definitions.  I am happy
to include generalised explanation into the text.

> In particular, the choice of a unary minus, without a companion
> definition of binary subtraction, seems to generate unnecessary
> clutter downstream. Similarly, an explicit `fromℕ` operation, used
> only at values 0 and 1, rather than the (obvious) additive and
> multiplicative units from an ambient `(Semi)Ring` structure, etc.

I agree with the general comment.  My idea was to define the smallest
set of operations on Reals that suffice for giving an interpretation of E.
As for unary minus, it is just a way to introduce subtraction, as
`a - b` = `a + (-b)`.  The `fromℕ` is also used in `scaledown` which we
actually use a few times in the resulting definition of the cnn.  I am
happy to explain this in the text using the language of Rings/Fields.

> p.11--14, Sections 4.2, 4.3
> 
> This seems to be an extended exposition of 'standard' (cf. Allais et
> al. above) constructions associated with de Bruijn representations of
> binding, but dressed up so that the nature of the Kripke function
> space semantics for binding forms is made more obscure than necessary:
> the Kripke idea of quantifying over context extensions in order to
> give semantics to object-level functions/`let`-bindings in terms of
> meta-level functions is at the heart of the Allais et
> al. papers... and goes much further back in the literature on the
> metamathematics of (representations of) binding. I would dearly love
> to see in particular 4.3 rewritten so as to make these ideas easier to
> grasp for the non-expert. As they stand, they're fine but
> incomprehensible (sic).

I am happy to have another go at this section and refer to Kripke.
Perhaps I was a bit overprotective while writing the prose as I am often
criticised for introducing too much theoretical constructions that can
be avoided.  For these particular sections, I was simply trying to
show enough definitions so that further constructions are not ambiguous.
I will try to find a good balance in the new description.

> p.14
> The definition of `sqerr` in particular is rendered much harder to
> read than necessary by poor choice of primitives (as above).

Sure, I can introduce smart constructors to make it more readable.

> The definition of `cnn`, much as `forward` before it, uses the new
> 'syntactic' (Agda-/meta-level) representations of E-/object-level
> `let` binders... but it might be useful to offer a side-by-side
> comparison with the deBruijn version, if only for the reader to
> appreciate all the work that has gone into 4.3?

I thought about it, but decided against it as I thought it would drive
too much attention to the syntactic wrappers.  However, after reading
the reviews, I actually think that emphasising that wrappers are useful
might be a good idea.  I am happy to have a go at this.
 
> p.15--19 AD for E
> 
> Much of this material seems standard by way of describing
> (reverse-mode) AD in terms of straight-line programs defining
> successive partial derivatives in terms of their primals, until the
> mechanics of implementing this on top of `E` is described.
> 
> Surprisingly, on p.17 and the definition of the various auxiliary
> functions as well as the main definition of $\nabla$ (ll.800--825), no
> mention is made of:
> 
> * l.792 that the 'seed' of reverse-mode AD is given by the $\delta$
>   parameter IIUC; so tell the reader!

We have to be really careful with terminology here.  The seed in terms
of reverse mode AD is given by `s` (stands for `s`eed).  Now, $\delta$
is the state of the environment (gradient, -isch) that we are updating.
We have to call `∇` with some initial value of the environment (zero
for all positions).  I am happy to rewrite this sentence.

> * l.823 the use of the HOAS syntax for `let` in the definition of the
>   derivative of `logistic`, so here we do see the full horror of the
>   de Bruijn calculation

Sure, I can mention this.

> * nor anywhere the idea of 'gradient' per se (nor what its meta- nor
>   object- level type might be)

Sure, I am happy to explain what that is.

> p.19 Section 5.2
> 
> No explicit link is made between the axiomatisation of units for
> addition and multiplication, and the corresponding semantic
> equivalence between 'smart' constructors for addition and
> multiplication and their vanilla counterparts?

Happy to make this explicit.

> p.20
> 
> There is some discussion of how to optimise (or rather: how to avoid
> pessimising) sharing in `let` expressions and their derivatives. The
> paper does not have a lot to say here, but NB citation [34] contains
> extensive discussion of this problem.

Thanks, I can make the link more explicit in the discussion.

> p.21
> 
> Codegen via `String`, IIUC. Perhaps that is the best one can do, but
> it seems as though an Agda-internal DSL for 'Futhark' (scare quotes to
> distinguish for actual Futhark) could be distinguished from `E`
> (esp. wrt higher-rank computations?), so that the questions about
> normalisation of `E` programs into 'Futhark' could be pursued as
> future work?

Absolutely, see our original rebuttal response to this.  In the ideal
world we would introduce embedding of Futhark in Agda, semantics for it,
and prove that our normalisation/compilation is semantics-preserving.
This is very obvious future work, but it is not on a critical path
in the following sense: Futhark's semantics is somewhat similar to Agda
and the entire normalisation/extraction takes about 50 lines of code.
Therefore, given that we can compile and run extracted programs, the
chances of mistakes in the translation process is relatively small.
Once again, by no means we claim that this shouldn't be done, we
simply didn't have enough resources to do this in this iteration.

> p.22--23 Section 6
> "One of the goals of this work"
> It would have been helpful to have posted this research question
> upfront in such a way that it would not get lost during the main
> thrust of the paper, concerning the Agda/E/Futhark pipeline.

Sure, happy to stress it more.

> What can we really learn from the performance study? It seems to be
> the conclusion that this pipeline approach is morally good enough,
> without really being clear about where future sources of
> improvement/optimisation might come from. This reader is happily
> convinced by the prehistory of FP that while implementations may be
> slow(er) now, they will improve, but lurking behind the scenes is
> a different problem: namely that of scale wrt number of dimensions/size
> of rank of the tensor calculations involved. In principle, with a
> rank-polymorphic and rank-safe language, such considerations are
> somehow outside the discussion, but when comparing with TensorFlow or
> PyTorch, this is where the sharp distinctions will be observed? I'm
> sure it's out-of-scope for this paper, but some words in this direction
> might have been... helpful to the authors' cause.

Sure, happy to expand on this.

> There is also a separate, unanalysed, question: why extract to Futhark?
> How hard would it be to have a different pipeline/backend, targeting
> PyTorch or TensorFlow directly? What would be involved? how would the
> claimed advantages deriving from rank-polymorphic, rank-safe languages
> in Agda give rise to 'better' back-end computations on other
> platforms? It would be very interesting to know!

Yes, we should say a bit more than what we said in lines 1114-1115,
happy to expand on this.

> p.23--25 Section 7
> Mention Abbott et al.
> Mention Allais et al.

Happy to do this!


> Nevertheless, despite all of the above detailed criticisms, I think
> they can all (mostly!?) be dealt with in such a way as to make a good
> paper much better!

Thank you so much for all your effort, this is enormously helpful!




