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

 
> WON'T FIX
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



> WON'T FIX
> * why define the Positions type family `P` directly as a `data` type
>   definition, rather than as a definition by recursion on `S`, as an
>   iterated product type?

You can pattern-match on indices directly, which sometimes look nicer.
Otherwise there isn't much difference.

> PARTIALLY FIXED (explained)
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

WON'T FIX THIS 
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


FIXED 
> p.7
> The "running example" finally makes an appearance, but without ever
> having been explicitly mentioned (nor the role that the `forward`
> function plays in its development/implementation)... some more words
> earlier, and here, would help make that bridge.

Sure, happy to expand.

FIXED
> Section 4 The embedded DSL
> 
> p.8
> 
> While this now might be regarded as 'standard', or 'folklore', the use
> of dependent types to ensure type- and scope- safe embedding of DSLs
> into Agda ought to have associated citation(s); anticipating 4.3, the
> ICFP/JFP papers of Allais et al. could/should be cited here.

Sure, happy to add this.


WILL DO LATER
> p.9
> 
> The definition of `data E` would surely look better (at the cost of
> some space, perhaps?) as a Figure, rather than inlined?

Sure, I can do this.

WON'T FIX THIS
> Similar remarks apply here to the types of the DSL analogues of
> `slide`, `backslide` etc. wrt the use of the complex shape invariants

The same answer as before applies :)


MAYBE LATER
> The definition of `cnn`, much as `forward` before it, uses the new
> 'syntactic' (Agda-/meta-level) representations of E-/object-level
> `let` binders... but it might be useful to offer a side-by-side
> comparison with the deBruijn version, if only for the reader to
> appreciate all the work that has gone into 4.3?

I thought about it, but decided against it as I thought it would drive
too much attention to the syntactic wrappers.  However, after reading
the reviews, I actually think that emphasising that wrappers are useful
might be a good idea.  I am happy to have a go at this.
 

NOTHING TO FIX HERE
> p.15--19 AD for E
> 
> Much of this material seems standard by way of describing
> (reverse-mode) AD in terms of straight-line programs defining
> successive partial derivatives in terms of their primals, until the
> mechanics of implementing this on top of `E` is described.







STILL TODO

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




