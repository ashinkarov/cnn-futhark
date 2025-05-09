We thank the reviewers for their comments. Before responding to specific
questions below (which we do not expect reviewers to read fully), we wish to
explain the intent of our paper in a way that we perhaps failed to do in the
paper itself.

Our paper investigates the use of Agda as a practical tool for scientific
programming, covering the span from problem specification using rank
polymorphism, to transformation via AD, to optimisation and code generation. Not
all parts of the whole are equally completely specified. Rank polymorphic
array theory
is the most developed and fully verified part. The AD is performed within a
well-shaped and well-scoped DSL, verifying its termination and absence of bounds and scoping errors.
Transformations that we run prior code generation guarantee semantics preservation.
Code generation implements NBE but does indeed use aptly termed
`String → String` monster.

In an ideal world, all parts would of course come with full formal specifications
and accompanying proof, but in practice some parts remain an entirely separate
(and nontrivial) research effort to verify for functional correctness (such as AD).
Other parts can be handled using known techniques (such as code generation),
but are somewhat time consuming. Despite all this, we wish to show that even in those cases where
resources preclude full verification, Agda can still be used as a practical
tool, with full verification employed where it is deemed desirable and
practical. This is what we mean by the somewhat oblique "correctness invariants
of our choice" in the abstract. Full verification of the entire pipeline is
naturally an important avenue for future work.

We agree that dependent types for index safety trace back to Xi and Pfenning,
and that our AD transformation is hardly state of the art, but our contribution
lies not just in reiterating these known ideas, but in engineering a practical
pipeline: from dependently-typed specifications in Agda to performant code
generation via Futhark, supporting non-trivial array programs and
transformations like AD.

## Answers to specific questions and remarks

### Reviewer A

> - How generally does your "unembedding" technique for HOAS-style wrappers of a deeply embedded DSL work? It works for your examples, but can you give any guarantees about the applicability of the technique? What are its limitations?

The key driver for the technique is the `Prefix` relation that automates checking whether
one context is a prefix of another one using 
instance search.  This bit is solid, and for intrinsically-typed DSLs with de Bruijn
variables, this works very well.  One has to define wrappers for all
the binders within the DSL, but this is straight-forward.

The limitation of all techniques that are based on instance search has
to do with bad complexity of instant search implementation.  When many things
become instances, instance search may have to traverse very large
search spaces (e.g. evaluating a large data structure of a constant
size, and so on).  However, this is a general concern rather than a
practical problem related to DSL wrappers.

> - How does your "unembedding" technique relate to the technique from 
> Atkey, Robert, Sam Lindley, and Jeremy Yallop. "Unembedding domain-specific languages." Proceedings of the 2nd ACM SIGPLAN symposium on Haskell. 2009.

There is quite a significant difference, as the quoted work
creates the actual data structure (`class Hoas`) that specifies constructs
of the untyped language syntax.  Then untyped terms are scope- and type-checked
using instance resolution mechanism, and if all the instances are found, the expression is
turned into unscoped de Bruijn, scoped de Bruijn, or simply-typed de Bruijn
representation.  Our technique never defines a particular HOAS syntax.
Every time we use our wrappers, we conceptually write the term in `E`,
our wrappers simply help us to automate computation of well-typed
de Bruijn indices.  There is no conversion between representations
or type-checking of untyped terms.

> ? Is there any reason not to use this tried and tested technique?

The reason is that in `E` we have non-trivial dependencies in constructors.
Most of the constructors are polymorphic in array shapes, and proofs in `imapb`,
`selb`, etc depend on the shapes bound by the given constructor.  It is unclear
whether the proposed technique can easily handle such cases.  While this
might be the case, the technique does not look very simple to use.  So we
took a conceptually simpler approach, which just automates computation
of offsets within the context.

> - What is the complexity of the code generated by your AD transformation? Does it really deserve to be called reverse AD?

I believe that this is deserved to be called reverse AD, as the algorithm computes
the entire gradient in one pass, sharing sub-expressions via introducing
local bindings on the way.  We never have to instantiate one derivative at a time
as in forward mode.

As for complexity, we implement a book-standard algorithm, yet instead of using
scalar elements, we use bulk operations on arrays. As we represent arrays as
stateless functions, we rely on the optimisations to bring bulk operations to
the expected form. Mainly, we aggressively fuse array updates and we eliminate
sums of `zero-but`s, i.e., to efficiently sum collections of sparse arrays that
each have only a statically known number of nonzero elements. Furthermore, we
rely on Futhark to take care of lowering down a pretty high-level code into a
chosen hardware efficiently. With optimisations and Futhark code generation in
place, we expect asymptotic complexity of the generated code to be $m$ times the
complexity of the original function, given that it takes $n$ arguments and
returns $m$ arguments (for our benchmark, $m=1$).

> - On l899 you say "direct compilation of the AD-generated expressions may be computationally inefficient". What are the main sources of inefficiency? Is there any way to classify them and address them systematically? Are your optimizations guaranteed to fix the problems on any other programs than your one example.

As mentioned above, there are two sources of inefficiency: excessive copying and
`zero-but` representation.  Excessive copying is a known problem in array languages,
and there seem to be no universal solution found so far.  However, the proposed
heuristics (e.g. fusion is controlled by inserting let bindings) gives good practical
results.  As for `zero-but` we could introduce a special operator that updates
array at a certain index.  However, we found that that the current approach has
a certain beauty, as it is based just on array combinators and nothing else.
We did test our optimisations on multiple smaller examples, and we observed
that generated expressions are of the same shape as human-written ones.  In
fact the code generated for our CNN example is very much similar to the one
that we wrote by hands first.  We do not have a formal proof that optimisations
fix all the problems, but as our language is very small, the number of patterns
that we had to consider is relatively small as well. In particular, the absence of
sequential looping inside parallel operations ensure that the sparsity of the adjoint
arrays is known statically.

> - Do you have any reason to believe that your code transformation computes derivatives other than evaluation on your one example?

Yes, as all our differentiation rules are specified in about 20 lines of code
(lines 979-830) it is relatively easy to convince yourself that they are doing
the right thing.  Most of these rules are book-standard differentiation rules
like `(f + g)' = f' + g'`.  The only non-trivial rule is the chain rule, and its
non-triviality has to do with: (i) our well-scoped encoding, and (ii) the fact that
we are sharing derivative of the let binding with its potential uses avoiding
inlining.  Now, ideally we would like to demonstrate that our ∇ is the actually a
linear approximation (derivative).  For this we'd have to introduce a lot of scaffolding
such as real numbers, deltas, jacobians, etc.  With those we'd have to define
correctness criteria for ∇, and it seems that specification of let case is likely
to be as complex as the implementation within ∇.  By no means we are disputing
that this should not be done, we just point out that it is likely that the correctness
specification might be still not convince the reader due to potential complexity.


### Reviewer B

We addressed most of the raised issues in other replies, so we will try not to
repeat ourselves.  However, we would like to address the following weakness:

> - Correctness guarantees are weak -- IIUC, the main correctness guarantee the paper ensures is indexing safety. There are no correctness guarantees for AD (and the authors point out that it is unclear how to specify this), nor are there any for the optimisations done in sections 5.2 and 5.3. Perhaps the optimisation can be shown correct with respect to the unoptimised version?

Firstly, the optimisations *are* shown to be semantics-preserving.  We say
this in the line 902, and you can convince yourself that this is the case
by looking at the type of `opt` which is a pair `e'` (optimised expression)
and the proof that `e'` preserves semantics of the original program.

There is also another important guarantee that is not very often found in
the work on AD --- we implement AD on a well-scoped and well-typed language,
so it is guaranteed by construction that the derivatives are well-scoped
and well-typed (-shaped) as well and AD terminates.  Working on
intrinsically-typed representation is noticeably harder than on a raw
syntax.

As for correctness of AD, as we mentioned above: it takes about 20 lines
of code to define all the AD rules (lines 979-830).  Most of these rules are
book-standard (e.g. `(f + g)' = f' + g'`), the only non-trivial part here is
the chain rule for lets.  It is non-trivial because we are working in intrinsic
encoding and we are sharing derivatives of the bound expression.  The phrase 
that you are quoting "not clear how to specify correctness of derivatives"
is not very good one.  Surely we can specify the notion of a derivative through
limits and deltas.  The point is that all the scaffolding that will be needed
to specify correctness of the let rule most likely will be comparable with the
implementation that we have.  While this would be great to have, this might
not give the best confidence due to envisioned complexity of the specification.


### Reviewer C

#### Improving the benchmarks

The JIT behaviour of industry-standard machine learning tools do pose challenges
for benchmarking, *particularly* when the MNIST benchmark is by modern standards
rather small, so the setup time becomes dominant. This is why we have isolated
it in our measurements. Alternatively, we could inflate the number of training
epochs to inflate the training time, although this is unlikely to actually
improve the training result, and so feels artificial. The purpose of our
experiment is not to provide comprehensive evidence for outperforming
TensorFlow, but to show that the performance of our system seems sufficient to
be useful, and that inefficiencies are not likely due to overheads imposed by
formal verification. More complicated benchmark applications, including
scientific programs outside of machine learning, remain future work.

#### Correctness of translation to Futhark

There are no correctness guarantees in the present work, largely for practical
reasons. Since Futhark's dynamic semantics are quite straightforward and similar
to those of Agda, verification is possible via known techniques, but requires
somewhat tedious modelling Futhark in Agda.  All the compilation to Futhark
takes 50 lines of very straight-forward code, so the chances of making a mistake,
given that the generated code is accepted by the compiler are sufficiently small.
On the other hand, correctness of transformations within the DSL is much more
tedious, as we perform non-trivial rewrites, and we managed to catch a few
incorrect ones due to inability to construct a proof.  Having said that, we
do not dispute the fact that it would be very nice to have verified compilation
in place, this is a clear future work, we are only indicating why we did not
prioritise this task in this work.

### Reviewer D

#### On the artifact

The artifact is indeed not in a portable state, as we did not anticipate
reviewers would desire to run it at this stage in the process (but are certainly
pleasantly surprised!). The reason is that due to the somewhat complex
dependencies (GPUs, Python library infrastructure), Docker is the most
accessible way to package it, but the GPU-equipped system on which we did our
work does not support Docker. This will of course be rectified in case the paper
is accepted.

## Answers to detailed comments 


### Reviewer A

> l5: "strong correctness guarantees" -- like/namely?

We make a list in lines 1197-1199, but we can surely put it here as well.

> l80: "distinguishes it from most existing approaches" -- Sure, but there are also several rank polymorphic DSLs/libaries already, like Accelerate. Maybe mention them somewhere?

Accelerate is mentioned 1168-1169, but we can mention it here as well.
Also, a small subtlety, Accelerate allows only for static ranks as far as I am aware, where as the proposed array theory supports dynamic ranks as well.

> l102: say somewhere that S is simply a list of natural numbers

We say this in line 86.

> l102: It would be helpful to say here what the intended semantics of Ar [n1, ..., nk] is, i.e. R^{n1 x ... x nk} = R^{n1} (x) ... (x) R^{nk}.
> 
> l111: maybe note that you can define n-ary zipWith's even.
> 
> l119: corresponds

Sure, thanks.

> l136: why call this a sum rather than a fold? this is particularly confusing as later sum is just a sum.

My thought process was as follows.  This is not quite `fold` because it does not traverse the unrolling, instead it recurses through the shape (hyperplanes).  However, maybe sum is not the best name, happy to change.

> l136: "pattern" -- quickly recall pattern syntax for readers less familiar with Agda
> 
> l160: "Dec" -- Just give the definition! It is not that hard and your current description is not enough to understand what it does.

Sure, will do.

> l160: "\exists" -- Explain. Contrast with "\Sigma". Does the choice matter here?

They are the same, it is just a shorter syntax.  I am happy to explain this.
 
> l172-l180:  This is currently super unclear and should probably be rewritten.

Ok, I'll have another go at this.

> l204: for

Sure, thanks.

> l204-205: It is unclear to me what the alternative is.

The alternative is to move `sum` inside the `imap` and compute the tile in the input array.

> l220: ternary
> 
> l224: Explain instance argument syntax {{}} here.
> 
> l220-225: Say in prose what these relations do/capture.
> 
> l235: Remind readers of Agda's notation for identity types.

Will do, thanks.

> l258: Equations relating slide and backslide?

Good idea, thanks!

> l297: "the local neighbourhood"
> 
> l298: rephrase sentence. grammar does not work.
> 
> l299: blocked selections "selb"

Thanks, will do.

> l329-342: very nice

Thanks :)

> l375: "use non-trivial dependencies within constructors" -- Please explain.

Will do.  The point is that constructors are polymorphic in shapes and proofs in `imapb`, `selb` depend on these shapes.

> l401: "imaps" -- isn't this normally called build or generate. Why stray from that? 
> l402:  "sels" -- isn't this just indexing? why not call it that?

I am not sure about build/generate.  The intuition here is that the constructor is an index map (maps the value per index) and the destructor `sel`ects a scalar, hence `sels`.  I do not have a strong opinion about these names and happy to change them.
> 
> l401-402: say in words what imap(s/b) and sel(s/b) are supposed to do.
> 
> l411: explain how zero-but gives a conditional.
> 
> l429: that we call imaps 
> 
> l433: equality.
> 
> l494: verb missing

Will do.

> l501-552: isn't this all standard? is the only point to introduce your notation?

It is standard.  However, I was criticised before that when these definitions are omitted it is hard to understand some of the expressions that use weakening, `skip`, etc.  So I thought it would be a good idea to show basic definitions.
 
> l554-694: Interesting! I didn't know this technique. Is this a novel contribution? If so, maybe list it in the intro?

I have seen the basic idea before, but I do not think that this has been applied for an intrinsically-typed language.  Happy to add this to the introduction.
 
> l702-735: Why so much white space? This seems like a perfect place to insert some diagrams/graphs!
> 
> l714-718: "inside-out....outside-in" -- This is quite vague and does not help the reader understand the difference between forward and reverse mode.
> 
> l716: reverse mode
> 
> l719: we can compute partial derivatives with respect to all of the inputs
> 
> l729: "computational graph" -- what is that? it comes out of nowhere here!

You are right, I'd like to redo the beginning of section 5.

> l786-791: please explain a bit more here.

Sure.

> l797-830: What is the complexity of the resulting algorithm? Is it as expected from reverse AD?

I answered this above.

> l925: is this how you fix expensive one-hot arrays?

It is mainly 935-937 that does this.  We took a compromise here by keeping the language simple.  As we need to optimise AD-generated code anyway, we can also try to resolve this problem through rewrite.

> l942-944: :-(

This is surely not ideal, but this is pretty much inevitable state in optimising compilers.
Specifically when languages are high-level, the quality of generated code crucially depends on the set of optimisations and even the order of running them.  Given that people make research careers on applying machine learning to figure the best optimisation strategy, this is still an unsolved problem.
 
> l1079: What about even larger datasets?

The structure of the code is such that there is a fixed-size kernel that runs backpropagation, and the size of input only indicates how many times this kernel will be launched (sequentially).  Therefore, it is very unlikely that bigger input sizes would change the behaviour.  However, we are happy to run a bigger dataset and report the results. 
 
> l1122: You may want to include some comparisons here to
> de Vilhena, Paulo Emílio, and François Pottier. "Verifying an Effect-Handler-Based Define-By-Run Reverse-Mode AD Library." Logical Methods in Computer Science 19 (2023).
> Paszke, Adam, et al. "Getting to the point: index sets and parallelism-preserving autodiff for pointful array programming." Proceedings of the ACM on Programming Languages 5.ICFP (2021): 1-29.
> Smeding, Tom J., and Matthijs IL Vákár. "Efficient CHAD." Proceedings of the ACM on Programming Languages 8.POPL (2024): 1060-1088.
> Smeding, Tom, and Matthijs Vákár. "Parallel dual-numbers reverse ad." arXiv preprint arXiv:2207.03418 (2022).

Thanks, will do.

> l1145: correctness 
> 
> l1171: "Even though our support for.."

Thanks.

> l1185-1187: Explain more please. I don't understand the difference.

Sure, happy to explain more.  In a nutshell, shape annotations in both SaC and Futhark are somewhat like types in Python, you can use them if you want to, but they could be ignored and do not provide guarantees.  Dynamic rank polymorphism means that array ranks are only known at runtime.

> l1197: "certain functions being inverses" -- where do you use this?

Line 160 and 242 mainly to ensure that subtraction is an inverse to addition. 


### Reviewer B

> * Line 76, "The work in the rest of the paper is presented in Agda, with which we assume some familiarity." I appreciated the comment upfront. The paper assumes a fair bit of Agda knowledge even for someone who has used other proof assistants and dependently typed programming languages.

Fair enough, happy to clarify this.

> * Line 162, "Recall that the type Fin n is a type for natural numbers i that are bounded by n (i.e. i < n)." This should come at first use. See Line 104.

Sure, thanks.

> * Line 1145, "implementatuion" implementation.

Thanks.

### Reviewer C

>  - 52: "focussing" should be focusing
>  - 76: minor stylistic comment: the superscript 1 should be on the period, not the last word in the
>    sentence.

Sure, thanks.

>  - 86: I'm a little confused, should an array of rank 0 not be simply the trivial vector
>    space/module? The space of scalars is dimension 1, not 0 in standard mathematics in my
>    experience.

It is a usual approach in array languages and tensor calculus to define rank zero arrays/tensors
to be isomorphic to scalars.  This becomes intuitive if you think about the product of the empty
list, which is typically defined to be 1.  Also, if rank-zero array is always a trivial vector,
for array (a : Ar [] (Ar [2,2] X)), how could `unnest a : Ar [2,2] X` ever produce a result?

For example [this link](https://www.damtp.cam.ac.uk/user/tong/vc/vc7.pdf) says: A tensor of rank 0 is just a
number, or scalar, T . Under a rotation, it doesn’t change: T 0 = T . A tensor of rank 1
is a vector, while a tensor of rank 2 is a matrix.

>  - 101: I can see why given the code things work out as they do, but this seems like an artifact of
>    how the indexing is set up: the smallest representable array is 1 by 1, not 0 by 0... Presumably
>    this is fine, because we do not need something like this, but is this really the standard
>    indexing convention in machine learning?

What do you mean by representable?  Any array that contains zero as one of its shape components
is an empty array, and we have infinitely many of these.  Empty arrays do not contain elements
(product of the shape is zero), but they are valid values, here is an example:
```
  x : Ar (2 ∷ 0 ∷ []) ℕ
  x (i ∷ () ∷ [])  -- absurd pattern indicates that such an index component couldn't possibly exist
```
They can be defined because the index space of an empty array is isomorphic to the empty type,
and we can define a function from the empty type to any other type.  This is entirely standard
treatment of arrays in array languages such as APL, SaC, etc.  I am pretty sure that NumPy
has the same treatment of empty arrays.

>  - 112: As a small side, zipWith should come from a more primitive operation which witnesses
>    `Ar s (X × Y) ≅ Ar s X × Arr s Y` (so this is pointed cartesian functor), but this is neither
>    this is a matter of aesthetics :)

Sure, I agree, but we use `zipWith` in the code and we do not really use the iso.

>  - 130: this is another "X is just Y" of the highest order, but I suppose one can remark that `nest`
>    and `unnest` ensure that `Ar - X` is a monoidal functor from `Shape` to `Type → Type` (with the
>    latter monoidal product coming from composition). Hardly the a pressing issue, but I found it
>    neat.

Sure, happy to remark this.

>  - 136: I think one should briefly explain what "pattern" does in Agda, since this sort of syntax is
>    a bit more Agda-specific than what has come before. I think it can be guessed from context, but a
>    footnote or just a description of what to search in the Agda docs might be helpful.
>  - 218: "that 𝑞 is a point-wise addition of 𝑝 and 𝑞" should be r.

Agreed, thanks for spotting this.

>  - 228: Again, this footnote should be on the period.

Oh, I learned something, thank you!  I was under the impression that footnotes go before punctuation, but I was wrong.

>  - 221: Incidentally, why is this specialized to natural numbers? Surely this works fine for an
>    arbitrary type A.

Sure, then `a`, `b`, `c` has to become `List A`, but they are currently of type `S`.
We only use these relations for shapes, so we didn't generalise it.

>  - 465: I'm surprised that passing the environment as an instance argument is a safe idea here:
>    could Agda not always update in the future to make this code just pass the empty environment
>    instead?

The type of environment is `Env Γ` where `Γ` is a parameter, whereas the empty environment has the type
`Env 𝜖`, so such an instance wouldn't typecheck.  Secondly, the instance search wouldn't do such search, as `Env`
is a function.  Finally, even if it were to find the empty environment that somehow magically fits,
it would (potentially) clash with the instance `𝜌`, and if more than one instance is found it
reports a type error.

>  - 716: "revers" to "reverse"

Thanks.

>  - 720: What is a "computational graph" in this context? Is it the dependency graph of expressions?

Yes.

>  - 725: 𝑤2= 𝑤1𝑤2 has a typo

Yes, indeed, thank you.

>  - Is the terminology adjoint standard? I've seen "partials" or "1-forms" for these objects.

It seem to be pretty standard terminology that is also used on Wikipedia.


### Reviewer D

> Comments for authors
> --------------------
> - l50ff "follow [36]" here and everywhere: do not use citations as nouns

Sure, happy to fix this.
> 
> - l99 Maybe add a footnote to the extend that `S ▷ P` is a container (I guess that motivated the letters `S` and `P`).
>   However, I agree with your choice to not overload the paper with technical terms that do not help understanding.

Happy to add a footnote.

> - l103 It is worth remarking that an array of dimension 0 (shape `[]`) is a singleton ("skalar").

We actually say this in line 86/87: "The `[]` shape describes an array of rank zero that contains exactly one element"

> - l136 Is there a reason to use `ι n` instead of the standard `[ n ]` for the singleton `n`?

Not really, so one could use `[ n ]` instead.

> - l137ff What is called `sum` is really a `fold`, even if you only use it with addition later.

Kind of, except it doesn't fold the unrolling of the array, it folds a hyperplane ar a time, so I am not sure whether the name fold helps here. I am not opposed to changing the name though.

> - l142 Why is the base case not simply `sum {s = []} f ε a = a []`?
>   I tried this out with your Agda artifact and it works, one can simplify some proofs.
>   An array of zero dimensions is a single scalar.  A combination of all its elements is thus just this one scalar.
>   I think your starting point was the `foldr` intuition where the result always in corporates the neutral element,
>   but maybe thinking in terms of non-empty folds (`fold1`) is more appropriate here.

Exactly as you say, if `ε` is neutral to `f` then it doesn't matter.
However, with lists, if you fold a singleton list `fold f e [ x ]` you end up with `f x e` rather than `e`.  As arrays of shape `[]` are singletons, it seems reasonable to do the application of `f`.

> - l169 I think the surprise goes away if the second hypothesis is written as $j ≤ n$ rather than $j + 1 < n$.

My line of thought was: `i : Fin m` translates to `i < m` and `j : Fin (1 + n)` translates to `j < 1 + n` (as I explained in line 163).  Then, for premises `a < b` and `c < d` it feels natural to conclude `a + c < b + d`, which is true, but it is also an overapproximation.  I am happy to add the comment saying that `j < 1 + n` is the same as `j ≤ n`.


> - l205 "fot" → for 
> - l216 "that $q$ is a point-wise addition" → that $r$ is ...
> - l220 "trenary" → ternary
> - l232 "f (g x)" and "f (g x y)" are in the wrong font
> - l246 "The implementation[s] of..."  Grammar and missing full stop.

Sure, thanks for spotting those.

> - l295ff A picture would help in the visualization of block formation (for low dimensions).

We are a bit pressed on space, but I can try to add this.

> - l299 "introducing blocked selections" insert `selp` here

You mean `selb`, sure.

> - l309 in the type you could have `Ar p (Ar s X)` instead of `P p → Ar s X` which would make it more symmetrical with `imapb`

Sure, thanks.

> - l419 why does `scaledown` take an `ℕ` and not an `ℝ`?

For simplicity really.  The definition of `E` keeps the type of reals completely opaque, e.g. it is a base type of the arrays of these shapes which you chose when you interpret the language.  Any real type you chose should allow conversions from natural numbers.  I could parametrise E with `ℝ`, or
use `E Γ unit` as an argument, natural number seemed to be the simplest option.

> - l456 "expressions in E Γ _is_" use parentheses "(E Γ _is_)"

Sure, thanks.

> - l696ff This section may offer opportunities for salvaging some space if you are struggling with the page limit:
>   it feels things are spaced out much more generously than in the other sections.

Yes, you are right, we can compress the list of equations.

> - Section 5: There is a drop in quality in the exposition of this section.  It deserves some serious polishing.

We'd be more than happy to try our best to improve this section.

> - l716 "revers[e] mode"

Sure.

> - l717 Having to juggle with the aliases $y = w₃$ and $x = w₀$ obstructs the pattern.

Fair enough.

> - l720 What role is served by $f x y$ here?  Why not simply $z = \sin(xy + x)$.

Agreed.

> - l720 $sin$ should be $\sin$.

Sure, thanks. 

> - l724 $w₂ = w₁ w₂$ I guess this should be $w₂ = w₀ w₁$.  The aliases even confuse you.
> - l729 ∂y should be ∂z, should it?

Yes to both, and thanks for noticing.
> 
> - l729 Please state what a "successor in the computational graph is", by example.
>        E.g. for $w₂$ is $w₃$ the successor or are these $w₀$ and $w₁$?
>        Make sure to include an example with more than one successor!
> 
> - l737ff I am totally lost here.  Please provide more calculation steps for each line.
>          You got plenty of unused horizontal space here!
> 
> - l746 "If we inline all the $\bar{w}ᵢ$ definitions"  Again more steps please.
>     If I do this myself, I am left with $\bar{w}₀ = \cos w₃ + (\cos w₃)²·x$ which isn't close to the results you report.

I will redo the example providing more intermediate steps.

> - l1000 This parenthesis never closes.

This is a typo, thanks.

> - l1015 So Futhark code is represented just by a `String`?
>         Why don't you model the relevant parts by some abstract syntax?
>         Can you even prove something about your normalization function when you juggle with monsters like `String → String` to represent a Futhark context? 


Yes, you are right, it would be nicer to prove safe translation to Futhark by
defining a model of Futhark, and then relating the interpretation of futhark programs
and evaluation of E.  This does require more work though, and in practice,
code generation seemed to be the least interesting part of the work.
We thought that the proposed way might be a reasonable compromise that gets
us NBE without introducing much scaffolding.

> 
> 
> 
> Artifact: agda
> ==============
> 
> Ar.agda
> -------
> 
> I suppose some functions you define here can also be found in the standard library, e.g.
> 
> - `_++_ = Data.List.Relation.Unary.All.Properties.++⁺`
> - `_∙_ = trans`
> - `inject-left = _↑ˡ_`
> - ...

Sure, I recall that we had troubles when collaborators used different versions of the standard library, so we just replicated some of the functions.  We can clean fix the library version and do a little cleanup.

