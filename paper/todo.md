List of minor remarks suggested by reviewers. Remove the ones that have been done or resolved

## A

l5: "strong correctness guarantees" -- like/namely?

l80: "distinguishes it from most existing approaches" -- Sure, but there are also several rank polymorphic DSLs/libaries already, like Accelerate. Maybe mention them somewhere?

l102: say somewhere that S is simply a list of natural numbers

l102: It would be helpful to say here what the intended semantics of Ar [n1, ..., nk] is, i.e. R^{n1 x ... x nk} = R^{n1} (x) ... (x) R^{nk}.

l111: maybe note that you can define n-ary zipWith's even.

l119: corresponds

l136: why call this a sum rather than a fold? this is particularly confusing as later sum is just a sum.

l136: "pattern" -- quickly recall pattern syntax for readers less familiar with Agda

l160: "Dec" -- Just give the definition! It is not that hard and your current description is not enough to understand what it does.

l160: "\exists" -- Explain. Contrast with "\Sigma". Does the choice matter here?

l172-l180:  This is currently super unclear and should probably be rewritten.

l204: for

l204-205: It is unclear to me what the alternative is.

l220: ternary

l224: Explain instance argument syntax {{}} here.

l220-225: Say in prose what these relations do/capture.

l235: Remind readers of Agda's notation for identity types.

l258: Equations relating slide and backslide?

l297: "the local neighbourhood"

l298: rephrase sentence. grammar does not work.

l299: blocked selections "selb"

l329-342: very nice

l375: "use non-trivial dependencies within constructors" -- Please explain.

l401: "imaps" -- isn't this normally called build or generate. Why stray from that? 

l402:  "sels" -- isn't this just indexing? why not call it that?

l401-402: say in words what imap(s/b) and sel(s/b) are supposed to do.

l411: explain how zero-but gives a conditional.

l429: that we call imaps 

l433: equality.

l494: verb missing

l501-552: isn't this all standard? is the only point to introduce your notation?

l554-694: Interesting! I didn't know this technique. Is this a novel contribution? If so, maybe list it in the intro?

l702-735: Why so much white space? This seems like a perfect place to insert some diagrams/graphs!

l714-718: "inside-out....outside-in" -- This is quite vague and does not help the reader understand the difference between forward and reverse mode.

l716: reverse mode

l719: we can compute partial derivatives with respect to all of the inputs

l729: "computational graph" -- what is that? it comes out of nowhere here!

l786-791: please explain a bit more here.

l797-830: What is the complexity of the resulting algorithm? Is it as expected from reverse AD?

l925: is this how you fix expensive one-hot arrays?

l942-944: :-(

l1079: What about even larger datasets?

l1122: You may want to include some comparisons here to
de Vilhena, Paulo Emílio, and François Pottier. "Verifying an Effect-Handler-Based Define-By-Run Reverse-Mode AD Library." Logical Methods in Computer Science 19 (2023).
Paszke, Adam, et al. "Getting to the point: index sets and parallelism-preserving autodiff for pointful array programming." Proceedings of the ACM on Programming Languages 5.ICFP (2021): 1-29.
Smeding, Tom J., and Matthijs IL Vákár. "Efficient CHAD." Proceedings of the ACM on Programming Languages 8.POPL (2024): 1060-1088.
Smeding, Tom, and Matthijs Vákár. "Parallel dual-numbers reverse ad." arXiv preprint arXiv:2207.03418 (2022).

l1145: correctness 

l1171: "Even though our support for.."

l1185-1187: Explain more please. I don't understand the difference.

l1197: "certain functions being inverses" -- where do you use this?

## B


* Line 76, "The work in the rest of the paper is presented in Agda, with which
  we assume some familiarity." I appreciated the comment upfront. The paper
  assumes a fair bit of Agda knowledge even for someone who has used other proof
  assistants and dependently typed programming languages.

* Line 162, "Recall that the type Fin n is a type for natural numbers i that are
  bounded by n (i.e. i < n)." This should come at first use. See Line 104.

* Line 1145, "implementatuion" implementation.

## C

 - 52: "focussing" should be focusing

 - 76: minor stylistic comment: the superscript 1 should be on the period, not the last word in the
   sentence.

 - 86: I'm a little confused, should an array of rank 0 not be simply the trivial vector
   space/module? The space of scalars is dimension 1, not 0 in standard mathematics in my
   experience.

 - 101: I can see why given the code things work out as they do, but this seems like an artifact of
   how the indexing is set up: the smallest representable array is 1 by 1, not 0 by 0... Presumably
   this is fine, because we do not need something like this, but is this really the standard
   indexing convention in machine learning?

 - 112: As a small side, zipWith should come from a more primitive operation which witnesses
   `Ar s (X × Y) ≅ Ar s X × Arr s Y` (so this is pointed cartesian functor), but this is neither
   this is a matter of aesthetics :)

 - 130: this is another "X is just Y" of the highest order, but I suppose one can remark that `nest`
   and `unnest` ensure that `Ar - X` is a monoidal functor from `Shape` to `Type → Type` (with the
   latter monoidal product coming from composition). Hardly the a pressing issue, but I found it
   neat.

 - 136: I think one should briefly explain what "pattern" does in Agda, since this sort of syntax is
   a bit more Agda-specific than what has come before. I think it can be guessed from context, but a
   footnote or just a description of what to search in the Agda docs might be helpful.

 - 218: "that 𝑞 is a point-wise addition of 𝑝 and 𝑞" should be r.

 - 228: Again, this footnote should be on the period.

 - 221: Incidentally, why is this specialized to natural numbers? Surely this works fine for an
   arbitrary type A.

 - 465: I'm surprised that passing the environment as an instance argument is a safe idea here:
   could Agda not always update in the future to make this code just pass the empty environment
   instead?

 - 716: "revers" to "reverse"

 - 720: What is a "computational graph" in this context? Is it the dependency graph of expressions?

 - 725: 𝑤2= 𝑤1𝑤2 has a typo

 - Is the terminology adjoint standard? I've seen "partials" or "1-forms" for these objects.

## D

- l50ff "follow [36]" here and everywhere: do not use citations as nouns

- l99 Maybe add a footnote to the extend that `S ▷ P` is a container (I guess that motivated the letters `S` and `P`).
  However, I agree with your choice to not overload the paper with technical terms that do not help understanding.

- l103 It is worth remarking that an array of dimension 0 (shape `[]`) is a singleton ("skalar").

- l136 Is there a reason to use `ι n` instead of the standard `[ n ]` for the singleton `n`?

- l137ff What is called `sum` is really a `fold`, even if you only use it with addition later.

- l142 Why is the base case not simply `sum {s = []} f ε a = a []`?
  I tried this out with your Agda artifact and it works, one can simplify some proofs.

  An array of zero dimensions is a single scalar.  A combination of all its elements is thus just this one scalar.
  I think your starting point was the `foldr` intuition where the result always in corporates the neutral element,
  but maybe thinking in terms of non-empty folds (`fold1`) is more appropriate here.

- l169 I think the surprise goes away if the second hypothesis is written as $j ≤ n$ rather than $j + 1 < n$.

- l205 "fot" → for

- l216 "that $q$ is a point-wise addition" → that $r$ is ...

- l220 "trenary" → ternary

- l232 "f (g x)" and "f (g x y)" are in the wrong font

- l246 "The implementation[s] of..."  Grammar and missing full stop.

- l295ff A picture would help in the visualization of block formation (for low dimensions).

- l299 "introducing blocked selections" insert `selp` here

- l309 in the type you could have `Ar p (Ar s X)` instead of `P p → Ar s X` which would make it more symmetrical with `imapb`

- l419 why does `scaledown` take an `ℕ` and not an `ℝ`?

- l456 "expressions in E Γ _is_" use parentheses "(E Γ _is_)"

- l696ff This section may offer opportunities for salvaging some space if you are struggling with the page limit:
  it feels things are spaced out much more generously than in the other sections.

- Section 5: There is a drop in quality in the exposition of this section.  It deserves some serious polishing.

- l716 "revers[e] mode"

- l717 Having to juggle with the aliases $y = w₃$ and $x = w₀$ obstructs the pattern.

- l720 What role is served by $f x y$ here?  Why not simply $z = \sin(xy + x)$.

- l720 $sin$ should be $\sin$.

- l724 $w₂ = w₁ w₂$ I guess this should be $w₂ = w₀ w₁$.  The aliases even confuse you.

- l729 ∂y should be ∂z, should it?

- l729 Please state what a "successor in the computational graph is", by example.
       E.g. for $w₂$ is $w₃$ the successor or are these $w₀$ and $w₁$?
       Make sure to include an example with more than one successor!

- l737ff I am totally lost here.  Please provide more calculation steps for each line.
         You got plenty of unused horizontal space here!

- l746 "If we inline all the $\bar{w}ᵢ$ definitions"  Again more steps please.
    If I do this myself, I am left with $\bar{w}₀ = \cos w₃ + (\cos w₃)²·x$ which isn't close to the results you report.

- l1000 This parenthesis never closes.

- l1015 So Futhark code is represented just by a `String`?
        Why don't you model the relevant parts by some abstract syntax?
        Can you even prove something about your normalization function when you juggle with monsters like `String → String` to represent a Futhark context?

## E

These comments are not written as bullet points and need to be considered more
carefully.
