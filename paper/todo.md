List of minor remarks suggested by reviewers. Remove the ones that have been done or resolved

## A

l5: "strong correctness guarantees" -- like/namely?

l102: It would be helpful to say here what the intended semantics of Ar [n1, ..., nk] is, i.e. R^{n1 x ... x nk} = R^{n1} (x) ... (x) R^{nk}.

l111: maybe note that you can define n-ary zipWith's even.

l136: "pattern" -- quickly recall pattern syntax for readers less familiar with Agda

l160: "Dec" -- Just give the definition! It is not that hard and your current description is not enough to understand what it does.

l160: "\exists" -- Explain. Contrast with "\Sigma". Does the choice matter here?

l172-l180:  This is currently super unclear and should probably be rewritten.

l224: Explain instance argument syntax {{}} here.

l220-225: Say in prose what these relations do/capture.

l235: Remind readers of Agda's notation for identity types.

l258: Equations relating slide and backslide?

l297: "the local neighbourhood"

l329-342: very nice

l375: "use non-trivial dependencies within constructors" -- Please explain.

l401: "imaps" -- isn't this normally called build or generate. Why stray from that? 

l402:  "sels" -- isn't this just indexing? why not call it that?

l401-402: say in words what imap(s/b) and sel(s/b) are supposed to do.

l411: explain how zero-but gives a conditional.

l501-552: isn't this all standard? is the only point to introduce your notation?

l554-694: Interesting! I didn't know this technique. Is this a novel contribution? If so, maybe list it in the intro?

l786-791: please explain a bit more here.

l797-830: What is the complexity of the resulting algorithm? Is it as expected from reverse AD?

l1122: You may want to include some comparisons here to
de Vilhena, Paulo Emílio, and François Pottier. "Verifying an Effect-Handler-Based Define-By-Run Reverse-Mode AD Library." Logical Methods in Computer Science 19 (2023).
Paszke, Adam, et al. "Getting to the point: index sets and parallelism-preserving autodiff for pointful array programming." Proceedings of the ACM on Programming Languages 5.ICFP (2021): 1-29.
Smeding, Tom J., and Matthijs IL Vákár. "Efficient CHAD." Proceedings of the ACM on Programming Languages 8.POPL (2024): 1060-1088.
Smeding, Tom, and Matthijs Vákár. "Parallel dual-numbers reverse ad." arXiv preprint arXiv:2207.03418 (2022).

l1197: "certain functions being inverses" -- where do you use this?

## C

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

 - 228: Again, this footnote should be on the period.

 - 221: Incidentally, why is this specialized to natural numbers? Surely this works fine for an
   arbitrary type A.

 - 465: I'm surprised that passing the environment as an instance argument is a safe idea here:
   could Agda not always update in the future to make this code just pass the empty environment
   instead?


## D

- l50ff "follow [36]" here and everywhere: do not use citations as nouns

- l99 Maybe add a footnote to the extend that `S ▷ P` is a container (I guess that motivated the letters `S` and `P`).
  However, I agree with your choice to not overload the paper with technical terms that do not help understanding.

- l136 Is there a reason to use `ι n` instead of the standard `[ n ]` for the singleton `n`?

- l169 I think the surprise goes away if the second hypothesis is written as $j ≤ n$ rather than $j + 1 < n$.

- l295ff A picture would help in the visualization of block formation (for low dimensions).

- l419 why does `scaledown` take an `ℕ` and not an `ℝ`?

- l1015 So Futhark code is represented just by a `String`?
        Why don't you model the relevant parts by some abstract syntax?
        Can you even prove something about your normalization function when you juggle with monsters like `String → String` to represent a Futhark context?

## E

These comments are not written as bullet points and need to be considered more
carefully.
