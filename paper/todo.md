List of minor remarks suggested by reviewers. Remove the ones that have been done or resolved

## A

WON'T FIX THIS, WE ELABORATE LATER
l5: "strong correctness guarantees" -- like/namely?

l329-342: very nice

WON'T FIX THIS
l401: "imaps" -- isn't this normally called build or generate. Why stray from that? 
l402:  "sels" -- isn't this just indexing? why not call it that?

NOTHING TO FIX HERE
l554-694: Interesting! I didn't know this technique. Is this a novel contribution? If so, maybe list it in the intro?

DON'T UNDERSTAND, IT IS EXPLAINED ABOVE
l786-791: please explain a bit more here.

MAYBE
l797-830: What is the complexity of the resulting algorithm? Is it as expected from reverse AD?

WON'T FIX, THIS IS USED FOR CONVOLUTION, BUT IT IS NOT AN IMPORTANT POINT
l1197: "certain functions being inverses" -- where do you use this?

## C

NOTHING TO FIX
 - 101: I can see why given the code things work out as they do, but this seems like an artifact of
   how the indexing is set up: the smallest representable array is 1 by 1, not 0 by 0... Presumably
   this is fine, because we do not need something like this, but is this really the standard
   indexing convention in machine learning?

NOTHING TO FIX
 - 112: As a small side, zipWith should come from a more primitive operation which witnesses
   `Ar s (X × Y) ≅ Ar s X × Arr s Y` (so this is pointed cartesian functor), but this is neither
   this is a matter of aesthetics :)

WON'T FIX THIS
 - 465: I'm surprised that passing the environment as an instance argument is a safe idea here:
   could Agda not always update in the future to make this code just pass the empty environment
   instead?


## D

CHECK 
- l50ff "follow [36]" here and everywhere: do not use citations as nouns

NOTHING TO FIX
- l136 Is there a reason to use `ι n` instead of the standard `[ n ]` for the singleton `n`?

WON'T FIX THIS
- l295ff A picture would help in the visualization of block formation (for low dimensions).


- l419 why does `scaledown` take an `ℕ` and not an `ℝ`?

## E

Changelog in a separate file.
