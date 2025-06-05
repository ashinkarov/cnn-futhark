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

