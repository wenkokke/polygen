<!-- Introduction -->

Nearly a decade ago, I was developing the type theory for a small linearly-typed programming language and hoped to test it using QuickCheck [@ClaessenH2000] before committing to a mechanised proof.
I was quickly told that generating simply-typed or even untyped λ-calculus terms is no small feat.
Eventually, during a visit to Sweden, Koen Claessen pointed me to Jonas Duregård's `lazy-search` package [@Duregard2016:lazy-search].
I wrote a very simple type checker for my programming language in Haskell, passed it to `lazy-search`, and it just... churned away, quickly producing well-typed terms.
Did you know there are 26,982,292 simply-typed λ-terms with 30 or fewer constructors?
It takes my machine about a minute to list them all.
I never looked back.

My motivation for writing this paper is twofold.

<!--
Folks kindly pointed me to PLT Redex [@FelleisenFF2009].
Unfortunately, its support for term generation and substructural type systems were not sufficient to for my programming language.
-->
