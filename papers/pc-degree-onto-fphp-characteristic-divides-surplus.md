---
layout: default
title: "Polynomial calculus degree of the onto functional pigeonhole principle when the characteristic divides the surplus"
scholar: {"citation_title": "Polynomial calculus degree of the onto functional pigeonhole principle when the characteristic divides the surplus", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/09", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/papers/pc-degree-onto-fphp-characteristic-divides-surplus.html", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/papers/pc-degree-onto-fphp-characteristic-divides-surplus/paper.pdf", "citation_doi": "10.5281/zenodo.24085724"}
---

# {% raw %}Polynomial calculus degree of the onto functional pigeonhole principle when the characteristic divides the surplus{% endraw %}

Lindheim, Björn · 2026-11-09 · version 1

Cite as: https://doi.org/10.5281/zenodo.24085723 (all versions; this version: https://doi.org/10.5281/zenodo.24085724)

## Abstract

{% raw %}
The onto functional pigeonhole principle with $n+k$ pigeons and $n$ holes has a polynomial
calculus refutation of degree $1$ over $\mathbb F\_p$ when $p\nmid k$, and one of degree
$p^{v\_p(k)}$ in general, by a criterion of Riis.  We study the lower bound when $p$ divides
$k$.  In Lean~4 we prove that the degree is exactly $p$ when $p$ divides $k$ exactly once
($n\ge2p-3$), at least $p+1$ when $p^2$ divides $k$ ($n\ge2p-1$), and at least $5$ for $p=2$,
$k=8$ ($n\ge7$).  With written proofs that rest on named published theorems and have been
checked by AI reviewers but not by people, we show that the degree is exactly $p^{v\_p(k)}$
for $n\ge2p^{v\_p(k)}-1$, so that for surplus $p^\ell$ it grows as $p^\ell$; we give two
further mechanisms, one through Nullstellensatz designs (degree at least $2^\ell$ with
explicit thresholds) and one degree by degree (exact degree $p^2$ when $v\_p(k)=2$); and we
record five errata in two of the sources these proofs use, among them a gap in the published
proof of a theorem we would otherwise have used.  Every statement carries its
evidence tier.  All results were produced by AI research agents under the author's direction.
{% endraw %}

- [PDF]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/paper.pdf" | relative_url }})
- [Manifest]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/manifest.json" | relative_url }}) (files with their sha256)

## Sources

- [appA-tilting.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/appA-tilting.tex" | relative_url }})
- [main.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/main.tex" | relative_url }})
- [refs.bib]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/refs.bib" | relative_url }})
- [sec1-introduction.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec1-introduction.tex" | relative_url }})
- [sec2-definitions.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec2-definitions.tex" | relative_url }})
- [sec3-lean-results.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec3-lean-results.tex" | relative_url }})
- [sec4-growth.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec4-growth.tex" | relative_url }})
- [sec5-periodicity.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec5-periodicity.tex" | relative_url }})
- [sec6-bands.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec6-bands.tex" | relative_url }})
- [sec7-errata.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec7-errata.tex" | relative_url }})
- [sec8-10-tail.tex]({{ "/papers/pc-degree-onto-fphp-characteristic-divides-surplus/source/sec8-10-tail.tex" | relative_url }})

## Related findings

- [{% raw %}Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p{% endraw %}]({{ "/findings/exact-pc-degree-onto-fphp-first-level.html" | relative_url }})
- [{% raw %}Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared{% endraw %}]({{ "/findings/pc-degree-above-p-onto-fphp-surplus-p-squared.html" | relative_url }})
- [{% raw %}Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8{% endraw %}]({{ "/findings/pc-degree-5-onto-fphp-surplus-8.html" | relative_url }})
- [{% raw %}Polynomial calculus degree above 4 over F3 for the onto functional pigeonhole principle with surplus divisible by 9, conditional on a spanning statement{% endraw %}]({{ "/findings/conditional-pc-degree-four-onto-fphp-surplus-9.html" | relative_url }})
