---
layout: default
title: "Interval-certified bounds on the area of the Mandelbrot set"
scholar: {"citation_title": "Interval-certified bounds on the area of the Mandelbrot set", "citation_author": "Lindheim, Bj\u00f6rn", "citation_publication_date": "2026/11/11", "citation_abstract_html_url": "https://kodakodapa.github.io/autoresearch-findings/papers/mandelbrot-area-certified-bounds.html", "citation_pdf_url": "https://kodakodapa.github.io/autoresearch-findings/papers/mandelbrot-area-certified-bounds/paper.pdf", "citation_doi": "10.5281/zenodo.24116751"}
---

# {% raw %}Interval-certified bounds on the area of the Mandelbrot set{% endraw %}

Lindheim, Björn · 2026-11-11 · version 2

Cite as: https://doi.org/10.5281/zenodo.24116750 (all versions; this version: https://doi.org/10.5281/zenodo.24116751)

## Abstract

{% raw %}
Using ball-arithmetic certificates checked by separately implemented verifiers, we establish $1.5064820 \le \mu(M) \le 6880083171681/2^{42} < 1.5643498$ for the area of the Mandelbrot set. The upper bound comes from a certified depth-17 dyadic quadtree (escape and a Koebe-type distance estimate with explicit truncation bounds); it is below Fisher and Hill's 1993 bound and the certified upper bounds we found, but above Förstemann's uncertified 1.53121. The lower bound sums certified area-theorem lower bounds over 3,352,592 hyperbolic components of periods 3 to 504 plus the exact period-1 and period-2 components; a stronger ball-arithmetic lower bound, above 1.50651, was published in October 2026 by the same method. Version 2: revised after an independent review; certificates and checkers are deposited separately.
{% endraw %}

- [PDF]({{ "/papers/mandelbrot-area-certified-bounds/paper.pdf" | relative_url }})
- [Manifest]({{ "/papers/mandelbrot-area-certified-bounds/manifest.json" | relative_url }}) (files with their sha256)

## Sources

- [main.tex]({{ "/papers/mandelbrot-area-certified-bounds/source/main.tex" | relative_url }})
- [refs.bib]({{ "/papers/mandelbrot-area-certified-bounds/source/refs.bib" | relative_url }})

## Revisions

- 2026-11-11 (version 2): {% raw %}Independent review: withdraw the lower-bound record claim (stronger 2026 bound found), correct counts and coefficient description, add proofs, checkpoint warning and data DOI{% endraw %}
