---
layout: default
title: "Checks: A complete calculus for the \u2112-general models of the ontological argument"
---

# Checks: [A complete calculus for the ℒ-general models of the ontological argument]({{ "/findings/ontological-lgeneral-semantics.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the independent reproofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-lgeneral-semantics/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
