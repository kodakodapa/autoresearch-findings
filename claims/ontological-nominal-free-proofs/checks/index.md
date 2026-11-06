---
layout: default
title: "Checks: Nominal-free proofs of the theorems Benzm\u00fcller's detector flags"
---

# Checks: [Nominal-free proofs of the theorems Benzmüller's detector flags]({{ "/findings/ontological-nominal-free-proofs.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the independent reproofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-nominal-free-proofs/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
