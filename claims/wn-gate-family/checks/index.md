---
layout: default
title: "Checks: An unexploitable modal agent that defects against itself"
---

# Checks: [An unexploitable modal agent that defects against itself]({{ "/findings/wn-gate-family.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the independent reproofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/wn-gate-family/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
