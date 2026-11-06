---
layout: default
title: "Checks: A certified map of variants of G\u00f6del's ontological argument"
---

# Checks: [A certified map of variants of Gödel's ontological argument]({{ "/findings/ontological-variant-map.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the independent reproofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-variant-map/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
