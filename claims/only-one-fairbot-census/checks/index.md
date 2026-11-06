---
layout: default
title: "Checks: Unexploitable modal agents that cooperate with themselves: a census"
---

# Checks: [Unexploitable modal agents that cooperate with themselves: a census]({{ "/findings/only-one-fairbot-census.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the independent reproofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/only-one-fairbot-census/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
