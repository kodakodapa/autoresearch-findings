---
layout: default
title: "Checks: From Lean proofs to certified derivations in the ontological embedding"
---

# Checks: [From Lean proofs to certified derivations in the ontological embedding]({{ "/findings/ontological-proof-translation.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the second-agent re-proofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-proof-translation/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
