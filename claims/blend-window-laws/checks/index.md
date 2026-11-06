---
layout: default
title: "Checks: Blending self-defecting modal agents with FairBot: exact laws"
---

# Checks: [Blending self-defecting modal agents with FairBot: exact laws]({{ "/findings/blend-window-laws.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the second-agent re-proofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/blend-window-laws/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
