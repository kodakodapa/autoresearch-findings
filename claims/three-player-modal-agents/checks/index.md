---
layout: default
title: "Checks: Three-player modal agents in a public-goods game"
---

# Checks: [Three-player modal agents in a public-goods game]({{ "/findings/three-player-modal-agents.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the second-agent re-proofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/three-player-modal-agents/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
