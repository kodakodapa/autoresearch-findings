---
layout: default
title: "Checks: How large must a program be to tell graded FairBots apart?"
---

# Checks: [How large must a program be to tell graded FairBots apart?]({{ "/findings/graded-fairbot-separators.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds; `reproofs/` holds the second-agent re-proofs with their recorded results.

{% for f in site.static_files %}{% if f.path contains "/claims/graded-fairbot-separators/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
