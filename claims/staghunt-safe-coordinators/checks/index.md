---
layout: default
title: "Checks: Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum"
---

# Checks: [Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum]({{ "/findings/staghunt-safe-coordinators.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds. The [manifest]({{ "/claims/staghunt-safe-coordinators/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/staghunt-safe-coordinators/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
