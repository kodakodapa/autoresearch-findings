---
layout: default
title: "Checks: Families of unexploitable agents that defect against themselves"
---

# Checks: [Families of unexploitable agents that defect against themselves]({{ "/findings/gate-families.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds. The [manifest]({{ "/claims/gate-families/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/gate-families/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
