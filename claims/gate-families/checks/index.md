---
layout: default
title: "Checks: Families of unexploitable agents that defect against themselves"
---

# Checks: [Families of unexploitable agents that defect against themselves]({{ "/findings/gate-families.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/gate-families/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/gate-families/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
