---
layout: default
title: "Checks: An unexploitable modal agent that defects against itself"
---

# Checks: [An unexploitable modal agent that defects against itself]({{ "/findings/wn-gate-family.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/wn-gate-family/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/wn-gate-family/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
