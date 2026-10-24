---
layout: default
title: "Checks: A certified map of variants of G\u00f6del's ontological argument"
---

# Checks: [A certified map of variants of Gödel's ontological argument]({{ "/findings/ontological-variant-map.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/ontological-variant-map/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-variant-map/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
