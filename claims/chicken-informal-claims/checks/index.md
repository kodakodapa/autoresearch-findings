---
layout: default
title: "Checks: Settling informal claims about modal agents in Chicken"
---

# Checks: [Settling informal claims about modal agents in Chicken]({{ "/findings/chicken-informal-claims.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/chicken-informal-claims/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/chicken-informal-claims/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
