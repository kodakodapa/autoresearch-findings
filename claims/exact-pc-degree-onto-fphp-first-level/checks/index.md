---
layout: default
title: "Checks: Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p"
---

# Checks: [Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p]({{ "/findings/exact-pc-degree-onto-fphp-first-level.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/exact-pc-degree-onto-fphp-first-level/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/exact-pc-degree-onto-fphp-first-level/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
