---
layout: default
title: "Checks: Round robins of modal agents in the Stag Hunt"
---

# Checks: [Round robins of modal agents in the Stag Hunt]({{ "/findings/staghunt-round-robin.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/staghunt-round-robin/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/staghunt-round-robin/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
