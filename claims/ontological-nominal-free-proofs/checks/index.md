---
layout: default
title: "Checks: Nominal-free proofs of the theorems Benzm\u00fcller's detector flags"
---

# Checks: [Nominal-free proofs of the theorems Benzmüller's detector flags]({{ "/findings/ontological-nominal-free-proofs.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/ontological-nominal-free-proofs/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-nominal-free-proofs/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
