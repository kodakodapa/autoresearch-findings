---
layout: default
title: "Checks: From Lean proofs to certified derivations in the ontological embedding"
---

# Checks: [From Lean proofs to certified derivations in the ontological embedding]({{ "/findings/ontological-proof-translation.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/ontological-proof-translation/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-proof-translation/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
