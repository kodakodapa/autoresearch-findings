---
layout: default
title: "Checks: G\u00f6del's lemma L under the rigid reading, with no condition on positivity"
---

# Checks: [Gödel's lemma L under the rigid reading, with no condition on positivity]({{ "/findings/ontological-rigid-l.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/ontological-rigid-l/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-rigid-l/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
