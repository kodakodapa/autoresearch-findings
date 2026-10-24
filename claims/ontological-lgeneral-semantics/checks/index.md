---
layout: default
title: "Checks: A complete calculus for the \u2112-general models of the ontological argument"
---

# Checks: [A complete calculus for the ℒ-general models of the ontological argument]({{ "/findings/ontological-lgeneral-semantics.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/ontological-lgeneral-semantics/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/ontological-lgeneral-semantics/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
