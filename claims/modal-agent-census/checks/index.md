---
layout: default
title: "Checks: A census of modal agents in the prisoner's dilemma"
---

# Checks: [A census of modal agents in the prisoner's dilemma]({{ "/findings/modal-agent-census.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/modal-agent-census/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/modal-agent-census/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
