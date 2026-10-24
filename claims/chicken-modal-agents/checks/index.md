---
layout: default
title: "Checks: Modal agents in the game of Chicken"
---

# Checks: [Modal agents in the game of Chicken]({{ "/findings/chicken-modal-agents.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/chicken-modal-agents/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/chicken-modal-agents/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
