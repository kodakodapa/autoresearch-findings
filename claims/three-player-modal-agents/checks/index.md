---
layout: default
title: "Checks: Three-player modal agents in a public-goods game"
---

# Checks: [Three-player modal agents in a public-goods game]({{ "/findings/three-player-modal-agents.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/three-player-modal-agents/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/three-player-modal-agents/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
