---
layout: default
title: "Checks: Blending self-defecting modal agents with FairBot: exact laws"
---

# Checks: [Blending self-defecting modal agents with FairBot: exact laws]({{ "/findings/blend-window-laws.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/blend-window-laws/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/blend-window-laws/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
