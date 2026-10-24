---
layout: default
title: "Checks: When graded PrudentBots cooperate with graded FairBots"
---

# Checks: [When graded PrudentBots cooperate with graded FairBots]({{ "/findings/graded-prudent-fair.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/graded-prudent-fair/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/graded-prudent-fair/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
