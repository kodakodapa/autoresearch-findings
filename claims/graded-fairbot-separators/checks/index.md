---
layout: default
title: "Checks: How large must a program be to tell graded FairBots apart?"
---

# Checks: [How large must a program be to tell graded FairBots apart?]({{ "/findings/graded-fairbot-separators.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/graded-fairbot-separators/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/graded-fairbot-separators/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
