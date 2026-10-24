---
layout: default
title: "Checks: Unexploitable modal agents that cooperate with themselves: a census"
---

# Checks: [Unexploitable modal agents that cooperate with themselves: a census]({{ "/findings/only-one-fairbot-census.html" | relative_url }})

Each file checks one claim; the claim id is the file name's prefix. The [manifest]({{ "/claims/only-one-fairbot-census/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/only-one-fairbot-census/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
