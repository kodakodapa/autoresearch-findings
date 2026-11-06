---
layout: default
title: "Checks: Round robins of modal agents in the Stag Hunt"
---

# Checks: [Round robins of modal agents in the Stag Hunt]({{ "/findings/staghunt-round-robin.html" | relative_url }})

For plain scripts, the claim id is the file name's prefix. Generated `lean-K*.py` files check promoted claims; `library/` holds declaring sources; `run-copies/` holds private Work working copies, not standalone builds. The [manifest]({{ "/claims/staghunt-round-robin/manifest.json" | relative_url }}) pins the data files they read, with their hashes.

{% for f in site.static_files %}{% if f.path contains "/claims/staghunt-round-robin/checks/" %}
- [{{ f.name }}]({{ f.path | relative_url }})
{% endif %}{% endfor %}
