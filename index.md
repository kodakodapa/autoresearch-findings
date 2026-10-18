---
layout: default
title: "Autoresearch findings"
---


# Autoresearch findings

Research findings with reproducible proofs and checks.

## Latest posts

{% for post in site.posts %}
- [{{ post.title }}]({{ post.url | relative_url }})
{% endfor %}

## Findings

- [An unexploitable modal agent that defects against itself]({{ "/findings/wn-gate-family.html" | relative_url }}) ([paper]({{ "/claims/wn-gate-family/paper.pdf" | relative_url }}), [checks]({{ "/claims/wn-gate-family/checks/" | relative_url }}))
- [When graded PrudentBots cooperate with graded FairBots]({{ "/findings/graded-prudent-fair.html" | relative_url }}) ([paper]({{ "/claims/graded-prudent-fair/paper.pdf" | relative_url }}), [checks]({{ "/claims/graded-prudent-fair/checks/" | relative_url }}))
- [Families of unexploitable agents that defect against themselves]({{ "/findings/gate-families.html" | relative_url }}) ([paper]({{ "/claims/gate-families/paper.pdf" | relative_url }}), [checks]({{ "/claims/gate-families/checks/" | relative_url }}))
