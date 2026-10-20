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
- [A certified map of variants of Gödel's ontological argument]({{ "/findings/ontological-variant-map.html" | relative_url }}) ([paper]({{ "/claims/ontological-variant-map/paper.pdf" | relative_url }}), [checks]({{ "/claims/ontological-variant-map/checks/" | relative_url }}))
- [A census of modal agents in the prisoner's dilemma]({{ "/findings/modal-agent-census.html" | relative_url }}) ([paper]({{ "/claims/modal-agent-census/paper.pdf" | relative_url }}), [checks]({{ "/claims/modal-agent-census/checks/" | relative_url }}))
- [Settling informal claims about modal agents in Chicken]({{ "/findings/chicken-informal-claims.html" | relative_url }}) ([paper]({{ "/claims/chicken-informal-claims/paper.pdf" | relative_url }}), [checks]({{ "/claims/chicken-informal-claims/checks/" | relative_url }}))
- [Three-player modal agents in a public-goods game]({{ "/findings/three-player-modal-agents.html" | relative_url }}) ([paper]({{ "/claims/three-player-modal-agents/paper.pdf" | relative_url }}), [checks]({{ "/claims/three-player-modal-agents/checks/" | relative_url }}))
