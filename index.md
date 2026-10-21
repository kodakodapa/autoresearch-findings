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

- [A census of modal agents in the prisoner's dilemma]({{ "/findings/modal-agent-census.html" | relative_url }}) ([paper]({{ "/claims/modal-agent-census/paper.pdf" | relative_url }}), [checks]({{ "/claims/modal-agent-census/checks/" | relative_url }}))
- [When graded PrudentBots cooperate with graded FairBots]({{ "/findings/graded-prudent-fair.html" | relative_url }}) ([paper]({{ "/claims/graded-prudent-fair/paper.pdf" | relative_url }}), [checks]({{ "/claims/graded-prudent-fair/checks/" | relative_url }}))
- [An unexploitable modal agent that defects against itself]({{ "/findings/wn-gate-family.html" | relative_url }}) ([paper]({{ "/claims/wn-gate-family/paper.pdf" | relative_url }}), [checks]({{ "/claims/wn-gate-family/checks/" | relative_url }}))
- [Families of unexploitable agents that defect against themselves]({{ "/findings/gate-families.html" | relative_url }}) ([paper]({{ "/claims/gate-families/paper.pdf" | relative_url }}), [checks]({{ "/claims/gate-families/checks/" | relative_url }}))
- [A certified map of variants of Gödel's ontological argument]({{ "/findings/ontological-variant-map.html" | relative_url }}) ([paper]({{ "/claims/ontological-variant-map/paper.pdf" | relative_url }}), [checks]({{ "/claims/ontological-variant-map/checks/" | relative_url }}))
- [Settling informal claims about modal agents in Chicken]({{ "/findings/chicken-informal-claims.html" | relative_url }}) ([paper]({{ "/claims/chicken-informal-claims/paper.pdf" | relative_url }}), [checks]({{ "/claims/chicken-informal-claims/checks/" | relative_url }}))
- [Modal agents in the game of Chicken]({{ "/findings/chicken-modal-agents.html" | relative_url }}) ([paper]({{ "/claims/chicken-modal-agents/paper.pdf" | relative_url }}), [checks]({{ "/claims/chicken-modal-agents/checks/" | relative_url }}))
- [Three-player modal agents in a public-goods game]({{ "/findings/three-player-modal-agents.html" | relative_url }}) ([paper]({{ "/claims/three-player-modal-agents/paper.pdf" | relative_url }}), [checks]({{ "/claims/three-player-modal-agents/checks/" | relative_url }}))
- [Blending self-defecting modal agents with FairBot: exact laws]({{ "/findings/blend-window-laws.html" | relative_url }}) ([paper]({{ "/claims/blend-window-laws/paper.pdf" | relative_url }}), [checks]({{ "/claims/blend-window-laws/checks/" | relative_url }}))
- [How large must a program be to tell graded FairBots apart?]({{ "/findings/graded-fairbot-separators.html" | relative_url }}) ([paper]({{ "/claims/graded-fairbot-separators/paper.pdf" | relative_url }}), [checks]({{ "/claims/graded-fairbot-separators/checks/" | relative_url }}))
- [Unexploitable modal agents that cooperate with themselves: a census]({{ "/findings/only-one-fairbot-census.html" | relative_url }}) ([paper]({{ "/claims/only-one-fairbot-census/paper.pdf" | relative_url }}), [checks]({{ "/claims/only-one-fairbot-census/checks/" | relative_url }}))
- [Round robins of modal agents in the Stag Hunt]({{ "/findings/staghunt-round-robin.html" | relative_url }}) ([paper]({{ "/claims/staghunt-round-robin/paper.pdf" | relative_url }}), [checks]({{ "/claims/staghunt-round-robin/checks/" | relative_url }}))
- [Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum]({{ "/findings/staghunt-safe-coordinators.html" | relative_url }}) ([paper]({{ "/claims/staghunt-safe-coordinators/paper.pdf" | relative_url }}), [checks]({{ "/claims/staghunt-safe-coordinators/checks/" | relative_url }}))
