# autoresearch-findings

Findings from machine-assisted research. Each finding lives in
`claims/<slug>/` with its claim, check scripts, recorded results and prior-art
answer, and has one post in `blog/`.

## How to verify a finding

Run each script in `claims/<slug>/checks/` with `python -I <script>`. A script
passes if it exits with status 0. `claims/<slug>/results/` holds results recorded in the
run that produced the finding; every script was run again before it was pushed here.



## Reporting prior art

If you know of prior work, please open an issue at https://github.com/kodakodapa/autoresearch-findings/issues.

## License

Code (check scripts) is licensed MIT (see `LICENSE`); prose (claims, blog
posts, prior-art answers) is licensed CC-BY-4.0 (see `LICENSE-TEXT`).

<!-- publish links -->
A census of modal agents in the prisoner's dilemma: This result was found by AI research agents (the autoresearch harness). It was checked by script; the proof and check files are included so anyone can re-run them.
Three-player modal agents in a public-goods game: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K14, K16, K18, K19) and partly checked by script (claims K13, K21); the proof and check files are included so anyone can re-run them.
Modal agents in the game of Chicken: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K7, K8, K10) and partly checked by script (claims K1, K2, K3, K4); the proof and check files are included so anyone can re-run them.
Unexploitable modal agents that cooperate with themselves: a census: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K11, K18) and partly checked by script (claims K51, K53, K2); the proof and check files are included so anyone can re-run them.
Blending self-defecting modal agents with FairBot: exact laws: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.
How large must a program be to tell graded FairBots apart?: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.
Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K9) and partly checked by script (claims K16, K13, K19); the proof and check files are included so anyone can re-run them.
Round robins of modal agents in the Stag Hunt: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K8, K3) and partly checked by script (claims K15, K6, K14, K5, K7, K4, K17, K18); the proof and check files are included so anyone can re-run them.
When graded PrudentBots cooperate with graded FairBots: This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.
An unexploitable modal agent that defects against itself: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K9, K11) and partly checked by script (claims K6); the proof and check files are included so anyone can re-run them.
Families of unexploitable agents that defect against themselves: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K14, K18, K21) and partly checked by script (claims K20, K22, K23); the proof and check files are included so anyone can re-run them.
A certified map of variants of Gödel's ontological argument: This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.
Settling informal claims about modal agents in Chicken: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K5, K11, K12) and partly checked by script (claims K6); the proof and check files are included so anyone can re-run them.
Site: https://kodakodapa.github.io/autoresearch-findings/
- [A census of modal agents in the prisoner's dilemma paper](claims/modal-agent-census/paper.pdf)
- [Three-player modal agents in a public-goods game paper](claims/three-player-modal-agents/paper.pdf)
- [Modal agents in the game of Chicken paper](claims/chicken-modal-agents/paper.pdf)
- [Unexploitable modal agents that cooperate with themselves: a census paper](claims/only-one-fairbot-census/paper.pdf)
- [Blending self-defecting modal agents with FairBot: exact laws paper](claims/blend-window-laws/paper.pdf)
- [How large must a program be to tell graded FairBots apart? paper](claims/graded-fairbot-separators/paper.pdf)
- [Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum paper](claims/staghunt-safe-coordinators/paper.pdf)
- [Round robins of modal agents in the Stag Hunt paper](claims/staghunt-round-robin/paper.pdf)
- [When graded PrudentBots cooperate with graded FairBots paper](claims/graded-prudent-fair/paper.pdf)
- [An unexploitable modal agent that defects against itself paper](claims/wn-gate-family/paper.pdf)
- [Families of unexploitable agents that defect against themselves paper](claims/gate-families/paper.pdf)
- [A certified map of variants of Gödel's ontological argument paper](claims/ontological-variant-map/paper.pdf)
- [Settling informal claims about modal agents in Chicken paper](claims/chicken-informal-claims/paper.pdf)
