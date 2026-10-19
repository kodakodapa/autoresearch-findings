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
An unexploitable modal agent that defects against itself: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.
When graded PrudentBots cooperate with graded FairBots: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.
Families of unexploitable agents that defect against themselves: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K14, K18, K21) and partly checked by script (claims K20, K22, K23); the proof and check files are included so anyone can re-run them.
A certified map of variants of Gödel's ontological argument: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.
Site: https://kodakodapa.github.io/autoresearch-findings/
- [An unexploitable modal agent that defects against itself paper](claims/wn-gate-family/paper.pdf)
- [When graded PrudentBots cooperate with graded FairBots paper](claims/graded-prudent-fair/paper.pdf)
- [Families of unexploitable agents that defect against themselves paper](claims/gate-families/paper.pdf)
- [A certified map of variants of Gödel's ontological argument paper](claims/ontological-variant-map/paper.pdf)
