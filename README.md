# autoresearch-findings

Findings from machine-assisted research. Each finding lives in
`claims/<slug>/` with its claim, check scripts, recorded results and prior-art
answer, and has one post in `_posts/`.

## How to verify a finding

Each finding's post has a "How to verify" section giving the steps for that finding;
a programme finding also has it on its page and in `claims/<slug>/claim.md`.
In general:

- A finding checked by scripts: run each script in `claims/<slug>/checks/` with
  `python -I <script>`; it passes if it exits with status 0.
- A programme finding (one with `checks/library/`): install elan, check out the
  programme library at the commit its "How to verify" section records, build it and
  run the generated checks:

```sh
git clone https://github.com/kodakodapa/autoresearch-findings.git
cd autoresearch-findings
git checkout <commit> -- programmes/<programme>
cd programmes/<programme> && lake build
AR_LIBRARY=$PWD python -I ../../claims/<slug>/checks/lean-K<n>.py
```

`claims/<slug>/results/` holds the results recorded in the run that produced the
finding. Checks re-run when a finding was pushed have their output in
`claims/<slug>/results/publication/`; a finding without that folder was published before
these records were kept.



## Reporting prior art

If you know of prior work, please open an issue at https://github.com/kodakodapa/autoresearch-findings/issues.

## License

Code (check scripts) is licensed MIT (see `LICENSE`); prose (claims, blog
posts, prior-art answers) is licensed CC-BY-4.0 (see `LICENSE-TEXT`).

<!-- publish links -->
A census of modal agents in the prisoner's dilemma: This result was found by AI research agents (the autoresearch harness). It was checked by script; the proof and check files are included so anyone can re-run them.
When graded PrudentBots cooperate with graded FairBots: This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.
An unexploitable modal agent that defects against itself: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K9, K11) and partly checked by script (claims K6); the proof and check files are included so anyone can re-run them.
Families of unexploitable agents that defect against themselves: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K14, K18, K21) and partly checked by script (claims K20, K22, K23); the proof and check files are included so anyone can re-run them.
A certified map of variants of Gödel's ontological argument: This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.
Settling informal claims about modal agents in Chicken: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K5, K11, K12) and partly checked by script (claims K6); the proof and check files are included so anyone can re-run them.
Modal agents in the game of Chicken: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K7, K8, K10) and partly checked by script (claims K1, K2, K3, K4); the proof and check files are included so anyone can re-run them.
Three-player modal agents in a public-goods game: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K14, K16, K18, K19) and partly checked by script (claims K13, K21); the proof and check files are included so anyone can re-run them.
Blending self-defecting modal agents with FairBot: exact laws: This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.
How large must a program be to tell graded FairBots apart?: This result was found by AI research agents (the autoresearch harness). It was checked by scripts that run Lean proofs; the proof and check files are included so anyone can re-run them.
Unexploitable modal agents that cooperate with themselves: a census: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K11, K18) and partly checked by script (claims K51, K53, K2); the proof and check files are included so anyone can re-run them.
Round robins of modal agents in the Stag Hunt: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K8, K3) and partly checked by script (claims K15, K6, K14, K5, K7, K4, K17, K18); the proof and check files are included so anyone can re-run them.
Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum: This result was found by AI research agents (the autoresearch harness). It was partly checked by scripts that run Lean proofs (claims K9) and partly checked by script (claims K16, K13, K19); the proof and check files are included so anyone can re-run them.
Nominal-free proofs of the theorems Benzmüller's detector flags: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.
A complete calculus for the ℒ-general models of the ontological argument: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K1, K2, K3, K4, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16, K17, K18) and partly checked by scripts that run Lean proofs (claims K5); the proof and check files are included so anyone can re-run them.
Gödel's lemma L under the rigid reading, with no condition on positivity: This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K1, K3) and partly checked by script (claims K2); the proof and check files are included so anyone can re-run them.
From Lean proofs to certified derivations in the ontological embedding: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.
Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the verification steps below build the published programme library.
Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the verification steps below build the published programme library.
Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared: This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the verification steps below build the published programme library.
Site: https://kodakodapa.github.io/autoresearch-findings/
- [A census of modal agents in the prisoner's dilemma — Finding report](claims/modal-agent-census/paper.pdf)
- [When graded PrudentBots cooperate with graded FairBots — Finding report](claims/graded-prudent-fair/paper.pdf)
- [An unexploitable modal agent that defects against itself — Finding report](claims/wn-gate-family/paper.pdf)
- [Families of unexploitable agents that defect against themselves — Finding report](claims/gate-families/paper.pdf)
- [A certified map of variants of Gödel's ontological argument — Finding report](claims/ontological-variant-map/paper.pdf)
- [Settling informal claims about modal agents in Chicken — Finding report](claims/chicken-informal-claims/paper.pdf)
- [Modal agents in the game of Chicken — Finding report](claims/chicken-modal-agents/paper.pdf)
- [Three-player modal agents in a public-goods game — Finding report](claims/three-player-modal-agents/paper.pdf)
- [Blending self-defecting modal agents with FairBot: exact laws — Finding report](claims/blend-window-laws/paper.pdf)
- [How large must a program be to tell graded FairBots apart? — Finding report](claims/graded-fairbot-separators/paper.pdf)
- [Unexploitable modal agents that cooperate with themselves: a census — Finding report](claims/only-one-fairbot-census/paper.pdf)
- [Round robins of modal agents in the Stag Hunt — Finding report](claims/staghunt-round-robin/paper.pdf)
- [Safe modal agents that coordinate in the Stag Hunt: size 13 is the minimum — Finding report](claims/staghunt-safe-coordinators/paper.pdf)
- [Nominal-free proofs of the theorems Benzmüller's detector flags — Finding report](claims/ontological-nominal-free-proofs/paper.pdf)
- [A complete calculus for the ℒ-general models of the ontological argument — Finding report](claims/ontological-lgeneral-semantics/paper.pdf)
- [Gödel's lemma L under the rigid reading, with no condition on positivity — Finding report](claims/ontological-rigid-l/paper.pdf)
- [From Lean proofs to certified derivations in the ontological embedding — Finding report](claims/ontological-proof-translation/paper.pdf)
- [Polynomial calculus degree at least 5 over F2 for the onto functional pigeonhole principle with surplus 8 — Finding report](claims/pc-degree-5-onto-fphp-surplus-8/paper.pdf)
- [Exact polynomial calculus degree p for the onto functional pigeonhole principle with surplus divisible by p — Finding report](claims/exact-pc-degree-onto-fphp-first-level/paper.pdf)
- [Polynomial calculus degree above p for the onto functional pigeonhole principle with surplus divisible by p squared — Finding report](claims/pc-degree-above-p-onto-fphp-surplus-p-squared/paper.pdf)
