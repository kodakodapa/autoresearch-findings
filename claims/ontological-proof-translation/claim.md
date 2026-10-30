# From Lean proofs to certified derivations in the ontological embedding

Cite as: https://doi.org/10.5281/zenodo.23795779

<!-- owner-summary -->
## Setting

The companion findings on this site give v4 [1] a machine-checked
semantics: a deep proof calculus, sound and complete over $\mathcal L$-general models. Its
derivations were written by hand. The shallow embedding's Lean proofs are richer than
higher-order logic, which is how a nominal can hide in a proof that v4's detector passes. This
finding builds a Lean command that reads a proof and produces the certified derivation itself.

## Result

- **The translator.** For a theorem of a shallow v4 module whose proof stays within higher-order
  logic (introduction and elimination of the connectives and quantifiers, classical logic,
  `Eq.subst`, `congrArg`, `congrFun`, `funext`, `propext`, beta and eta, unfolding of the
  module's definitions), `#deep_translate X as N` reads the statement and the proof term and
  builds a derivation in the certified calculus, kernel-checked, whose conclusion is the deep
  image of the statement, matched by `rfl`. It also reads off the module's axioms the proof
  uses as an $\mathcal L$-theory $T$, and yields `N.valid`: the statement holds at every world
  of every v4 $\mathcal L$-general model of $T$ with nonempty individuals. A proof outside the
  fragment, or one violating the whole-term condition, is rejected with the first offending
  step named. The rejections are tests the build enforces: v4's own hybrid proof of `L_R`, the
  detector-passing proof with a hidden nominal, and a minimal `congrFun` probe.
- **Applied to v4's proofs.** L under the rigid reading (from the detector-certified proof of
  `L_R`), unrestricted Ax1Gen from Ax1GenTwo in variants 2 and 3′, modal collapse, necessary
  and possible existence of a God-like being, and the essence theorems (`EssMemI`, `UniqueEss1`,
  `UniqueEss2`, `Ess_iff_Ess2`) in variant 2, 3′ and in v4's S4 module of variant 3, each now as
  a semantic theorem over $\mathcal L$-general models.
- **The frame condition for Th3.** For Th3 ($\Diamond\exists^E G\to\Box\exists^E G$) from Ax2a,
  Ax2b and Ax3 in variant 2, translation gives validity on symmetric and on Euclidean frames.
  Reflexive and transitive frames do not suffice, nor does any set of frame formulas true on a
  fixed five-edge frame. The exact condition: Th3 holds everywhere in every $\mathcal L$-general
  model on $(W,R)$ iff no world outside an $R$-closed set $B$ of all-dead or all-serial worlds
  sees both a member and a non-member of $B$.

## Why it matters

A detector certifies a proof only as far as the detector reads it correctly. The translator
replaces that trust with a kernel-checked derivation and the calculus's soundness theorem, and
it turns v4's Lean proofs into statements about v4's semantics without rewriting them by hand.
The Th3 result shows what the semantics adds: an exact frame condition, where the shallow
embedding only gives sufficient ones.

## Proved vs checked

Everything is Lean 4 (core library, axioms propext, Classical.choice and Quot.sound only) and is
kernel-checked in the library build. The run's skeptic verified the translator's first three
results (L under the rigid reading; the equivalence in variants 2 and 3′); the remaining
thirteen claims carry the status *analogy*, because the run ended before its skeptic checked
them. We rebuilt six of them outside the run and checked their axioms: the symmetric-frame result,
the reflexive–transitive and five-edge counterexamples, the general countermodel construction,
the sufficiency direction, and the exact condition.
<!-- /owner-summary -->

This result extends:

- C. Benzmüller, "Proofs Without Nominals …", arXiv 2609.36279 v4 (https://arxiv.org/abs/2609.36279):.
- C. Benzmüller, "Gödel's and Scott's Variants … in Lean 4 and TPTP THF", arXiv 2609.26806 v3 (https://arxiv.org/abs/2609.26806): the port the developments build on. It points to 2609.36279 for nominals and the open questions, and has no general-model results.
- C. Benzmüller, "A Comment on Modal Collapse and Ultrafilters", arXiv 2608.07578 (https://arxiv.org/pdf/2608.07578): rigidity of positivity as the driver of collapse. It is background for K1's proviso question and does not address general models.

Our prior-art search (2026-10-23) covered:

- WebFetch: https://arxiv.org/a/benzmuller_c_1 (author listing, 2026 papers), 2026-10-23
- Web pages other than the arXiv listing were seen through search-result summaries only. The Springer and LLP papers were not opened.

The search was run automatically by claude/claude-opus-5-5.

The checkers' full answers, with every query and file they searched, are published with this finding (`prior-art/`).

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was proved in Lean; the proof and check files are included so anyone can re-run them.

## K1

Let $T$ be the $\mathcal L$-sentences Ax1GenR at PosGlobal, Ax4, Ax2a, Ax2b of OpenQuestions.Ax1GenRigidVariant2, read off RigidHF.L_R_hf by the translator. Then $P\,G$ (run 4's Run3.K1.Pos Run3.K1.God) holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K1-TranslateRigid.lean`: Programme.Run6.H.LR.valid\_god — pass (`results/K1-4.json`)
- proof `checks/K1-TranslateRigid.lean`: Programme.Run6.H.LR.of\_deep — pass (`results/K1-5.json`)
- proof `checks/K1-TranslateRigid.lean`: Programme.Run6.H.LR.of\_struct — pass (`results/K1-6.json`)
- reasoning: Structural image check (the theorist's C8). For each sentence of $T$ read off module axiom $X$ with $n$ outer binders the file proves `N.struct<k>: type_of% @X = shV R existsAt P n N.ax<k> ()`, and `N.struct_φ` for the statement, by `rfl` after δ-unfolding the module side; the only rewrites allowed are `(a ↔ b) = ((a → b) ∧ (b → a))` and `(∃ v, R w v ∧ B v) = ¬∀ v, R w v → ¬B v`, identities of Lean propositions. `shR` is the unguarded structural reading, one Lean connective per constructor, so an extra conjunct (the theorist's `phiSep` mutant, rejected by a `fail_if_success` test in TranslateV2Mod.lean), a dropped guard or a swapped quantifier fails. `N.of_struct` re-proves the module statement from the deep certificate through `of_valid_full`, `shV_iff` and these equations only, so $T$ and $\varphi$ are the module's sentences up to definitional unfolding, not just up to full-structure equivalence (the theorist's `full_check_blind`).

Prior art: partial prior art (answer: `prior-art/R1.md`)

### Provenance

- run: 20261023-0556
- claim: K1
- author: pr (claude)
- round: 6
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K1-4.json, K1-5.json, K1-6.json

## K3

Let $T$ be the $\mathcal L$-sentences Ax1GenTwo, $\exists x.\top$, Ax4, Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant2, read off the module by the translator. Then unrestricted Ax1Gen holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals (ValidV4).

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K3-TranslateTwo.lean`: Programme.Run6.H.A1G.valid\_ax1gen — pass (`results/K3-4.json`)
- proof `checks/K3-TranslateTwo.lean`: Programme.Run6.H.A1G.of\_deep — pass (`results/K3-3.json`)
- proof `checks/K3-TranslateTwo.lean`: Programme.Run6.H.A1G.of\_struct — pass (`results/K3-5.json`)
- reasoning: Structural image check (the theorist's C8). For each sentence of $T$ read off module axiom $X$ with $n$ outer binders the file proves `N.struct<k>: type_of% @X = shV R existsAt P n N.ax<k> ()`, and `N.struct_φ` for the statement, by `rfl` after δ-unfolding the module side; the only rewrites allowed are `(a ↔ b) = ((a → b) ∧ (b → a))` and `(∃ v, R w v ∧ B v) = ¬∀ v, R w v → ¬B v`, identities of Lean propositions. `shR` is the unguarded structural reading, one Lean connective per constructor, so an extra conjunct (the theorist's `phiSep` mutant, rejected by a `fail_if_success` test in TranslateV2Mod.lean), a dropped guard or a swapped quantifier fails. `N.of_struct` re-proves the module statement from the deep certificate through `of_valid_full`, `shV_iff` and these equations only, so $T$ and $\varphi$ are the module's sentences up to definitional unfolding, not just up to full-structure equivalence (the theorist's `full_check_blind`).

Prior art: partial prior art (answer: `prior-art/R1.md`)

### Provenance

- run: 20261023-0556
- claim: K3
- author: pr (claude)
- round: 3
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K3-3.json, K3-4.json, K3-5.json

## K4

Let $T$ be the $\mathcal L$-sentences Ax1GenTwo, $\exists x.\top$, Ax4, Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant3Plain, read off the module by the translator. Then unrestricted Ax1Gen holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals (ValidV4).

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K4-TranslateV3.lean`: Programme.Run6.H.A1G3.valid\_ax1gen — pass (`results/K4-4.json`)
- proof `checks/K4-TranslateV3.lean`: Programme.Run6.H.A1G3.of\_deep — pass (`results/K4-3.json`)
- proof `checks/K4-TranslateV3.lean`: Programme.Run6.H.A1G3.of\_struct — pass (`results/K4-5.json`)
- reasoning: Structural image check (the theorist's C8). For each sentence of $T$ read off module axiom $X$ with $n$ outer binders the file proves `N.struct<k>: type_of% @X = shV R existsAt P n N.ax<k> ()`, and `N.struct_φ` for the statement, by `rfl` after δ-unfolding the module side; the only rewrites allowed are `(a ↔ b) = ((a → b) ∧ (b → a))` and `(∃ v, R w v ∧ B v) = ¬∀ v, R w v → ¬B v`, identities of Lean propositions. `shR` is the unguarded structural reading, one Lean connective per constructor, so an extra conjunct (the theorist's `phiSep` mutant, rejected by a `fail_if_success` test in TranslateV2Mod.lean), a dropped guard or a swapped quantifier fails. `N.of_struct` re-proves the module statement from the deep certificate through `of_valid_full`, `shV_iff` and these equations only, so $T$ and $\varphi$ are the module's sentences up to definitional unfolding, not just up to full-structure equivalence (the theorist's `full_check_blind`).

Prior art: partial prior art (answer: `prior-art/R1.md`)

### Provenance

- run: 20261023-0556
- claim: K4
- author: pr (claude)
- round: 3
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K4-3.json, K4-4.json, K4-5.json

## K5

Let $T$ be the $\mathcal L$-sentences Ax4, Ax3, Ax1GenTwo, Ax2a, Ax2b, $\exists x.\top$ of OpenQuestions.Ax1GenTwoVariant2, read off its proof of MC_Two_unconditional. Then $\forall p{:}\sigma.\,p\to\Box p$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.MCU.valid — pass (`results/K5-3.json`)
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.MCU.of\_deep — pass (`results/K5-2.json`)
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.MCU.of\_struct — pass (`results/K5-4.json`)
- reasoning: Structural image check (the theorist's C8). For each sentence of $T$ read off module axiom $X$ with $n$ outer binders the file proves `N.struct<k>: type_of% @X = shV R existsAt P n N.ax<k> ()`, and `N.struct_φ` for the statement, by `rfl` after δ-unfolding the module side; the only rewrites allowed are `(a ↔ b) = ((a → b) ∧ (b → a))` and `(∃ v, R w v ∧ B v) = ¬∀ v, R w v → ¬B v`, identities of Lean propositions. `shR` is the unguarded structural reading, one Lean connective per constructor, so an extra conjunct (the theorist's `phiSep` mutant, rejected by a `fail_if_success` test in TranslateV2Mod.lean), a dropped guard or a swapped quantifier fails. `N.of_struct` re-proves the module statement from the deep certificate through `of_valid_full`, `shV_iff` and these equations only, so $T$ and $\varphi$ are the module's sentences up to definitional unfolding, not just up to full-structure equivalence (the theorist's `full_check_blind`).

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K5
- author: pr (claude)
- round: 7
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K5-2.json, K5-3.json, K5-4.json

## K6

Let $T$ be the $\mathcal L$-sentences Ax4, Ax3, Ax1GenTwo, Ax2a, $\exists x.\top$ of OpenQuestions.Ax1GenTwoVariant2, read off its proofs. Then $\Box\exists^E x.G\,x$ and $\neg\Box\neg\exists^E x.G\,x$ hold at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.Th5U.valid — pass (`results/K6-5.json`)
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.Th4.valid — pass (`results/K6-6.json`)
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.Th5U.of\_deep — pass (`results/K6-3.json`)
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.Th4.of\_deep — pass (`results/K6-4.json`)
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.Th5U.of\_struct — pass (`results/K6-7.json`)
- proof `checks/K5-TranslateV2Mod.lean`: Programme.Run6.H.Th4.of\_struct — pass (`results/K6-8.json`)
- reasoning: Structural image check (the theorist's C8). For each sentence of $T$ read off module axiom $X$ with $n$ outer binders the file proves `N.struct<k>: type_of% @X = shV R existsAt P n N.ax<k> ()`, and `N.struct_φ` for the statement, by `rfl` after δ-unfolding the module side; the only rewrites allowed are `(a ↔ b) = ((a → b) ∧ (b → a))` and `(∃ v, R w v ∧ B v) = ¬∀ v, R w v → ¬B v`, identities of Lean propositions. `shR` is the unguarded structural reading, one Lean connective per constructor, so an extra conjunct (the theorist's `phiSep` mutant, rejected by a `fail_if_success` test in TranslateV2Mod.lean), a dropped guard or a swapped quantifier fails. `N.of_struct` re-proves the module statement from the deep certificate through `of_valid_full`, `shV_iff` and these equations only, so $T$ and $\varphi$ are the module's sentences up to definitional unfolding, not just up to full-structure equivalence (the theorist's `full_check_blind`).

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K6
- author: pr (claude)
- round: 7
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K6-3.json, K6-4.json, K6-5.json, K6-6.json, K6-7.json, K6-8.json

## K7

Let $T$ be the $\mathcal L$-sentences Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant2, read off its proof of Th3. Then $\neg\Box\neg\exists^E x.G\,x\to\Box\exists^E x.G\,x$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals and symmetric $R$.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K7-TranslateKB.lean`: Programme.Run6.H.Th3K.validF — pass (`results/K7-1.json`)
- proof `checks/K7-TranslateKB.lean`: Programme.Run6.H.Th3K.of\_struct — pass (`results/K7-2.json`)
- reasoning: Frame hypotheses (the theorist's C7). The statement's hypothesis `symm: ∀ x y, x 𝗿 y → y 𝗿 x` reifies to the closed frame formula $\forall u\,v.\,R\,u\,v\to R\,v\,u$ (`N.Fs`, checked by `rfl` in the file; `N.Fs_ok: AllRel N.Fs` built constructor by constructor). It is not an $\mathcal L$-sentence, so it is not put into $T$. It stays in the hypothesis list of `N.deep: DW N.Tfull [.w] (N.Fs.map wk) …`. `sound_v4_wt_frames` (the theorist's `sound_v4_wt_frame` for a list: `toStr` keeps the model's accessibility relation, and a `RelOnly` formula depends on it alone) gives `N.validF: ValidV4Fs N.Fs N.T N.φ`, which quantifies over v4 VM/LGen models with nonempty individuals whose $R$ satisfies every formula of `N.Fs`. A hypothesis that mentions $P$ is not a frame formula; that probe is refused under `#guard_msgs` in the file. `N.of_struct` re-proves the module's statement from `N.validF` through the theorist's `of_validF_full` (for a list), the structural `rfl` checks (C8), and `frame_hold` (the module's `symm` gives `FrameHolds R F`). In that last step only the direction `symm → F` is needed: a weaker reading of the frame condition would make the proved statement stronger, not wrong.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K7
- author: pr (claude)
- round: 6
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K7-1.json, K7-2.json

## K8

Let $T$ be the $\mathcal L$-sentences Ax1Gen, Ax2a, Ax2b, Ax4, $\exists x.\top$ of OpenQuestions.GoedelVariantHOML3inS4oneFile (variant 3), read off its proof of MC_K. Then $\forall p{:}\sigma.\,p\to\Box p$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K8-TranslateS4V3.lean`: Programme.Run6.H.MC3K.valid — pass (`results/K8-1.json`)
- proof `checks/K8-TranslateS4V3.lean`: Programme.Run6.H.MC3K.of\_struct — pass (`results/K8-2.json`)
- reasoning: The module's own proofs are translated by `#deep_translate`, which reads the sentences of $T$ off the module axioms the proof uses; lemmas (L, G\_ex, Ax2a') are cut in through the theory's prefix (`Good`/`GoodF`). Soundness per output: the kernel checks `N.deep`, and `sound_v4_wt` (run 4) or `sound_v4_wt_frames` turns it into the validity statement. Statement identity: `N.of_struct: type_of% @X` re-proves the module's statement from the certificate through the structural `rfl` checks `N.struct<k>`/`N.struct_φ` (C8). Those checks allow only the rewrites `iff_nf`, `dia_nf`, `exAct_nf`, which are identities of Lean propositions. Variant 3's Ax4 carries the non-emptiness guard $\varphi\neq\lambda x.\bot$ inside the box, as in the module. No Lean theorem is claimed about the translator itself.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K8
- author: pr (claude)
- round: 7
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K8-1.json, K8-2.json

## K9

Let $T$ be the $\mathcal L$-sentences Ax1Gen, Ax2a, Ax4, $\exists x.\top$ of OpenQuestions.GoedelVariantHOML3inS4oneFile. In every v4 $\mathcal L$-general model of $T$ with nonempty individuals, on any frame, $\Box\exists^E x.G\,x$ and $\neg\Box\neg\exists^E x.G\,x$ hold at every world.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K8-TranslateS4V3.lean`: Programme.Run6.H.Th5V3.valid — pass (`results/K9-1.json`)
- proof `checks/K8-TranslateS4V3.lean`: Programme.Run6.H.Th4S4.validF — pass (`results/K9-2.json`)
- proof `checks/K8-TranslateS4V3.lean`: Programme.Run6.H.Th5V3.of\_struct — pass (`results/K9-3.json`)
- proof `checks/K8-TranslateS4V3.lean`: Programme.Run6.H.Th4S4.of\_struct — pass (`results/K9-4.json`)
- reasoning: The module's own proofs are translated by `#deep_translate`, which reads the sentences of $T$ off the module axioms the proof uses; lemmas (L, G\_ex, Ax2a') are cut in through the theory's prefix (`Good`/`GoodF`). Soundness per output: the kernel checks `N.deep`, and `sound_v4_wt` (run 4) or `sound_v4_wt_frames` turns it into the validity statement. Statement identity: `N.of_struct: type_of% @X` re-proves the module's statement from the certificate through the structural `rfl` checks `N.struct<k>`/`N.struct_φ` (C8). Those checks allow only the rewrites `iff_nf`, `dia_nf`, `exAct_nf`, which are identities of Lean propositions. Variant 3's Ax4 carries the non-emptiness guard $\varphi\neq\lambda x.\bot$ inside the box, as in the module. No Lean theorem is claimed about the translator itself. Th4S4's frame list `Fs` comes from the module axiom `Rrefl`. `ValidV4Fs Fs` quantifies over v4 models whose $R$ satisfies every formula of `Fs`; `Fs_ok: AllRel Fs` is built constructor by constructor.
- proof `checks/K9-TranslateS4V3b.lean`: Programme.Run6.H.Th4B.valid — pass (`results/K9-5.json`)
- proof `checks/K9-TranslateS4V3b.lean`: Programme.Run6.H.Th4B.of\_struct — pass (`results/K9-6.json`)
- reasoning: the theorist's ThH19. In variant 3 the inclusion in Ax4 is boxed. At a world with no successor, $G\supset^N\neg G$ is therefore vacuous, and Ax4 with L gives $P\neg G$, which contradicts Ax2a. Th4\_box reaches the same contradiction from $\Box\neg\exists^E G$ through G\_ex at each successor, with no world-existential step. The translator emits no frame formula. `Th4B.T = Th5V3.T` and `Th4B.φ = Th4S4.φ` are checked by rfl.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K9
- author: pr (claude)
- round: 7
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K9-1.json, K9-2.json, K9-3.json, K9-4.json, K9-5.json, K9-6.json

## K10

For the $\mathcal L$-sentences $T$ = Ax3, Ax2a, Ax2b and $\varphi$ = Th3 of K7 (Th3K): $\varphi$ is not valid in all v4 $\mathcal L$-general models of $T$ with nonempty individuals whose $R$ is reflexive and transitive; hence also not without frame condition.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K10-TranslateKBNec.lean`: Programme.Run6.H.NecSymm.not\_validFs\_S4 — pass (`results/K10-1.json`)
- proof `checks/K10-TranslateKBNec.lean`: Programme.Run6.H.NecSymm.not\_valid — pass (`results/K10-2.json`)
- reasoning: the theorist's two-world S4 model ThH7: R = {00,01,11}, one always-actual entity, positivity P phi w:= phi () 1. Its full structure is L-general (of\_validFs\_full). Th3K.ax0..2 (Ax3, Ax2b, Ax2a, the very terms emitted for K7) hold there by definitional unfolding of shR (NecSymm.hT uses `exact ThH7.Ax3 w` etc., no rewriting); the closed frame formulas for reflexivity and transitivity hold (NecSymm.frames). So ValidV4Fs \[refl, trans\] Th3K.T Th3K.phi would give Th3 at world 0, contradicting ThH7.Th3\_fails; ValidV4 implies ValidV4Fs for any frame list, giving not\_valid. World 0 sees world 1 but not conversely, which is exactly where symmetry fails.
- reasoning: Unchanged proof (ThH7 two-world S4 model R = {00,01,11}). The model is neither symmetric nor Euclidean (R00, R01 hold, R10 fails), consistent with K7 and with the Euclidean result; no claim that symmetry is necessary.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K10
- author: pr (claude)
- round: 10
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K10-1.json, K10-2.json

## K11

Let $T$ be Ax4, Ax3, Ax2a, Ax1GenTwo, $\exists x.\top$ of OpenQuestions.Ax1GenTwoVariant3Plain (plus Ax2b for UniqueEss). Then EssMemI_K_unconditional, UniqueEss1_K_unconditional, UniqueEss2_K_unconditional hold at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K11-TranslateV3NE.lean`: Programme.Run6.H.EssMemV3.valid — pass (`results/K11-1.json`)
- proof `checks/K11-TranslateV3NE.lean`: Programme.Run6.H.EssMemV3.of\_struct — pass (`results/K11-2.json`)
- proof `checks/K11-TranslateV3NE.lean`: Programme.Run6.H.UE1V3.valid — pass (`results/K11-3.json`)
- proof `checks/K11-TranslateV3NE.lean`: Programme.Run6.H.UE1V3.of\_struct — pass (`results/K11-4.json`)
- proof `checks/K11-TranslateV3NE.lean`: Programme.Run6.H.UE2V3.valid — pass (`results/K11-5.json`)
- proof `checks/K11-TranslateV3NE.lean`: Programme.Run6.H.UE2V3.of\_struct — pass (`results/K11-6.json`)
- reasoning: Soundness per output: the kernel checks `N.deep: DW...`; `sound_v4_wt` (run 4) gives `N.valid: ValidV4 N.T N.phi`. The not-E rewrite uses only existing DW rules: the forall-E/exists-I instance is the certified L-term M\[E1\], and the switch between M\[E1\] and M\[E0\] is a Leibniz step at type e -\> sigma, which is plain, so LeibOK holds by its first disjunct. Statement identity: `N.of_struct: type_of% @X` re-proves the module statement from the certificate through the structural rfl checks `N.struct<k>`/`N.struct_phi` (C8), with only the rewrites iff\_nf, dia\_nf, exAct\_nf. No Lean theorem is claimed about the translator.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K11
- author: pr (claude)
- round: 9
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K11-1.json, K11-2.json, K11-3.json, K11-4.json, K11-5.json, K11-6.json

## K12

Let $T$ be the $\mathcal L$-sentences Ax3, Ax2a, Ax2b of OpenQuestions.Ax1GenTwoVariant2. Then $\neg\Box\neg\exists^E x.G\,x\to\Box\exists^E x.G\,x$ holds at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals and Euclidean $R$.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K12-TranslateEucl.lean`: Programme.Run6.H.Th3E.validF — pass (`results/K12-1.json`)
- proof `checks/K12-TranslateEucl.lean`: Programme.Run6.H.Th3E.of\_struct — pass (`results/K12-2.json`)
- reasoning: Same mechanism as K7 (C7 frame hypotheses, C8 structural checks). `Th3E.validF: ValidV4Fs Th3E.Fs Th3E.T Th3E.phi` comes from the kernel-checked derivation `Th3E.deep` via `sound_v4_wt_frames`; Fs is the Euclidean frame formula (rfl-checked in the file). `Th3E.of_struct` re-proves the module-level statement (with hypothesis eucl) from validF through of\_validFs\_full, the structural rfl checks and frame\_hold; only the direction eucl -\> F is used. The source proof is the theorist's ThH10.Th3\_eucl, copied verbatim; no Lean theorem is claimed about the translator.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K12
- author: pr (claude)
- round: 11
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K12-1.json, K12-2.json

## K13

Let $T$ be Ax1Gen, Ax2a, Ax3, Ax4, $\exists x.\top$ of OpenQuestions.GoedelVariantHOML3inS4oneFile (plus Ax2b for UniqueEss). Then EssMemI_K, UniqueEss1_K, UniqueEss2_K, Ess_iff_Ess2_K hold at every world of every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.EssMem3S.valid — pass (`results/K13-1.json`)
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.EssMem3S.of\_struct — pass (`results/K13-2.json`)
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.UE1S.valid — pass (`results/K13-3.json`)
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.UE1S.of\_struct — pass (`results/K13-4.json`)
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.UE2S.valid — pass (`results/K13-5.json`)
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.UE2S.of\_struct — pass (`results/K13-6.json`)
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.EssIffS.valid — pass (`results/K13-7.json`)
- proof `checks/K13-TranslateS4NE.lean`: Programme.Run6.H.EssIffS.of\_struct — pass (`results/K13-8.json`)
- reasoning: Same mechanism as K11 (not-E rewrite: forall-E/exists-I at the certified L-term M\[E1\], E1 = lambda z. exists^E y. y = z, switched to M\[E0\] by a Leibniz step at the plain type e -\> sigma, so LeibOK holds by its first disjunct). The kernel checks N.deep; sound\_v4\_wt gives N.valid: ValidV4 N.T N.phi. No frame formula is emitted: the module proofs use the lemma Reach\_K, not Rrefl/Rtrans, so the result holds on arbitrary frames. N.of\_struct re-proves the module statement from N.valid through the structural rfl checks (C8; rewrites iff\_nf, dia\_nf, exAct\_nf only). The module's own proofs are translated unchanged. No Lean theorem is claimed about the translator.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K13
- author: pr (claude)
- round: 12
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K13-1.json, K13-2.json, K13-3.json, K13-4.json, K13-5.json, K13-6.json, K13-7.json, K13-8.json

## K14

Let $T$ = Ax3, Ax2b, Ax2a of OpenQuestions.Ax1GenTwoVariant2 (K7's Th3K) and $\varphi$ = Th3. For every list $F_s$ of frame formulas true on F4 $=\{01,03,31,12,21\}$, $\varphi$ is not valid in all v4 $\mathcal L$-general models of $T$ with nonempty individuals whose $R$ satisfies $F_s$.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K14-TranslateKBF4.lean`: Programme.Run6.H.F4.not\_validFs\_F4 — pass (`results/K14-1.json`)
- proof `checks/K14-TranslateKBF4.lean`: Programme.Run6.H.F4.F4\_Qt — pass (`results/K14-2.json`)
- reasoning: Pull-back along a surjective bounded morphism (forth/back) keeps carriers and evaluation; only the box clause uses forth/back, pr\_inj uses surjectivity (the theorist's ThH13). The refuting model on F4 is the pull-back of the full model on F3, which is L-general by ofStr\_lgen. F4\_Qt: no world of F4 sees a quasi-terminal world together with a different world.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K14
- author: pr (claude)
- round: 14
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K14-1.json, K14-2.json

## K15

For $T$ = Ax3, Ax2b, Ax2a, $\varphi$ = Th3 of Ax1GenTwoVariant2: on any frame $(W,R)$ with $B$ $R$-closed, uniform (all members have successors or none), $b\in B$, $u\notin B$, $Rwb$, $Rwu$, some v4 $\mathcal L$-general model of $T$ on $(W,R)$, nonempty individuals, refutes $\varphi$.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K15-TranslateKBQL.lean`: Programme.Run6.H.QL.not\_validOn — pass (`results/K15-1.json`)
- proof `checks/K15-TranslateKBQL.lean`: Programme.Run6.H.QL.not\_validFs — pass (`results/K15-2.json`)
- reasoning: col B is a surjective bounded morphism from (W,R) onto RC R B when B is nonempty, R-closed and uniform (col\_back). Pulling an L-general model back along a surjective bounded morphism keeps it L-general with the same evaluation (pullL, the theorist's ThH13), and its accessibility is R by definition. The full model on RC R B with P phi:= phi () (inr ()) satisfies Ax3 because inr () is quasi-terminal (pt\_qt), satisfies Ax2a/Ax2b trivially, and refutes Th3 at col w.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K15
- author: pr (claude)
- round: 15
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K15-1.json, K15-2.json

## K16

Let $T$ = Ax3, Ax2b, Ax2a of OpenQuestions.Ax1GenTwoVariant2. On any frame $(W,R)$ with $Q_L$ (no world outside an $R$-closed $B$ sees a member and a non-member of $B$), $\Diamond\exists^E G\to\Box\exists^E G$ holds everywhere in every v4 $\mathcal L$-general model of $T$ with nonempty individuals.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K16-TranslateKBQLi.lean`: Programme.Run6.H.QLi.validOn\_QL — pass (`results/K16-1.json`)
- proof `checks/K16-TranslateKBQLi.lean`: Programme.Run6.H.Th2X.valid — pass (`results/K16-2.json`)
- proof `checks/K16-TranslateKBQLi.lean`: Programme.Run6.H.QLi.validOn\_symm — pass (`results/K16-3.json`)
- proof `checks/K16-TranslateKBQLi.lean`: Programme.Run6.H.QLi.validOn\_eucl — pass (`results/K16-4.json`)
- reasoning: Th2X.valid gives $\psi_G\to\Box\psi_G$ at every world of every L-general model of Th3K.T (T\_eq, th2\_eq by rfl). Then the extension $B$ of $\psi_G$ is R-closed. If $w\models\Diamond\psi_G$, some $b\in B$ with $Rwb$. If $w\in B$, closure gives $\Box\psi_G$; otherwise $Q_L$ puts every successor $u$ of $w$ in $B$. Only the LGen clauses imp, neg, box are used (th3\_of\_th2). th3\_eq identifies the result with Th3K.φ by rfl.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K16
- author: pr (claude)
- round: 16
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K16-1.json, K16-2.json, K16-3.json, K16-4.json

## K17

Let $T$ = Ax3, Ax2b, Ax2a of OpenQuestions.Ax1GenTwoVariant2. On any frame $(W,R)$, Th3 holds everywhere in every v4 $\mathcal L$-general model of $T$ with nonempty individuals iff no world outside an $R$-closed set $B$ of all-dead or all-serial worlds sees a member and a non-member of $B$.

**Status: analogy: a resemblance, not an established result**

Kind: theorem

Evidence:
- proof `checks/K17-TranslateKBQU.lean`: Programme.Run6.H.QU.validOn\_iff\_QU — pass (`results/K17-1.json`)
- proof `checks/K17-TranslateKBQU.lean`: Programme.Run6.H.QU.F5\_valid — pass (`results/K17-2.json`)
- proof `checks/K17-TranslateKBQU.lean`: Programme.Run6.H.QU.F5\_not\_QL — pass (`results/K17-3.json`)
- proof `checks/K17-TranslateKBQU.lean`: Programme.Run6.H.DPos.valid — pass (`results/K17-4.json`)
- proof `checks/K17-TranslateKBQU.lean`: Programme.Run6.H.DRigN.valid — pass (`results/K17-5.json`)
- reasoning: If: from Th2X.valid, DPos.valid, DRig.valid, DRigN.valid (kernel-checked derivations, sound\_v4\_wt) the four sentences $\psi\to\Box\psi$, $\psi\to(\Box\bot\leftrightarrow\rho)$, $\rho\to\Box\rho$, $\neg\rho\to\Box\neg\rho$ hold everywhere ($\psi=\exists^E G$, $\rho=P(\lambda z.\Box\bot)$, all matched by rfl). Then $B=\{v\mid\psi v\wedge(\rho v\leftrightarrow\rho b)\}$ is R-closed and uniform, and $Q_U$ gives $\Box\psi$ (th3\_of\_unif). Only if: a closed uniform violating $B$ gives K15's refuting model (collapse plus pull-back).
- proof `checks/K17-TranslateKBQC.lean`: Programme.Run6.H.QC.validOn\_iff\_QC — pass (`results/K17-6.json`)
- proof `checks/K17-TranslateKBQC.lean`: Programme.Run6.H.QC.QU\_iff\_QC — pass (`results/K17-7.json`)
- proof `checks/K17-TranslateKBQC.lean`: Programme.Run6.H.QC.dead\_only\_of\_validOn — pass (`results/K17-8.json`)
- reasoning: the theorist's ThH18 (verbatim). For $Q_U\to Q_C$, take $B=R^*(b)$, which is closed. If $w\in R^*(b)$, closure gives $u\in R^*(b)$; otherwise $Q_U$ applies. For $Q_C\to Q_U$, a closed $B\ni b$ contains $R^*(b)$, so uniformity of $B$ passes to the cone, and then $u\in R^*(b)\subseteq B$.

Prior art: unchecked

### Provenance

- run: 20261023-0556
- claim: K17
- author: pr (claude)
- round: 17
- run-folder commit: ade4f20858f2a3b683193e13de0d89273d57c4c9
- check results: K17-1.json, K17-2.json, K17-3.json, K17-4.json, K17-5.json, K17-6.json, K17-7.json, K17-8.json

## References

1. <!-- cite:benzmueller2026nominals --> Benzm\"uller, Christoph. 2026. Proofs Without Nominals: G\"odel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes. [Link](https://arxiv.org/abs/2609.36279v4)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-24 — readable prior-art section
