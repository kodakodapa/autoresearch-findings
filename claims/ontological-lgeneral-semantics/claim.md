# A complete calculus for the ℒ-general models of the ontological argument

Cite as: https://doi.org/10.5281/zenodo.23795768

<!-- owner-summary -->
## Setting

Benzmüller's *Proofs Without Nominals* [1] (v4) judges proofs in the
shallow embedding of higher-order modal logic against $\mathcal L$-*general models*: Henkin-style
models whose carriers are closed under the terms of the modal object language $\mathcal L$. Its
Proposition prop:lgeneral gives soundness over these models for proofs meeting a *whole-term*
condition; its Example ex:separating gives a sentence of $\mathcal L$,
$\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$, that the embedding proves but the condition
excludes, formalised in its propositional part only. v4 leaves open whether its weaker *witness
criterion* alone implies the condition, and whether a separating model exists for any of its
axiom sets. This finding makes that semantics machine-checked.

## Result

- **A sound and complete calculus.** A deep natural-deduction calculus for the embedding's
  higher-order logic, with ∀E/∃I instances restricted to $\mathcal L$-terms and Leibniz
  substitution at every type of $\mathcal L$, is sound over v4's $\mathcal L$-general models
  with nonempty individuals, and complete: for every $\mathcal L$-theory $T$ and sentence
  $\varphi$, $\varphi$ holds in all such models of $T$ exactly when the calculus derives it from
  $T\cup\{\exists x.\top\}$. Löwenheim–Skolem and compactness follow: for theories containing
  $\exists x.\top$, a failure has a countermodel with countably many worlds and countable
  carriers, and every consequence follows from a finite sub-theory.
- **prop:lgeneral in deep form.** Leibniz with whole-term motives and $\mathcal L$-term sides
  derives the same sentences, and unrestricted Leibniz derives the separating sentence from any
  theory, so the motive clause is what keeps the calculus sound.
- **ex:separating at all types.** v4's flip model (total frame on $2^{\mathbb N}$, one
  individual, empty positivity) is $\mathcal L$-general at every type of $\mathcal L$ and refutes
  the separating sentence at every world. A model of variant 2 (Ax1Gen, Ax2a, Ax2b, Ax3, Ax4),
  with modal collapse and a God-like being, also refutes it at every world: a separating model
  for one of v4's axiom sets. With finitely many worlds the sentence always holds, so such a
  model needs infinitely many.
- **The equivalence, semantically.** In every $\mathcal L$-general model of variant 2 or 3′
  (Ax2a, Ax2b, $P\,E$, Ax4, $\exists x.\top$), Ax1GenTwo holds everywhere exactly when
  unrestricted Ax1Gen does, and then modal collapse and a God-like being follow (in variant 2
  with Ax3).
- **The witness criterion does not suffice in practice.** A Lean proof of the separating
  sentence in v4's own `Ax1GenTwoVariant2` module, which uses the nominal $\lambda u.\,u=w$ only
  as an argument of `congrFun`, passes v4's `hybrid_check.py` with no flags in both witness and
  whole-term mode. The sentence fails in the variant-2 model above, so the detector certifies a
  proof of a sentence that is not a consequence over $\mathcal L$-general models.

## Prior work

Soundness over $\mathcal L$-general models for whole-term proofs is v4's Proposition
prop:lgeneral, proved there in prose; here it is a Lean theorem about an explicit calculus. The
separating sentence is in substance the world-proposition axiom of Fine and Kaplan
[2]: some true proposition entails every truth. Its failure in atomless
algebras is known for S5 with propositional quantifiers [3], finite-support
(Fraenkel–Mostowski) constructions of Henkin models are standard [4], and
compactness and Löwenheim–Skolem for intensional general models follow Muskens's pattern
[5]. Existing completeness theorems for the embedding are relative to
Henkin models [6], whose domains contain every singleton, so they are
not $\mathcal L$-general. We found no statement of completeness over $\mathcal L$-general
models, of a separating model for one of v4's axiom sets, or of the detector result.

## Why it matters

The first four items settle, inside Lean, the semantic question v4 states as open, and they
give the detector-certified proofs on this site a meaning: a whole-term proof is true in every
$\mathcal L$-general model. The last item shows that the detector's implementation can miss a
nominal hidden in a motive, which is the case v4's open question asks about. It does not refute
Proposition prop:lgeneral, which holds; it shows that certifying proofs with the detector is
not yet a substitute for the semantic proof.

## Proved vs checked

Every claim except the detector result is a Lean 4 theorem (core library, axioms propext,
Classical.choice and Quot.sound only), kernel-checked in the library build. The detector result
is a Lean proof plus a run of v4's `hybrid_check.py` on it; the run's skeptic found it and we
reproduced it outside the run. Its status is *derived* because the detector run is a check, not
a Lean theorem.
<!-- /owner-summary -->

This result extends:

- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4, Prop. prop:lgeneral with Def. def:lgeneral: soundness of HOL proofs over 𝓛-general models, under a stronger whole-term hypothesis (every term used as an element of an 𝓛-domain is an 𝓛-term). It uses the same relativisation and covers the same Leibniz case. The proof is informal and not mechanised, and there is no deep ND. The paper leaves the instance-only (witness) version open.
- Benzmüller, "Gödel's and Scott's variants … in Lean 4 and TPTP THF", arXiv 2609.26806 v3, Section sec:axioms: states without proof that results whose instantiations are object-language terms hold in all models closed under the object-language operations.
- Hetzl, "Higher-Order Logic" lecture notes, https://dmg.tuwien.ac.at/hetzl/teaching/hol.20190125.pdf: Henkin structures as prestructures closed under definability, and Henkin soundness of the calculus (generic HOL, not the modal embedding).
- Stanford Encyclopedia of Philosophy, "Second-order and Higher-order Logic", https://plato.stanford.edu/archIves/spr2010/entries/logic-higher-order/: general structures closed under definability, where the comprehension axioms hold.
- van Benthem, "Changing a semantics: opportunism or courage?", https://arxiv.org/pdf/1411.7636: predicative or restricted comprehension goes naturally with Henkin-style models.
- Benzmüller & Kirchner, "Monadic Second-Order Logic in HOL: Deep and Shallow with Automated Faithfulness", https://arxiv.org/abs/2609.07345: mechanised deep/shallow faithfulness against comprehension-closed vs general MSO readings. There is no restricted-instance ND soundness and no primitive equality.
- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4, https://arxiv.org/abs/2609.36279: soundness over 𝓛-general models for whole-term 𝓛-proofs (Prop. prop:lgeneral). Hybrid-free derivations of ∃^E G and MC under Ax1GenTwo, Ax2a, Ax3 and Ax4 (Thm. thm:gextwo, Cor. cor:gextwo, Thm. thm:plain). G_ex from Ax1Gen, Ax2a, Ax4 and L (Thm. thm:gex). Ax1GenTwo ⇒ Ax1Gen is proved only with nominals and is stated as open without them (Sect. sec:plain, sec:open).
- Benzmüller, "Gödel's and Scott's Variants … in Lean 4 and TPTP THF", arXiv 2609.26806 v3, https://arxiv.org/abs/2609.26806: notes that its object-language-only instantiations make the port's bounds hold in every model closed under the object-language operations. This is informal; there is no theorem.
- Benzmüller & Scott, "Notes on Gödel's and Scott's variants…", Monatshefte 2025, https://link.springer.com/article/10.1007/s00605-025-02078-x: the source variants, with Ax1Gen, MC and G_ex proved over full/Henkin semantics only.
- C. Benzmüller, "Proofs Without Nominals", arXiv 2609.36279v4 (sources/2609.36279/v4/main.tex). `def:lgeneral` and `prop:lgeneral` give soundness over 𝓛-closed models, with equality read as agreement on P and functions extended by restriction (the respect-eqT idea, assumed rather than separated). `ex:separating` gives the FM flip model on 2^ℕ refuting A∃p.(Atom p ∧ p). There is no non-respecting counterexample, no Leibniz rule at every type, and no rel-self-related carriers.
- P. B. Andrews, "General models and extensionality", JSL 37(2) 1972, https://doi.org/10.2307/2272982. A general model in which Leibniz-stated extensionality fails because the sets are sparse. This is the classical form of the K3 phenomenon.
- C. Benzmüller, C. E. Brown, M. Kohlhase, "Higher-order semantics and extensionality", JSL 69(4) 2004, https://projecteuclid.org/journals/journal-of-symbolic-logic/volume-69/issue-4/Higher-order-semantics-and-extensionality/10.2178/jsl/1102022211.short. Model classes with and without functional extensionality, property q, and Leibniz versus primitive equality. This is the general framework for K3/K4.
- W. Degen & J. Johannsen, "Cumulative Higher-Order Logic as a Foundation for Set Theory", https://www.ifi.lmu.de/institut/personen/jjohannsen/jj_papers/kumlog.pdf. A quotient of Henkin structures under Leibniz equality, related to the self-related/collapse construction in K6.
- P. Fritz, "Propositional Quantifiers" (Cambridge Element), https://philpapers.org/rec/FRIPQC, and "Nonconservative extensions by propositional quantifiers…", https://academic.oup.com/logcom/advance-article/doi/10.1093/logcom/exae043/7724499. Quantifiable general frames (domains closed under definable formulas) for propositionally quantified modal logic. This covers only the propositional level of the 𝓛-closure condition.
- C. Benzmüller, "Proofs Without Nominals …", https://arxiv.org/abs/2609.36279 (v4), Example ex:separating: an atomless L-general model on 2^N (total frame, empty positivity, one individual) in which A∃p.(Atom p ∧ p) fails everywhere, formalised in Isabelle and Lean (propositional part). The paper states that this model is not a variant-2 model, and lists as open whether a separating model exists for any of the variants' axioms. K7 fills that gap for variant 2 (identity frame).
- Same paper, Proposition prop:lgeneral: soundness of proofs meeting the whole-term criterion over L-general models. This is the tool that turns K7's model into "underivable in the calculus".
- Some General Completeness Results for Propositionally Quantified Modal Logics, https://arxiv.org/html/2406.16034: atomless principle under bisimulation quantifiers and atomic general frames. General PQML background, not the ontological axioms.
- B. ten Cate (2006), cited in the source: expressing nominal-free hybrid ↓/@ sentences with propositional quantifiers. Expressivity background only.
- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4 (sources/2609.36279/v4/main.tex): defines $\mathcal L$-general models (def:lgeneral) and proves soundness over them for HOL proofs meeting the whole-term condition (prop:lgeneral), which is a closely related analogue of K9. Gives the FM separating model (ex:separating), which is the method behind K8, but states that it is not a model of variant 2. Lists the existence of a separating model of any variant, and a hybrid-free Ax1GenTwo ⇔ Ax1Gen, as open (sec:open).
- Benzmüller & Kirchner, "First-Order Modal Logic in HOL: deep and shallow embeddings with automated faithfulness", https://arxiv.org/pdf/2607.10880: deep/shallow faithfulness for first-order modal logic only. No propositional quantification, so no $\mathcal L$-general models.
- Muskens, "Higher Order Modal Logic", https://philarchive.org/archive/MUSHOM: general frames ⟨W,R,Π⟩ with Π a Boolean-closed subset of P(W), the standard background for general models of propositional quantification.
- Fritz & Bacon, "The Algebra of Logical Atomism", https://andrew-bacon.github.io/papers/The%20Algebra%20of%20Logical%20Atomism.pdf: algebraic treatment of atomicity of propositions in higher-order logic, background for the role of atomless models.
- C. Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4, https://arxiv.org/abs/2609.36279:.
- C. Benzmüller, "Gödel's and Scott's Variants … in Lean 4 and TPTP THF", arXiv 2609.26806, https://arxiv.org/abs/2609.26806: shows that the proofs draw on the degenerate instances of Ax1Gen (empty and singleton conjunctions). It does not treat Ax1GenTwo.
- C. Benzmüller & D. Scott, "Notes on Gödel's and Scott's variants of the ontological argument", Monatshefte für Mathematik 2025, https://link.springer.com/article/10.1007/s00605-025-02078-x: source of Ax1Gen and variants 2 and 3; it has no two-conjunct reading.
- K. Fine, "Propositional quantifiers in modal logic", Theoria 36 (1970), and D. Kaplan (1970): introduce the world-proposition axiom (W) for S5 with propositional quantifiers. It is the S5 counterpart of A∃p.(Atom p ∧ p).
- W. H. Holliday, "A Note on Algebraic Semantics for S5 with Propositional Quantifiers", NDJFL 60(2) 2019, https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-60/issue-2/A-Note-on-Algebraic-Semantics-for-S5-with-Propositional-Quantifiers/10.1215/00294527-2019-0001.full: (W) characterises complete atomic algebras, and ¬(W) characterises complete atomless ones. This covers the "atom sentence fails exactly in atomless models" core in the S5 setting.
- Ding & Li (as given in search results), "Some General Completeness Results for Propositionally Quantified Modal Logics", https://arxiv.org/html/2406.16034v1: discusses the atomicity principle and the atomless principle on general frames versus Kripke frames. It notes that Kripke frames validate atomicity.
- P. Fritz, *Propositional Quantifiers* (Cambridge Elements 2024), https://philpapers.org/rec/FRIPQC, and "Axiomatizability of PQML on relational frames", JSL 2024: survey world propositions and atomicity, including Fine's observation that propositional quantifiers can express "true at exactly one accessible world".
- R. Muskens, "Higher Order Modal Logic", https://philarchive.org/archive/MUSHOM: notes that in Henkin-style modal models singletons {w} may be absent, and that nominals enforce their definability. This is the gap the flip model exploits.
- SEP, "Second-order and Higher-order Logic", https://plato.stanford.edu/entries/logic-higher-order/: describes the Fraenkel–Mostowski method as a standard construction of Henkin models. It is the method the flip model uses, though not applied there to modal worlds.
- B. ten Cate (2006), cited in the source: expressing nominal-free hybrid sentences with propositional quantifiers. This is the related expressivity background named in `sec:criterion-open`.
- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 (v4, `prop:lgeneral`, `ex:separating`): the soundness direction of K12 over L-general models, plus a separating example. It explicitly does not prove completeness.
- Benzmüller & Paulson, "Quantified Multimodal Logics in Simple Type Theory", Logica Universalis 7 (2013), https://arxiv.org/abs/0905.2435: soundness and completeness of the HOML shallow embedding relative to Henkin models, not L-general models. 2609.36279 notes the theorem needs a closure clause.
- Gallin, *Intensional and Higher-Order Modal Logic* (North-Holland 1975): Henkin-style completeness of an axiomatised intensional higher-order logic over general models. It is an object-level calculus, not the embedding fragment.
- Muskens, "Higher Order Modal Logic", https://semanticsarchive.net/Archive/WQ0ODMxM/homl.pdf: generalized completeness of MTT over intensional (general) models via model existence, building on Fitting's intensional type theory.
- Areces, Blackburn, Huertas, Manzano, "Completeness in Hybrid Type Theory", https://www.researchgate.net/publication/235801245_Completeness_in_Hybrid_Type_Theory: Henkin completeness for higher-order modal logic with nominals and @, i.e. with exactly the resources K12's calculus excludes.
- Benzmüller & Kirchner, arXiv 2607.10880 and AFP MSOinHOL (2026): mechanised deep↔shallow faithfulness for first-order modal logic and for MSO. The MSO entry identifies range-relative validity with general (Henkin) semantics, an analogue for a non-modal second-order language.
- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279v4 (sources/…/v4/main.tex): this is the source of K14's finite-worlds half (remark in `ex:separating`). It gives an atomless separating model that is not a model of variant 2, and `sec:open` leaves the variant-2 case open. It proves soundness over L-general models but no compactness or Löwenheim–Skolem theorem.
- R. Muskens, "Intensional Models for the Theory of Types", https://arxiv.org/abs/math/0608571: generalised compactness and countable-model Löwenheim–Skolem for intensional general models of type theory. This is the K13 pattern for a different model class.
- D. Gallin, *Intensional and Higher-Order Modal Logic* (1975), via Muskens, https://philarchive.org/archive/MUSHOM: Henkin-style completeness for higher-order modal logic, from which compactness and Löwenheim–Skolem follow.
- K. Fine, "Propositional Quantifiers in Modal Logic", Theoria 1970, https://onlinelibrary.wiley.com/doi/abs/10.1111/j.1755-2567.1970.tb00432.x: propositional quantifiers over arbitrary Boolean algebras of sets of worlds, and an atom formula. Covers the propositional analogue relevant to K13 and K14.
- Y. Ding, "On the Logics with Propositional Quantifiers Extending S5Π", AiML 12 (2018), https://philarchive.org/archive/DINOTL: atomless S5 algebras falsify ∃p(p ∧ atom p), while Kripke (full) frames force it. This is the propositional, axiom-free analogue of K14.
- Benzmüller, "Proofs Without Nominals", arXiv 2609.36279 v4, Proposition prop:lgeneral: soundness of HOL proofs meeting a whole-term L-term condition (motives and equation sides included) over L-general models. This is essentially K15. Example ex:separating separates unrestricted HOL provability from L-general validity. There is no completeness result, and the question is listed as open.
- Benzmüller & Paulson, "Quantified Multimodal Logics in Simple Type Theory", Logica Universalis 2013, https://arxiv.org/abs/0905.2435: the embedding is sound and complete with respect to Henkin semantics, not L-general models.
- D. Gallin, Intensional and Higher-Order Modal Logic (1975): an axiom system for intensional logic, complete for Henkin-style general models. It is an object-level analogue of one leg of K16.
- M. Fitting, Types, Tableaus, and Gödel's God (2002), https://link.springer.com/book/10.1007/978-94-010-0411-4: tableau completeness for (generalised) Henkin models of classical and intensional type theory.
- R. Muskens, "Higher Order Modal Logic" (Handbook of Modal Logic, 2007), https://philarchive.org/archive/MUSHOM: general models ⟨W,R,Π⟩ with Π⊆P(W), and generalised completeness. It notes that singletons may fail to exist in such models.
- Benzmüller & Kirchner, arXiv 2607.10880: deep↔shallow faithfulness for first-order modal logic only, where the singleton issue does not arise.
- C. Benzmüller, "Proofs Without Nominals …", arXiv 2609.36279 v4, https://arxiv.org/abs/2609.36279: the same sentence φ; a separating atomless L-general model for the empty theory, not for variant 2; soundness with a whole-term (motive-inclusive) clause (prop:lgeneral); the witness-only and variant-2 questions stated as open.
- C. Benzmüller, "Gödel's and Scott's Variants … in Lean 4 and TPTP THF", arXiv 2609.26806 v3: the Lean port; no L-general semantics.
- Y. Ding & Y. Li, "Some General Completeness Results for Propositionally Quantified Modal Logics", https://arxiv.org/abs/2406.16034: quantifiable general frames; atomicity and atomlessness principles for propositional quantifiers.
- "Discernment is all you need", https://arxiv.org/pdf/2602.20038 (summary only): Andrews' general models in which Leibniz equality is not identity, so Henkin's soundness fails.
- B. ten Cate (2006), cited in v4: nominal-free hybrid sentences expressible with propositional quantifiers over standard models.
- K. Fine, "Propositional quantifiers in modal logic", Theoria 1970, https://philpapers.org/rec/FINPQI: atomicity principle for S5 with propositional quantifiers; non-atomic propositional domains.
- W. H. Holliday, "A Note on Algebraic Semantics for S5 with Propositional Quantifiers", NDJFL 60(2) 2019, https://escholarship.org/uc/item/303338xr: S5Π plus the negation of atomicity is complete for complete atomless algebras. This is the propositional analogue of the claim's model without atoms.
- Y. Ding & W. H. Holliday, "Some General Completeness Results for Propositionally Quantified Modal Logics", https://arxiv.org/html/2406.16034: atomicity principle At^n holds on Kripke frames but not on general frames.
- Y. Ding, "Propositional Quantification and Comparison in Modal Logic" (thesis), https://escholarship.org/uc/item/78w732g8: Π-logics over S5 with and without atomicity.
- C. Gaßner, "Permutation Models of Second Order", https://arxiv.org/html/2409.14211 (and arXiv 2409.10276, 2410.23276): finite-support FM-style Henkin models of second-order logic, following Asser. Same technique, not modal.
- M. J. Gabbay & D. Mulligan, "Nominal Henkin Semantics", https://arxiv.org/pdf/1111.0089: Henkin models of typed λ-calculus in nominal (finitely supported) sets.
- P. Fritz & A. Bacon, "The Algebra of Logical Atomism", RSL, https://andrew-bacon.github.io/papers/The%20Algebra%20of%20Logical%20Atomism.pdf: atomic and atomless propositional algebras extended to higher-order models.
- B. ten Cate 2006 and Kaminski & Tiomkin 1996 (NDJFL 37(1)): expressive power of propositional quantification, which defines atoms and nominals over standard models (the source cites ten Cate).

Our prior-art search (2026-10-22) covered:

- https://arxiv.org/abs/2609.07345 and https://arxiv.org/html/2609.07345 (fetched), 2026-10-22
- I did not open these pages; I used only the search-result summaries: https://dmg.tuwien.ac.at/hetzl/teaching/hol.20190125.pdf, https://plato.stanford.edu/archIves/spr2010/entries/logic-higher-order/, https://philarchive.org/archive/ROSFLSv1, https://arxiv.org/pdf/1411.7636, https://philarchive.org/archive/MUSHOM, https://arxiv.org/pdf/1106.3685, https://arxiv.org/html/2502.19311v2
- I used search-result summaries only for the web hits and did not open those pages; the verdict rests on the files in sources/.
- Result pages seen: https://arxiv.org/abs/2609.36279, https://arxiv.org/pdf/2608.07578, https://arxiv.org/pdf/2607.10880, https://link.springer.com/article/10.1007/s00605-025-02078-x, https://arxiv.org/html/2502.19311v3, https://philarchive.org/archive/MUSHOM, https://andrew-bacon.github.io/papers/The%20Algebra%20of%20Logical%20Atomism.pdf, https://link.springer.com/article/10.1007/s11787-026-00409-6
- I opened no web pages; the web part rests on search-result summaries only.
- Only search-result summaries were available for the web sources. Direct page fetches failed.
- WebFetch: https://isa-afp.org/entries/MSOinHOL.html, 2026-10-22
- The web-search items other than the MSOinHOL page were judged from search-engine summaries only.
- https://arxiv.org/abs/math/0608571: abstract opened, 2026-10-22. The PDF could not be parsed, so its theorem statements are taken from search snippets.
- I used only search-result summaries for the external sources and opened no pages.
- https://arxiv.org/abs/2609.36279 (version history; v4 dated 2026-10-14 is latest), 2026-10-22
- (Other pages were seen only as search-engine summaries: arXiv 2602.20038, 2406.16034, 2104.04284, 2607.10880.)
- I used search-engine results and summaries only. I did not open the external pages in full.

The search was run automatically by claude/claude-opus-5-5.

The checkers' full answers, with every query and file they searched, are published with this finding (`prior-art/`).

If you know of related work we missed, please open an issue.

This result was found by AI research agents (the autoresearch harness). It was partly proved in Lean (claims K1, K2, K3, K4, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16, K17, K18) and partly checked by scripts that run Lean proofs (claims K5); the proof and check files are included so anyone can re-run them.

## K1

Deep ND for the embedding's HOL (𝓛-types, worlds, $o$; Leibniz only where relativised equality is identity): a derivation from 𝓛-sentences $T$ whose ∀E/∃I instances at 𝓛-types are $[\![t]\!]$, $t$ an 𝓛-term, holds in every 𝓛-closed structure of $T$ admitting all entities.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K1-DeepND.lean`: Programme.Run3.HOL.soundness — pass (`results/K1-1.json`)

Prior art: partial prior art (answer: `prior-art/R1.md`)

### Provenance

- run: 20261022-1724
- claim: K1
- author: pr (claude)
- round: 1
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K1-1.json

## K2

Run 2's K1 (TwoClosed: Ax2a, Ax2b, Ax3, Ax4, Ax1GenTwo, $\exists x.\top$ give Ax1Gen, MC, $\exists^E G$) and K14 (GexL: Ax2a, Ax2b, Ax4, $P E_3$, $P G$ give $\exists^E G$, MC) have deep derivations with only 𝓛-term ∀E/∃I instances, so hold in every 𝓛-closed structure admitting all entities.

Status: proved (axioms: propext, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K2-DeepK.lean`: Programme.Run3.Deep.Sem.k1\_derivations — pass (`results/K2-1.json`)
- proof `checks/K2-DeepK.lean`: Programme.Run3.Deep.Sem.k14\_derivations — pass (`results/K2-2.json`)
- proof `checks/K2-DeepK.lean`: Programme.Run3.Deep.Sem.k1\_valid — pass (`results/K2-3.json`)
- proof `checks/K2-DeepK.lean`: Programme.Run3.Deep.Sem.k14\_valid — pass (`results/K2-4.json`)

Prior art: partial prior art (answer: `prior-art/R2.md`)

### Provenance

- run: 20261022-1724
- claim: K2
- author: pr (claude)
- round: 2
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K2-1.json, K2-2.json, K2-3.json, K2-4.json

## K3

There is a closed structure ($W=2^{\mathbb N}$, one entity, identity frame) where $\forall f_1f_2{:}\sigma\to\sigma\,\forall F.\,f_1=f_2\to Ff_1=Ff_2$ fails, so K1's Deriv T Cert does not derive it from the empty theory; it holds in every structure whose admitted functions respect eqT.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K3-LeibnizGap.lean`: Programme.Run3.LeibnizGap.leib\_not\_derivable\_empty — pass (`results/K3-1.json`)
- proof `checks/K3-LeibnizGap.lean`: Programme.Run3.LeibnizGap.closed\_SF — pass (`results/K3-2.json`)
- proof `checks/K3-LeibnizGap.lean`: Programme.Run3.LeibnizGap.leib\_fails — pass (`results/K3-3.json`)
- proof `checks/K3-LeibnizGap.lean`: Programme.Run3.LeibnizGap.leib\_of\_resp — pass (`results/K3-4.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1724
- claim: K3
- author: pr (claude)
- round: 3
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K3-1.json, K3-2.json, K3-3.json, K3-4.json

## K4

Adding Leibniz substitution at every type of $\mathcal L$ (𝓛-motive, 𝓛-term sides) to K1's calculus gives one sound over closed structures admitting all entities whose admitted functions respect eqT; it derives Leibniz at $\sigma\to\sigma$, which fails in a closed non-respecting structure.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K4-DeepLeib.lean`: Programme.Run3.HOLX.soundness — pass (`results/K4-1.json`)
- proof `checks/K4-DeepLeib.lean`: Programme.Run3.HOLX.fund — pass (`results/K4-2.json`)
- proof `checks/K4-DeepLeib.lean`: Programme.Run3.HOLX.leib\_derivable — pass (`results/K4-3.json`)
- proof `checks/K4-DeepLeib.lean`: Programme.Run3.HOLX.Flip.resp\_needed — pass (`results/K4-4.json`)
- proof `checks/K4-DeepLeib.lean`: Programme.Run3.HOLX.full\_closed\_resp — pass (`results/K4-5.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1724
- claim: K4
- author: pr (claude)
- round: 3
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K4-1.json, K4-2.json, K4-3.json, K4-4.json, K4-5.json

## K6

`For every flip-style Sym, carriers 'supported and rel-self-related' are closed under all full-L terms, validate Leibniz at all types, and agree with support carriers at σ,τ,τ→σ; v4's separating model refutes A∃p.(Atom p∧p).`

Status: proved (axioms: propext, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K6-Respect.lean`: Programme.Run3.Respect.closedR — pass (`results/K6-1.json`)
- proof `checks/K6-Respect.lean`: Programme.Run3.Respect.leibnizR — pass (`results/K6-2.json`)
- proof `checks/K6-Respect.lean`: Programme.Run3.Respect.lgenFR\_of\_sym — pass (`results/K6-3.json`)
- proof `checks/K6-Respect.lean`: Programme.Run3.Respect.Sep.separating\_all\_types — pass (`results/K6-4.json`)

Prior art: partial prior art (answer: `prior-art/R3.md`)

### Provenance

- run: 20261022-1724
- claim: K6
- author: r1 (claude)
- round: 3
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K6-1.json, K6-2.json, K6-3.json, K6-4.json

## K7

$W=2^{\mathbb N}$, identity frame, one entity, $P\varphi w=\varphi()w$, K6's extensional carriers: a closed eqT-respecting structure satisfies variant 2 (Ax1Gen, Ax2a, Ax2b, Ax3, Ax4) and MC, yet $\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$ fails everywhere; K4's calculus cannot derive it.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K7-SepV2.lean`: Programme.Run3.SepV2.V2.sep\_v2 — pass (`results/K7-1.json`)
- proof `checks/K7-SepV2.lean`: Programme.Run3.SepV2.V2.sep\_not\_derivable — pass (`results/K7-2.json`)
- proof `checks/K7-SepV2.lean`: Programme.Run3.SepV2.V2.resp\_symId — pass (`results/K7-3.json`)

Prior art: partial prior art (answer: `prior-art/R4.md`)

### Provenance

- run: 20261022-1724
- claim: K7
- author: pr (claude)
- round: 4
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K7-1.json, K7-2.json, K7-3.json

## K8

There is a v4 $\mathcal L$-general model ($W=2^{\mathbb N}$, identity frame, one entity, $P\varphi w=\varphi()w$; eqT-quotient of K7's structure) of variant 2 (Ax1Gen, Ax2a, Ax2b, Ax3, Ax4), with MC and $\exists^E G$, in which $\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$ fails at every world.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K8-DeepV4.lean`: Programme.Run3.SepV2.V2.sep\_v4 — pass (`results/K8-1.json`)
- proof `checks/K8-DeepV4.lean`: Programme.Run3.SepV2.V2.sep\_not\_valid\_v4 — pass (`results/K8-2.json`)

Prior art: partial prior art (answer: `prior-art/R5.md`)

### Provenance

- run: 20261022-1724
- claim: K8
- author: pr (claude)
- round: 5
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K8-1.json, K8-2.json

## K9

A deep derivation of $\varphi$ from $\mathcal L$-theory $T$ in K4's certified calculus makes $\varphi$ true in every v4 $\mathcal L$-general model of $T$ with nonempty individuals; so run 2's K1 (variant 2: Ax1GenTwo gives Ax1Gen, MC, $\exists^E G$) and K14 hold in all such models.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K8-DeepV4.lean`: Programme.Run3.V4.sound\_v4 — pass (`results/K9-1.json`)
- proof `checks/K8-DeepV4.lean`: Programme.Run3.V4.k1\_valid\_v4 — pass (`results/K9-2.json`)
- proof `checks/K8-DeepV4.lean`: Programme.Run3.V4.k14\_valid\_v4 — pass (`results/K9-3.json`)
- proof `checks/K8-DeepV4.lean`: Programme.Run3.LX.valid\_iff — pass (`results/K9-4.json`)

Prior art: partial prior art (answer: `prior-art/R5.md`)

### Provenance

- run: 20261022-1724
- claim: K9
- author: pr (claude)
- round: 5
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K9-1.json, K9-2.json, K9-3.json, K9-4.json

## K10

In every v4 $\mathcal L$-general model where Ax2a, Ax2b, $P\,E$, plain Ax4 and $\exists x.\top$ hold at all worlds ($E$ the necessary existence of variant 2, resp. 3′), Ax1GenTwo holds everywhere iff Ax1Gen does; with Ax1GenTwo, MC and $\exists^E G$ hold everywhere (variant 3′).

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K10-DeepE.lean`: Programme.Run3.V4.two\_equivalent\_v3p — pass (`results/K10-1.json`)
- proof `checks/K10-DeepE.lean`: Programme.Run3.V4.two\_equivalent\_v2 — pass (`results/K10-2.json`)
- proof `checks/K10-DeepE.lean`: Programme.Run3.V4.k3p\_valid\_v4 — pass (`results/K10-3.json`)
- proof `checks/K10-DeepE.lean`: Programme.Run3.Conv.two\_of\_gen — pass (`results/K10-4.json`)

Prior art: partial prior art (answer: `prior-art/R6.md`)

### Provenance

- run: 20261022-1724
- claim: K10
- author: pr (claude)
- round: 6
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K10-1.json, K10-2.json, K10-3.json, K10-4.json

## K11

$\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$ holds in v4 $\mathcal L$-general models with finitely many worlds or all singletons; universal frame plus $T_2$ gives only $\emptyset,W$; a flip model (universal frame, one entity, empty Pos, K6 carriers mod eqT) is $\mathcal L$-general, refutes both.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K11-DeepSep.lean`: Programme.Run3.SepR.sep\_finite — pass (`results/K11-1.json`)
- proof `checks/K11-DeepSep.lean`: Programme.Run3.SepR.sep\_singletons — pass (`results/K11-2.json`)
- proof `checks/K11-DeepSep.lean`: Programme.Run3.SepR.v2\_universal\_trivial — pass (`results/K11-3.json`)
- proof `checks/K11-DeepSep.lean`: Programme.Run3.SepR.not\_v2\_of\_contingent — pass (`results/K11-4.json`)
- proof `checks/K11-DeepSep.lean`: Programme.Run3.SepR.sep\_example\_v4 — pass (`results/K11-7.json`)
- reasoning: Narrowing of the last clause to the model actually built in DeepSep.lean (sep\_example\_v4); first two clauses unchanged and verified by the skeptic.

Prior art: partial prior art (answer: `prior-art/R7.md`)

### Provenance

- run: 20261022-1724
- claim: K11
- author: pr (claude)
- round: 10
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K11-1.json, K11-2.json, K11-3.json, K11-4.json, K11-7.json

## K12

For every $\mathcal L$-theory $T$ and $\mathcal L$-sentence $\varphi$: $\varphi$ holds in all v4 $\mathcal L$-general models of $T$ with nonempty individuals iff K4's certified calculus derives $[\![\varphi]\!]$ at a world variable from $T\cup\{\exists x.\top\}$.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K12-Canon.lean`: Programme.ThCanon.sound\_complete\_all — pass (`results/K12-1.json`)
- proof `checks/K12-Canon.lean`: Programme.ThCanon.completeness — pass (`results/K12-2.json`)
- proof `checks/K12-Canon.lean`: Programme.ThCanon.sound\_complete\_str — pass (`results/K12-3.json`)

Prior art: partial prior art (answer: `prior-art/R8.md`)

### Provenance

- run: 20261022-1724
- claim: K12
- author: pr (claude)
- round: 8
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K12-1.json, K12-2.json, K12-3.json

## K13

Over v4 $\mathcal L$-general models with nonempty individuals: if $\exists x.\top\in T$ and $\varphi$ fails in a model of $T$, it fails in one with countably many worlds and countable carriers at every type; and if $T\models\varphi$, then $T_0\models\varphi$ for some finite $T_0\subseteq T$.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K13-LS.lean`: Programme.ThCanon.lowenheim\_skolem — pass (`results/K13-1.json`)
- proof `checks/K13-LS.lean`: Programme.ThCanon.valid\_iff\_ctbl — pass (`results/K13-2.json`)
- proof `checks/K13-LS.lean`: Programme.ThCanon.compactness — pass (`results/K13-3.json`)
- proof `checks/K13-LS.lean`: Programme.ThCanon.Deriv.finite — pass (`results/K13-4.json`)

Prior art: partial prior art (answer: `prior-art/R9.md`)

### Provenance

- run: 20261022-1724
- claim: K13
- author: pr (claude)
- round: 9
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K13-1.json, K13-2.json, K13-3.json, K13-4.json

## K14

A v4 $\mathcal L$-general model of variant 2 (Ax1Gen, Ax2a, Ax2b, Ax3, Ax4), nonempty individuals, countable worlds and carriers, infinitely many worlds refutes $\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$ at a world; every $\mathcal L$-general model with finitely many worlds satisfies it.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K14-SepLS.lean`: Programme.Run3.SepLS.sep\_threshold — pass (`results/K14-1.json`)

Prior art: partial prior art (answer: `prior-art/R9.md`)

### Provenance

- run: 20261022-1724
- claim: K14
- author: pr (claude)
- round: 9
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K14-1.json

## K15

In K4's HOL ($\mathcal L$-types, $w$, $o$), derivations from $\mathcal L$-theory $T$ with Leibniz at any type and motive are sound in v4 $\mathcal L$-general models of $T$ (nonempty individuals) if ∀E/∃I instances are $\mathcal L$-terms and non-plain Leibniz has WT motives, $\mathcal L$-term sides.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K15-WholeTerm.lean`: Programme.ThWhole.sound\_v4\_wt — pass (`results/K15-1.json`)
- proof `checks/K15-WholeTerm.lean`: Programme.ThWhole.of\_DC — pass (`results/K15-2.json`)
- proof `checks/K15-WholeTerm.lean`: Programme.ThWhole.cong — pass (`results/K15-3.json`)
- reasoning: Wording narrowed to K4's HOL per the skeptic; Lean evidence unchanged.

Prior art: partial prior art (answer: `prior-art/R10.md`)

### Provenance

- run: 20261022-1724
- claim: K15
- author: pr (claude)
- round: 10
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K15-1.json, K15-2.json, K15-3.json

## K16

In K4's HOL ($\mathcal L$-types, $w$, $o$), for $\mathcal L$-theory $T$: WT Leibniz (any type, WT motives, $\mathcal L$-term sides) derives $[\![\varphi]\!]$ from $T+\exists x.\top$ iff K4's calculus does iff $\varphi$ holds in all v4 $\mathcal L$-general models of $T$ (nonempty individuals).

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K15-WholeTerm.lean`: Programme.ThWhole.wt\_sound\_complete — pass (`results/K16-1.json`)
- reasoning: Scope wording only; Lean evidence wt\_sound\_complete unchanged.
- reasoning: Wording narrowed to K4's HOL per the skeptic; Lean evidence unchanged.

Prior art: partial prior art (answer: `prior-art/R10.md`)

### Provenance

- run: 20261022-1724
- claim: K16
- author: pr (claude)
- round: 10
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K16-1.json

## K17

In K4's HOL (types of $\mathcal L$, $w$, $o$), rules with $\mathcal L$-term ∀E/∃I instances and unrestricted Leibniz derive $\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$ from any theory; it fails in a v4 $\mathcal L$-general model of variant 2. Adding the motive clause restores soundness.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K17-WitnessDeep.lean`: Programme.ThWit.witness\_alone\_unsound — pass (`results/K17-1.json`)
- proof `checks/K17-WitnessDeep.lean`: Programme.ThWit.sep\_deep — pass (`results/K17-2.json`)
- proof `checks/K17-WitnessDeep.lean`: Programme.ThWit.step\_profile — pass (`results/K17-3.json`)

Prior art: partial prior art (answer: `prior-art/R11.md`)

### Provenance

- run: 20261022-1724
- claim: K17
- author: pr (claude)
- round: 11
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K17-1.json, K17-2.json, K17-3.json

## K18

v4's flip model (total frame on $2^{\mathbb N}$, one individual, empty Pos, hereditarily FS carriers $P_\tau$, every type of $\mathcal L$) is $\mathcal L$-general; $P_\sigma$ = finitary sets, has no singletons, and $\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$ fails at every world.

Status: proved (axioms: propext, Classical.choice, Quot.sound)

Kind: theorem

Evidence:
- proof `checks/K18-FMAll.lean`: Programme.ThFM.sep\_all\_types — pass (`results/K18-1.json`)
- proof `checks/K18-FMAll.lean`: Programme.ThFM.fmL — pass (`results/K18-2.json`)
- proof `checks/K18-FMAll.lean`: Programme.ThFM.carrier\_s — pass (`results/K18-3.json`)
- proof `checks/K18-FMAll.lean`: Programme.ThFM.sep\_not\_valid\_empty — pass (`results/K18-4.json`)

Prior art: partial prior art (answer: `prior-art/R12.md`)

### Provenance

- run: 20261022-1724
- claim: K18
- author: pr (claude)
- round: 12
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K18-1.json, K18-2.json, K18-3.json, K18-4.json

## K5

A Lean proof of v4's separating sentence $\mathsf A\exists p.(\mathsf{Atom}\,p\wedge p)$ in the shallow embedding of OpenQuestions.Ax1GenTwoVariant2, using the nominal $\lambda u.\,u=w$ only as an argument of congrFun, passes hybrid_check.py with 0 flags in witness and whole-term mode.

Status: derived · author check only

Kind: model

Evidence:
- check `checks/K5-witness_gap.py`: module proving the separating sentence builds without sorry, axioms \[i, propext, Classical.choice, Quot.sound\]; hybrid\_check.py reports PASS, witness-mode hybrid 0, whole-term flagged 0, EXTRA 0 — pass (`results/K5-1.json`)

Prior art: unchecked

### Provenance

- run: 20261022-1724
- claim: K5
- author: pr (claude)
- round: 3
- run-folder commit: 2537c3c1e409694e656412ead00d75260626d0fb
- check results: K5-1.json

## References

1. <!-- cite:benzmueller2026nominals --> Benzm\"uller, Christoph. 2026. Proofs Without Nominals: G\"odel's Ontological Argument, its Shallow Embedding, and the Open Questions of the Monatshefte Notes. [Link](https://arxiv.org/abs/2609.36279v4)
2. <!-- cite:fine1970propositional --> Fine, Kit. 1970. Propositional Quantifiers in Modal Logic. Theoria
3. <!-- cite:holliday2019note --> Holliday, Wesley H.. 2019. A Note on Algebraic Semantics for S5 with Propositional Quantifiers. Notre Dame Journal of Formal Logic
4. <!-- cite:gabbay2011nominal --> Gabbay, Murdoch J. and Mulligan, Dominic P.. 2011. Nominal Henkin Semantics: simply-typed lambda-calculus models in nominal sets. [Link](https://arxiv.org/abs/1111.0089)
5. <!-- cite:muskens2007intensional --> Muskens, Reinhard. 2007. Intensional Models for the Theory of Types. Journal of Symbolic Logic. [Link](https://arxiv.org/abs/math/0608571)
6. <!-- cite:benzmueller2013quantified --> Benzm\"uller, Christoph and Paulson, Lawrence C.. 2013. Quantified Multimodal Logics in Simple Type Theory. Logica Universalis. [Link](https://arxiv.org/abs/0905.2435)

<!-- autoresearch:revisions -->
## Revisions

- 2026-10-24 — readable prior-art section
