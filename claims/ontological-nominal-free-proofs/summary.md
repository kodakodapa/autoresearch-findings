## Setting

Benzmüller and Scott's *Notes* prove variants of Gödel's ontological argument in a shallow
embedding of higher-order modal logic in classical higher-order logic [@benzmueller2025notes].
Benzmüller's *Proofs Without Nominals* [@benzmueller2026nominals] (v4) points out that the
embedding's quantifiers also range over *nominals*, properties like $\lambda u.\,u = w$ that pick
out a single world. A proof that substitutes one proves a theorem of the embedding but not
necessarily of the modal object language $\mathcal L$. v4 ships a detector that flags such
"hybrid" proofs in two modes (witness and whole-term), and lists the theorems of its Lean
modules it could only prove with a flagged step, among them two of its stated open questions:
whether the equivalence of the restricted conjunction axiom Ax1GenTwo with the unrestricted
Ax1Gen has a nominal-free proof in variants 2 and 3′, and whether Gödel's lemma L follows under
the rigid reading Ax1GenR with no condition on positivity.

## Result

For each flagged theorem below we give a new proof of the *identical* statement, from the same
module's definitions, that v4's own detector passes in both modes (full names):

- **The equivalence question:** `Ax1Gen_of_Two` and `Two_equivalent`, with `P_of_conj`,
  `loc_of_conj` and the related lemmas, in `Ax1GenTwoVariant2` and `Ax1GenTwoVariant3Plain`
  (logic K).
- **The rigid question:** `L_R` in `Ax1GenRigidVariant2`, from Ax2a, Ax2b and Ax4 only, with
  witness `PosGlobal` and no condition on positivity.
- **Further flagged theorems:** modal collapse and Th5 in `Ax1GenBoxVariant3` (the reflexivity
  hypothesis unused); fourteen theorems of `GoedelVariantHOML3inS4oneFile` without `Rrefl` or
  `Rtrans`; the one-conjunct theorems of `Ax1GenOneVariant3`; collapse and the existence
  theorems of `Ax1GenTwoVariant3` and `Ax1GenTwoVariant3Th4`; `AllExist` and `MC_OneWorld` of
  `Ax1GenTwoVariant3Plain`; and collapse in its possibilist and Anderson-quantifier versions.
- **A model:** on two worlds with one always-actual entity and a universal frame, Ax1, Ax2a,
  Ax2b, Ax3, both forms of Ax4, Ax1Gen with its Two, One and Box restrictions, and Th4 hold, and necessary
  existence holds at both worlds, so `NoNecExist` fails there; and an
  abstract Henkin lemma describing what Ax1GenR forces over admitted rigid families.

## What is new

v4 already has nominal-free proofs of two of the lemmas listed first (`ae_Two` and
`G_ex_Two_unconditional`, under those names), and frame-free `_K` versions of most theorems of
`GoedelVariantHOML3inS4oneFile`; what this finding adds there are proofs under the original names
that the detector passes, and nominal-free routes to `EssSupp`, `EssDetermined` and `AllExist`.
The new results are the equivalence lemmas, which v4 proves only through the nominal arguments
`OneWorld` and `R_Id` and lists as open, and `L_R` with no condition on positivity, also listed
as open. v4's text and its Lean module disagree on whether the detector flags the witness of its
own `L_R` proof; ours passes either way.

## Why it matters

v4 asks whether these results are theorems of the modal logic or only of its embedding. A
detector-certified proof answers that for every proof the detector reads correctly. The
companion findings on this site make the answer semantic: a complete calculus over v4's
$\mathcal L$-general models, the equivalence and L under the rigid reading proved in every such
model, and a hole in the detector that shows why the semantic proofs are needed.

## Proved vs checked

Every proof is Lean 4 (core library, axioms propext, Classical.choice and Quot.sound only),
built in v4's own modules, and was run through v4's `hybrid_check.py` in witness and whole-term
mode with full-name matching. One further claim of the run (a Henkin-model version of the
equivalence over eleven listed closure terms) was disputed by the run's skeptic and is left out.
