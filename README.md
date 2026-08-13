# A Note on Compactness and Clique Size

LaTeX source and Lean 4 formalization accompanying the note *A Note on Compactness and Clique
Size*, by David V. Feldman (University of New Hampshire) and Alexander Wilce (Susquehanna
University).

A topological space has **finite cliques** (FCP), respectively **bounded cliques** (BCP), iff
every closed irreflexive binary relation on it has cliques of finite, respectively bounded finite,
size. Compact spaces have bounded cliques; countable compactness is equivalent, for `T₁` spaces,
to having finite cliques; and whether some countably compact space has finite but unbounded
cliques is the main open question of the note.

## Contents

| Path | Description |
| --- | --- |
| `paper/Compactness_Question-v7.tex` | The note. |
| `RequestProject/` | The Lean 4 library. `Main.lean` imports everything and indexes the sections. |
| `scripts/Audit.lean` | `#print axioms` for the headline results. |
| `.github/workflows/verify.yml` | CI: build, `sorry` scan, axiom audit, artifact upload. |
| `docs/ARISTOTLE_SUMMARY.md` | Report from the final Aristotle formalization round. |

## Building

Requires [`elan`](https://github.com/leanprover/elan); the toolchain is pinned in
`lean-toolchain` (Lean 4.28.0, Mathlib `v4.28.0`).

```
lake exe cache get
lake build
lake env lean scripts/Audit.lean
```

On Windows, run the same three commands from CMD or PowerShell after installing `elan`.
`lake exe cache get` is not optional in practice: without it, Mathlib is rebuilt from source.

## Verification status

Every declaration compiles with no `sorry`, no `axiom` declaration, no `native_decide` and no
`implemented_by`; the audited results depend only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

| Item of the note | Lean | |
| --- | --- | --- |
| Definitions 1, 2 | `IsOrthogonality`, `IsClique`, `HasFiniteCliques`, `HasBoundedCliques`, `FiniteCliqueProperty`, `BoundedCliqueProperty` | ✔ |
| Lemma 1 | `hasBoundedCliques_of_compact`, `boundedCliqueProperty_of_compact` | ✔ |
| Lemma 1, uniform/metric footnote | `Uniform.lean` (`hasBoundedCliques_of_compact_uniform`, `exists_pos_le_dist_of_isOrthogonality`) | ✔ |
| Remark 1(i) | `encard_le_chiOp`, `finiteOpenChromatic_of_compact` | ✔ |
| Lemma 2 | `limitPointCompact_of_finiteCliqueProperty`, `finiteCliqueProperty_of_omegaLimitPointCompact`, `finiteCliqueProperty_iff_countablyCompact_t1` | ✔ |
| Lemma 2, countable-compactness footnote | `omegaLimitPointCompact_iff_countablyCompact` | ✔ |
| Corollary 1 | `compactSpace_of_finiteCliqueProperty` | ✔ |
| Question 1 | `MainQuestion` (statement) | open |
| Remark 2, non-`T₁` example | `exists_limitPointCompact_not_finiteCliqueProperty` | ✔ |
| Remark 2, the two side questions | `MainQuestionNonT1`, `OmegaLimitPointCompactNecessaryQuestion` (statements) | open |
| Remark 3, the dichotomy | `mainQuestion_or_boundedCliqueProperty_iff_countablyCompact` | ✔ |
| Proposition 1, Corollary 2 | `galoisConnection_perpCover_cov`, `finiteCliqueProperty_iff_separated_finite`, `boundedCliqueProperty_iff_separated_bounded` | ✔ |
| Corollary 3 | `stronglyStarCompact_of_finiteCliqueProperty` | ✔ |
| Failure of its converse | `exists_stronglyStarCompact_not_finiteCliqueProperty` (`Cocountable.lean`) | ✔ |
| Theorem 1 | `boundedCliqueProperty_of_countablyCompact_pi` | ✔ |
| Corollary 4 (a), (b), (c) | `boundedCliqueProperty_of_seqCompactSpace`, `_of_omegaBounded`, `_of_ultrafilterCompact` | ✔ |
| Remark 4, `ω₁` | `OmegaOne.lean` (`exists_boundedCliqueProperty_not_compactSpace`, `hasBoundedCliques_direct`, `cofinalRel`) | ✔ |
| Propositions 2, 3 | `BoundedCliqueProperty.of_isClosed`, `.image`, `separable_reflection` | ✔ |
| Corollary 5 | `compactSpace_of_metacompact_of_countablyCompact`, `finiteCliqueProperty_iff_compactSpace_of_metacompact` | ✔ |
| Profile of a witness | `witness_profile` | ✔ |
| §4, the `βω` construction | `BetaOmega.lean` (`mem_closure_betaR0_iff`, `isOpen_goodSet`, `exists_free_ultrafilter_no_isPartialSection`) | ✔ |
| §4, the conditional witness | `mainQuestion_of_exists_countablyCompact_dense_subset_goodSet` | ✔ |
| §5, `compact ⇒ finite χ_op ⇒ BCP` | `finiteOpenChromatic_of_compact`, `boundedCliqueProperty_of_finiteOpenChromatic` | ✔ |
| §5, strictness of the first implication | `OmegaOne.exists_finiteOpenChromatic_not_compactSpace` | ✔ |
| Question 2 | `ChromaticQuestion` (statement) | open |
| §5, clique number of `S^{n-1}` | `sphere_clique_number`, `le_chiOp_sphereOrth` | ✔ |
| §5, `χ_op(S²,⊥) ≤ 24` | `chiOp_sphereOrth_three_le`, `chiOp_sphereOrth_three_bounds` | ✔ |
| Question 3 | — | open |

Results of the note that rest on cited literature rather than on arguments given in the note are
not formalized: the Tomita consistency result, `χ(S²,⊥) = 4` (Godsil–Zaks, so the formal sphere
statement is `3 ≤ χ_op(S²,⊥) ≤ 24`), the Holmsen–Lee remark, and the ZFC construction of
Hrušák–van Mill–Ramos-García–Shelah invoked in the second horn of Remark 3. See `AUDIT.md` for
the places where a formal statement departs from the note's wording or proof.

## Machine assistance

The mathematics was drafted in dialogue with Anthropic's Claude and checked and revised by the
authors, as recorded in the note. The Lean development was produced with
[Aristotle](https://aristotle.harmonic.fun) (Harmonic); to cite Aristotle, tag
`@Aristotle-Harmonic` on GitHub, or add

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

to commits.

## License

Not yet set — to be agreed between the authors before the repository is made public.
