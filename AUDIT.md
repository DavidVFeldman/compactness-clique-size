# Audit

Static audit of the Lean development against the note, performed on the sources in this
repository. It records what was checked without compiling, what the CI checks on every push, and
every place where a formal statement departs from the note.

## Checked statically

* No `sorry` and no `admit` anywhere in `RequestProject/`.
* No `axiom` declaration, no `native_decide`, no `implemented_by`, no `unsafe`, no `partial def`,
  no `@[extern]`.
* 141 `theorem`, 47 `def`, 3 `noncomputable def`, 3 `abbrev`, 5 `instance`, 1 `structure`,
  1 `class`; 3237 lines across 18 modules.
* `lean-toolchain` (`leanprover/lean4:v4.28.0`) agrees with the Mathlib revision pinned in
  `lake-manifest.json` (`v4.28.0`, `8f9d9cff6bd7`).
* Every module is reachable from `RequestProject/Main.lean`.
* The three open questions are `def ... : Prop` — statements, not theorems — as the note intends.

**A static audit is not a compilation.** The claim that the development is verified rests on
`lake build` succeeding together with a clean `#print axioms` report; run the CI workflow, or the
three commands in the README, before making any closure claim.

## Checked by CI

`.github/workflows/verify.yml` builds the library, rescans for `sorry`/`admit` and for suspect
declarations, runs `scripts/Audit.lean`, parses the axiom report and fails on anything beyond
`propext`, `Classical.choice` and `Quot.sound`, writes a declaration census, and uploads
`audit/` plus `build.log` as artifacts.

## Departures from the note

None of these is an error; each is a place where the formal statement and the prose differ, and
each should be read before any sentence in the note asserts what has been verified.

1. **The sphere bound is two-sided from below at 3, not 4.** `chiOp_sphereOrth_three_bounds`
   gives `3 ≤ χ_op(S²,⊥) ≤ 24`. The note's `4 = χ(S²,⊥)` is Godsil–Zaks, cited rather than
   proved, so the formal lower bound is the clique number `3` via `le_chiOp_sphereOrth`.
2. **The 24-set cover uses explicit frames.** The note chooses `ρ₂`, `ρ₃` generically. The
   formalization fixes the standard frame together with two rational orthonormal frames
   (`frameRow`), and verifies `C ∩ ρ₂(C) ∩ ρ₃(C) = ∅` as a finite computation over the 27 triples
   of rows (`eq_zero_of_frameForm_eq_zero`). Same bound, different witness.
3. **`chiOp` takes values in `ℕ∞`.** Infinite covers all receive the value `⊤`, so the
   development distinguishes finite from infinite open chromatic number but not one infinite
   cardinal from another. Everything the note asks of `χ_op` lives inside that.
4. **Corollary 4(c) is proved, not cited.** The note cites Bernstein for productivity of
   `𝔲`-compactness; `ultrafilterCompact_pi` proves the countable case needed.
5. **Corollary 5 is proved, not cited.** `compactSpace_of_metacompact_of_countablyCompact` proves
   the Arens–Dugundji step rather than citing it.
6. **Theorem 1 appears in two forms.** `boundedCliqueProperty_of_countablyCompact_pi` takes
   exactly the note's hypothesis (`X^ω` countably compact);
   `boundedCliqueProperty_of_seqClusterCompact_pi` takes the cluster-point form the proof
   consumes. Earlier drafts of the note's verification paragraph disclaimed the first of these;
   that disclaimer is now obsolete.
7. **The co-countable results are more general than the note's.** The note uses `ℝ` with the
   co-countable topology; `stronglyStarCompact_cocountable` and `not_countablyCompact_cocountable`
   hold for any uncountable, respectively infinite, underlying set.
8. **The conditional witness uses the note's sufficient density condition.**
   `mainQuestion_of_exists_countablyCompact_dense_subset_goodSet` hypothesizes that `Y` meets `Ŝ`
   for every infinite partial section `S` — the form the note observes to be enough — rather than
   topological density in `ω*`.
9. **`ω* \ G` nowhere dense is not stated separately.** `isOpen_goodSet` and
   `exists_free_ultrafilter_mem_goodSet` give openness and density of `G`, and
   `exists_free_ultrafilter_no_isPartialSection` gives non-emptiness of the complement; the
   nowhere-density assertion of §4 follows immediately but has no named declaration.
10. **Not formalized, resting on cited literature:** the Tomita consistency result; the
    Ginsburg–Saks theorem in the cardinal-power generality in which the note quotes it (the
    countable case used in Corollary 4(c) is formalized); the Hrušák–van Mill–Ramos-García–Shelah
    construction behind the second horn of Remark 3; the Holmsen–Lee remark; Godsil–Zaks.

## Missing from the delivered tarball

The Aristotle report (`docs/ARISTOTLE_SUMMARY.md`, item 6) refers to a "Properties table" that
was updated. No such file is present in the delivered archive; it exists only in the Aristotle
session. Request it if the table is wanted as a repository artifact.

## LaTeX housekeeping

* Four references — `\ref{cofinite}`, `\ref{sphere}`, `\ref{betaomega}`, `\ref{profile}` — have
  no corresponding `\label`. They occur only inside `\tempout{...}` (which expands to nothing) in
  material placed after `\end{document}`, so they are inert; restoring any of that material
  without adding the labels will produce undefined references.
* Three fragments of the blue revision markup survive in the body and bibliography of v6
  (the period after Corollary 3, and two bibliography items).
* `\ref{metrizable}`, `\ref{dichotomy}` and `\ref{sphereq}` are defined but never cited.

## Verification paragraph

A drop-in replacement for the stale paragraph currently parked after `\end{document}`, using only
labels that exist:

```latex
{\bf Verification} The mathematical content of this note has been formalized in Lean 4 against
Mathlib (toolchain \texttt{v4.28.0}) and machine-checked, with no {\tt sorry}s and no axioms
beyond Lean's standard three ({\tt propext}, {\tt Classical.choice}, {\tt Quot.sound}):
Lemmas \ref{compactbounded} and \ref{finitecc} with their footnotes, Corollary \ref{metrizable},
Proposition \ref{galois} with Corollary \ref{covers}, Corollary \ref{starcompact} and the failure
of its converse, Remark \ref{dichotomy}, Theorem \ref{omegapower} and Corollary \ref{suffconds},
the $\omega_1$ example of Remark \ref{omegaone}, Propositions \ref{preserve} and \ref{separable},
Corollary \ref{metacompact}, the profile of a witness, the $\beta\omega$ construction of \S 4
together with its conditional consequence, the implications of \S 5, the clique number of
$S^{n-1}$, and the bound $\chiop(S^2,\perp) \leq 24$. Questions \ref{mainq} and \ref{sphereq}, and
the question of \S 5, are stated formally and left unresolved. Results quoted from the literature
are not formalized; in particular the lower bound $\chi(S^2,\perp) = 4$ is not, so the formal
sphere statement is $3 \leq \chiop(S^2,\perp) \leq 24$, and the $\leq 24$ bound is obtained from
three explicit orthonormal frames of $\R^3$ in place of the genericity argument given above. The
development is available at [repository link], archived at [DOI].
```
