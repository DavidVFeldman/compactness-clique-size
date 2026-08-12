import RequestProject.Basic
import RequestProject.Compactness
import RequestProject.Covers
import RequestProject.Uniform
import RequestProject.Powers
import RequestProject.Structure
import RequestProject.Chromatic
import RequestProject.Metrizable
import RequestProject.Metacompact
import RequestProject.Examples
import RequestProject.Cocountable
import RequestProject.OmegaOne
import RequestProject.BetaOmega
import RequestProject.Witness
import RequestProject.Profile
import RequestProject.Sphere
import RequestProject.SphereChromatic

/-!
# A Note on Compactness and Clique Size — index

This module collects the whole formalization of the source note *A Note on Compactness and
Clique Size* (D. V. Feldman and A. Wilce).  The individual sections of the note are formalized in:

* `RequestProject.Basic` — orthogonality relations, cliques, the finite/bounded clique properties
  (Definitions 1 and 2 of §1) and Lemma 1 (compact ⇒ bounded cliques);
* `RequestProject.Compactness` — ω-limit points, ω-limit point compactness, countable compactness
  and Lemma 2 of §1;
* `RequestProject.Uniform` — the uniform/metric footnote discussion following Lemma 1;
* `RequestProject.Covers` — the Galois connection `(⊥, Cov)` of §2, Proposition 1, Corollary 2 and
  Corollary 3 (finite cliques ⇒ strongly star-compact);
* `RequestProject.Cocountable` — the co-countable topology, showing the converse of Corollary 3
  fails;
* `RequestProject.Powers` — Theorem 1 of §3 and Corollary 4 (its sufficient conditions);
* `RequestProject.Structure` — Proposition 2 (preservation) and Proposition 3 (separable
  reflection) of §4;
* `RequestProject.Metrizable`, `RequestProject.Metacompact` — Corollary 1 of §1 and Corollary 5
  of §4;
* `RequestProject.Chromatic` — the open chromatic number `χ_op` of Remark 1(i), §5, Question 1 and
  Question 2;
* `RequestProject.Examples` — the non-`T₁` example of Remark 2;
* `RequestProject.OmegaOne` — the space `ω₁` of Remark 4;
* `RequestProject.BetaOmega`, `RequestProject.Witness` — the `βω` construction at the end of §4;
* `RequestProject.Profile` — the profile of a witness to Question 1;
* `RequestProject.Sphere`, `RequestProject.SphereChromatic` — the sphere `S^{n-1}` of §5 and the
  bound `χ_op(S², ⊥) ≤ 24`.
-/
