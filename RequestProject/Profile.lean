import RequestProject.Powers
import RequestProject.Metacompact
import RequestProject.Structure

/-!
# A Note on Compactness and Clique Size — the profile of a witness to Question 1

This file assembles the results of Sections 3 and 4 of the source note *A Note on Compactness and
Clique Size* (D. V. Feldman and A. Wilce) into the summary drawn there:

> Taken together, Theorem 1, Corollary 4, Proposition 3, and Corollary 5 severely constrain the
> shape of any witness `X` to a positive answer to Question 1: it may be taken to be separable,
> and must be countably compact; but it must also be non-compact, non-sequentially-compact,
> non-`ω`-bounded, non-metacompact, not `𝔲`-compact for any free ultrafilter `𝔲`, and — most
> tellingly — must have `X^ω` *not* countably compact.

Every clause is a consequence of a result proved elsewhere in this development: Lemma 1 for
non-compactness, Corollary 4(a), (b), (c) for the next three, Corollary 5 for non-metacompactness,
Theorem 1 for the power, and Proposition 3 for the separable reduction.
-/

namespace CliqueSize

open Set Filter Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- **Sections 3–4 of the note**: the profile of a witness to a positive answer to Question 1.
A countably compact `T₁` space `X` carrying a closed orthogonality relation with finite but
unbounded cliques must fail to be compact, sequentially compact, `ω`-bounded, `𝔲`-compact for
every free ultrafilter `𝔲`, and metacompact, and its countable power `X^ω` must fail to be
countably compact; moreover some *separable* such space exists. -/
theorem witness_profile [T1Space X] {R : X → X → Prop} (hcc : CountablyCompact X)
    (hR : IsOrthogonality R) (hfin : HasFiniteCliques R) (hunb : ¬ HasBoundedCliques R) :
    ¬ Nonempty (CompactSpace X) ∧
      ¬ Nonempty (SeqCompactSpace X) ∧
      ¬ OmegaBounded X ∧
      (∀ u : Ultrafilter ℕ, (u : Filter ℕ) ≤ Filter.cofinite → ¬ UltrafilterCompact u X) ∧
      ¬ Metacompact X ∧
      ¬ CountablyCompact (ℕ → X) ∧
      ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T1Space Y)
        (_ : TopologicalSpace.SeparableSpace Y) (S : Y → Y → Prop),
        CountablyCompact Y ∧ IsOrthogonality S ∧ HasFiniteCliques S ∧ ¬ HasBoundedCliques S := by
  have hnotBCP : ¬ BoundedCliqueProperty X := fun h => hunb (h R hR)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, separable_reflection hcc hR hfin hunb⟩
  · rintro ⟨hcompact⟩
    exact hnotBCP boundedCliqueProperty_of_compact
  · rintro ⟨hseq⟩
    exact hnotBCP boundedCliqueProperty_of_seqCompactSpace
  · intro hob
    exact hnotBCP (boundedCliqueProperty_of_omegaBounded hob)
  · intro u hfree hu
    exact hnotBCP (boundedCliqueProperty_of_ultrafilterCompact hfree hu)
  · intro hmc
    have := (finiteCliqueProperty_iff_compactSpace_of_metacompact hmc).1.1
      (finiteCliqueProperty_of_countablyCompact hcc)
    exact hnotBCP this
  · intro hpow
    exact hnotBCP (boundedCliqueProperty_of_countablyCompact_pi hpow)

end CliqueSize
