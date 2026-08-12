import RequestProject.Chromatic

/-!
# A Note on Compactness and Clique Size — Corollary 1 (the metrizable case)

This file formalizes **Corollary 1** (`metrizable`) of the source note *A Note on Compactness and
Clique Size* (D. V. Feldman and A. Wilce): a metrizable space with finite cliques is compact, and
in particular has bounded cliques.
-/

namespace CliqueSize

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-- In a first-countable space, if every sequence has a cluster point then the space is
sequentially compact.  (Used for the metrizable case, Corollary 1 of the note.) -/
theorem seqCompactSpace_of_seqClusterCompact [FirstCountableTopology X]
    (h : SeqClusterCompact X) : SeqCompactSpace X := by
  refine ⟨fun {u} _ => ?_⟩
  obtain ⟨q, hq⟩ := h u
  obtain ⟨ψ, hψ, htend⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hq
  exact ⟨q, Set.mem_univ _, ψ, hψ, htend⟩

/-- **Corollary 1** (`metrizable`) of the note: a metrizable space with finite cliques is
compact. -/
theorem compactSpace_of_finiteCliqueProperty [TopologicalSpace.MetrizableSpace X]
    (hX : FiniteCliqueProperty X) : CompactSpace X := by
  letI : T1Space X := inferInstance
  have hcc : CountablyCompact X := finiteCliqueProperty_iff_countablyCompact_t1.mp hX
  exact compactSpace_iff_seqCompactSpace.mpr
    (seqCompactSpace_of_seqClusterCompact hcc.seqClusterCompact)

/-- **Corollary 1** (`metrizable`) of the note: a metrizable space with finite cliques has
bounded cliques. -/
theorem boundedCliqueProperty_of_finiteCliqueProperty_metrizable
    [TopologicalSpace.MetrizableSpace X] (hX : FiniteCliqueProperty X) :
    BoundedCliqueProperty X :=
  letI := compactSpace_of_finiteCliqueProperty hX
  boundedCliqueProperty_of_compact

end CliqueSize
