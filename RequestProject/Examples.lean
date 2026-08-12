import RequestProject.Metacompact

/-!
# A Note on Compactness and Clique Size — Remark 2: a non-`T1` example

This file formalizes the example of Remark 2 of the source note *A Note on Compactness and Clique
Size* (D. V. Feldman and A. Wilce): "it is not hard to find non-`T1` lp-compact spaces having
infinite cliques (consider, e.g., `ℕ × {0,1}` with `ℕ` discrete and `{0,1}` indiscrete, and
consider the relation of being in different fibres over `ℕ`)".

This shows that the `T1` hypothesis cannot be dropped from the last statement of Lemma 2 of the
note: limit point compactness does not imply the finite clique property in general.
-/

namespace CliqueSize

open Set Filter Topology

/-- The space `ℕ × {0,1}` of Remark 2 of the note, with `ℕ` discrete and `{0,1}` indiscrete:
the open sets are exactly the preimages of subsets of `ℕ` under the first projection. -/
abbrev RemarkTwoSpace : Type := ℕ × Bool

/-- The topology of the space `ℕ × {0,1}` of Remark 2 of the note: the product of the discrete
topology on `ℕ` with the indiscrete topology on `{0,1}`, i.e. the topology induced from the
discrete topology on `ℕ` by the first projection. -/
instance : TopologicalSpace RemarkTwoSpace := TopologicalSpace.induced Prod.fst ⊥

/-- The relation of Remark 2 of the note: two points of `ℕ × {0,1}` are related iff they lie in
different fibres over `ℕ`. -/
def remarkTwoRel : RemarkTwoSpace → RemarkTwoSpace → Prop := fun p q => p.1 ≠ q.1

/-- Remark 2 of the note: the "different fibres" relation on `ℕ × {0,1}` is a closed
orthogonality relation. -/
theorem isOrthogonality_remarkTwoRel : IsOrthogonality remarkTwoRel := by
  refine ⟨fun p q h => Ne.symm h, fun p h => h rfl, ?_⟩
  rw [← isOpen_compl_iff]
  have hcont : Continuous (fun r : RemarkTwoSpace × RemarkTwoSpace => (r.1.1, r.2.1)) := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_induced_dom).comp continuous_fst
    · exact (continuous_induced_dom).comp continuous_snd
  have : {r : RemarkTwoSpace × RemarkTwoSpace | remarkTwoRel r.1 r.2}ᶜ
      = (fun r : RemarkTwoSpace × RemarkTwoSpace => (r.1.1, r.2.1)) ⁻¹'
        {s : ℕ × ℕ | s.1 = s.2} := by
    ext r
    simp [remarkTwoRel]
  rw [this]
  exact hcont.isOpen_preimage _ (isOpen_discrete _)

/-- Remark 2 of the note: the space `ℕ × {0,1}` is limit point compact — indeed every nonempty
subset has an accumulation point, since the two points of a fibre are topologically
indistinguishable. -/
theorem limitPointCompact_remarkTwoSpace : LimitPointCompact RemarkTwoSpace := by
  intro A hA
  obtain ⟨p, hp⟩ := hA.nonempty
  refine ⟨(p.1, !p.2), accPt_iff_nhds.mpr fun U hU => ?_⟩
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hU
  rw [isOpen_induced_iff] at hVopen
  obtain ⟨S, -, hSV⟩ := hVopen
  have hpV : p ∈ V := by
    rw [← hSV] at hxV ⊢
    exact hxV
  exact ⟨p, ⟨hVsub hpV, hp⟩, fun h => (Bool.not_ne_self p.2) (congrArg Prod.snd h).symm⟩

/-- Remark 2 of the note: the relation of being in different fibres has an infinite clique,
namely a section of `ℕ × {0,1} → ℕ`. -/
theorem infinite_clique_remarkTwoRel :
    ∃ A : Set RemarkTwoSpace, IsClique remarkTwoRel A ∧ A.Infinite := by
  refine ⟨Set.range (fun n : ℕ => (n, true)), ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ hnm
    simpa [remarkTwoRel] using fun h => hnm (by rw [h])
  · exact Set.infinite_range_of_injective (fun n m h => by simpa using h)

/-- Remark 2 of the note: there is a (non-`T1`) limit point compact space carrying a closed
orthogonality relation with an infinite clique; hence limit point compactness alone does not
imply the finite clique property, and the `T1` hypothesis in the final statement of Lemma 2 of
the note is needed. -/
theorem exists_limitPointCompact_not_finiteCliqueProperty :
    ∃ (Y : Type) (_ : TopologicalSpace Y), LimitPointCompact Y ∧ ¬ FiniteCliqueProperty Y := by
  refine ⟨RemarkTwoSpace, inferInstance, limitPointCompact_remarkTwoSpace, fun h => ?_⟩
  obtain ⟨A, hAclique, hAinf⟩ := infinite_clique_remarkTwoRel
  exact hAinf (h _ isOrthogonality_remarkTwoRel A hAclique)

end CliqueSize
