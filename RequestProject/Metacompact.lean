import RequestProject.Metrizable

/-!
# A Note on Compactness and Clique Size — Corollary 5 (the metacompact case)

This file formalizes **Corollary 5** (`metacompact`) of the source note *A Note on Compactness
and Clique Size* (D. V. Feldman and A. Wilce): a metacompact `T1` space has finite cliques iff it
has bounded cliques iff it is compact.

The topological ingredient quoted in the note (Arens–Dugundji: countably compact metacompact
spaces are compact) is proved here from scratch, via the classical argument through irreducible
subcovers of a point-finite open refinement.
-/

namespace CliqueSize

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## Metacompactness -/

/-- A family of sets is *point-finite* iff each point lies in only finitely many members. -/
def IsPointFinite (V : Set (Set X)) : Prop := ∀ x : X, {W | W ∈ V ∧ x ∈ W}.Finite

/-- **Metacompactness**: every open cover has a point-finite open refinement.  (This is the
hypothesis of Corollary 5 of the note.) -/
def Metacompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : Set (Set X), IsOpenCover U →
    ∃ V : Set (Set X), IsOpenCover V ∧ (∀ W ∈ V, ∃ U' ∈ U, W ⊆ U') ∧ IsPointFinite V

omit [TopologicalSpace X] in
/-- An irreducible (minimal) subcover of a point-finite cover exists, by Zorn's lemma applied to
subcovers ordered by reverse inclusion. -/
theorem exists_minimal_subcover {V : Set (Set X)} (hV : ⋃₀ V = Set.univ)
    (hpf : IsPointFinite V) :
    ∃ m, Minimal (fun W : Set (Set X) => W ⊆ V ∧ ⋃₀ W = Set.univ) m := by
  refine zorn_superset {W : Set (Set X) | W ⊆ V ∧ ⋃₀ W = Set.univ} ?_
  intro c hc hchain
  rcases Set.eq_empty_or_nonempty c with rfl | hcne
  · exact ⟨V, ⟨subset_rfl, hV⟩, by simp⟩
  obtain ⟨K₀, hK₀⟩ := hcne
  refine ⟨⋂₀ c, ⟨?_, ?_⟩, fun s hs => Set.sInter_subset_of_mem hs⟩
  · exact fun W hW => (hc hK₀).1 (hW K₀ hK₀)
  · -- the intersection of a chain of subcovers of a point-finite cover is a cover
    refine Set.eq_univ_of_forall fun x => ?_
    by_contra hx
    have hbad : ∀ W : Set X, W ∈ {W | W ∈ V ∧ x ∈ W} → ∃ K ∈ c, W ∉ K := by
      intro W hW
      by_contra hall
      push_neg at hall
      exact hx ⟨W, Set.mem_sInter.mpr fun K hK => hall K hK, hW.2⟩
    have hchoice : ∀ W : Set X, ∃ K, K ∈ c ∧ (W ∈ {W | W ∈ V ∧ x ∈ W} → W ∉ K) := by
      intro W
      by_cases hW : W ∈ {W | W ∈ V ∧ x ∈ W}
      · obtain ⟨K, hKc, hWK⟩ := hbad W hW
        exact ⟨K, hKc, fun _ => hWK⟩
      · exact ⟨K₀, hK₀, fun h => absurd h hW⟩
    choose g hgc hgnot using hchoice
    -- the finitely many chosen members of the chain have a least element
    have hFne : {W | W ∈ V ∧ x ∈ W}.Nonempty := by
      obtain ⟨W, hWK₀, hxW⟩ := Set.mem_sUnion.mp ((hc hK₀).2 ▸ Set.mem_univ x)
      exact ⟨W, (hc hK₀).1 hWK₀, hxW⟩
    obtain ⟨K, hK⟩ := ((hpf x).image g).exists_minimalFor id _ (hFne.image g)
    obtain ⟨⟨W₀, hW₀F, rfl⟩, hmin⟩ := hK
    have hleast : ∀ K' ∈ g '' {W | W ∈ V ∧ x ∈ W}, g W₀ ⊆ K' := by
      rintro K' ⟨W, hWF, rfl⟩
      rcases hchain.total (hgc W₀) (hgc W) with h | h
      · exact h
      · exact hmin ⟨W, hWF, rfl⟩ h
    obtain ⟨W', hW'K, hxW'⟩ := Set.mem_sUnion.mp ((hc (hgc W₀)).2 ▸ Set.mem_univ x)
    have hW'F : W' ∈ {W | W ∈ V ∧ x ∈ W} := ⟨(hc (hgc W₀)).1 hW'K, hxW'⟩
    exact hgnot W' hW'F (hleast (g W') ⟨W', hW'F, rfl⟩ hW'K)

/-- A point-finite open cover of an $\omega$-limit point compact (equivalently countably
compact) space has a finite subcover.  This is the key step of the Arens–Dugundji theorem quoted
in Corollary 5 of the note. -/
theorem exists_finite_subcover_of_pointFinite (hX : OmegaLimitPointCompact X)
    {V : Set (Set X)} (hVopen : ∀ W ∈ V, IsOpen W) (hV : ⋃₀ V = Set.univ)
    (hpf : IsPointFinite V) :
    ∃ W ⊆ V, W.Finite ∧ ⋃₀ W = Set.univ := by
  obtain ⟨m, hm⟩ := exists_minimal_subcover hV hpf
  refine ⟨m, hm.1.1, ?_, hm.1.2⟩
  by_contra hinf
  -- by minimality, each member of `m` contains a point covered by no other member
  have hpt : ∀ W : m, ∃ p : X, p ∉ ⋃₀ (m \ {(W : Set X)}) := by
    rintro ⟨W, hW⟩
    by_contra hall
    push_neg at hall
    have hcover : ⋃₀ (m \ {W}) = Set.univ :=
      Set.eq_univ_of_forall fun p => by simpa using hall p
    have hmem : m \ {W} ∈ {W : Set (Set X) | W ⊆ V ∧ ⋃₀ W = Set.univ} :=
      ⟨fun U hU => hm.1.1 hU.1, hcover⟩
    have := hm.2 hmem Set.diff_subset hW
    simp at this
  choose pt hpt using hpt
  have hptmem : ∀ W : m, pt W ∈ (W : Set X) := by
    intro W
    obtain ⟨W', hW'm, hW'⟩ := Set.mem_sUnion.mp (hm.1.2 ▸ Set.mem_univ (pt W))
    by_cases hWW' : W' = (W : Set X)
    · exact hWW' ▸ hW'
    · exact absurd ⟨W', ⟨hW'm, hWW'⟩, hW'⟩ (hpt W)
  have hptinj : Function.Injective pt := by
    intro W W' hWW'
    by_contra hne
    refine hpt W ⟨(W' : Set X), ⟨W'.2, fun h => hne (Subtype.ext h.symm)⟩, ?_⟩
    rw [hWW']
    exact hptmem W'
  -- the resulting set of points is infinite, so it has an ω-limit point
  haveI : Infinite m := Set.infinite_coe_iff.mpr hinf
  obtain ⟨q, hq⟩ := hX (Set.range pt) (Set.infinite_range_of_injective hptinj)
  obtain ⟨V₀, hV₀m, hqV₀⟩ := Set.mem_sUnion.mp (hm.1.2 ▸ Set.mem_univ q)
  have hV₀inf := hq V₀ ((hVopen V₀ (hm.1.1 hV₀m)).mem_nhds hqV₀)
  -- but the only such point lying in `V₀` is the one attached to `V₀`
  refine hV₀inf (Set.Finite.subset (Set.finite_singleton (pt ⟨V₀, hV₀m⟩)) ?_)
  rintro y ⟨hyV₀, W, rfl⟩
  by_cases hWV₀ : (W : Set X) = V₀
  · have hWeq : W = (⟨V₀, hV₀m⟩ : m) := Subtype.ext hWV₀
    simp [hWeq]
  · exact absurd ⟨V₀, ⟨hV₀m, fun h => hWV₀ h.symm⟩, hyV₀⟩ (hpt W)

/-- **Arens–Dugundji**, as quoted in Corollary 5 of the note: a countably compact metacompact
space is compact. -/
theorem compactSpace_of_metacompact_of_countablyCompact (hmc : Metacompact X)
    (hcc : CountablyCompact X) : CompactSpace X := by
  rw [← isCompact_univ_iff]
  refine isCompact_of_finite_subcover fun {ι} U hUopen hcover => ?_
  have hOC : IsOpenCover (Set.range U) := by
    refine ⟨?_, Set.eq_univ_of_forall fun x => ?_⟩
    · rintro _ ⟨i, rfl⟩
      exact hUopen i
    · obtain ⟨i, hx⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ x))
      exact ⟨U i, ⟨i, rfl⟩, hx⟩
  obtain ⟨V, hVcover, hVref, hVpf⟩ := hmc _ hOC
  obtain ⟨W, hWV, hWfin, hWcover⟩ :=
    exists_finite_subcover_of_pointFinite hcc.omegaLimitPointCompact hVcover.1 hVcover.2 hVpf
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- with no indices at all the space must be empty
    refine ⟨∅, fun x _ => ?_⟩
    obtain ⟨i, -⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ x))
    exact (hι.false i).elim
  -- pick, for each member of the finite subcover, an index of the original family
  have hchoice : ∀ S : Set X, ∃ i : ι, S ∈ W → S ⊆ U i := by
    intro S
    by_cases hS : S ∈ W
    · obtain ⟨U', ⟨i, rfl⟩, hSU⟩ := hVref S (hWV hS)
      exact ⟨i, fun _ => hSU⟩
    · exact ⟨Classical.arbitrary ι, fun h => absurd h hS⟩
  choose f hf using hchoice
  refine ⟨(hWfin.image f).toFinset, fun x _ => ?_⟩
  obtain ⟨S, hSW, hxS⟩ := Set.mem_sUnion.mp (hWcover ▸ Set.mem_univ x)
  refine Set.mem_iUnion₂.2 ⟨f S, ?_, hf S hSW hxS⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_image]
  exact ⟨S, hSW, rfl⟩

/-- **Corollary 5** (`metacompact`) of the note: a metacompact `T1` space has finite cliques iff
it has bounded cliques iff it is compact. -/
theorem finiteCliqueProperty_iff_compactSpace_of_metacompact [T1Space X] (hmc : Metacompact X) :
    (FiniteCliqueProperty X ↔ BoundedCliqueProperty X) ∧
      (BoundedCliqueProperty X ↔ Nonempty (CompactSpace X)) := by
  have hFC_to_compact : FiniteCliqueProperty X → CompactSpace X := fun hfc =>
    compactSpace_of_metacompact_of_countablyCompact hmc
      (finiteCliqueProperty_iff_countablyCompact_t1.mp hfc)
  constructor
  · refine ⟨fun hfc => ?_, BoundedCliqueProperty.finiteCliqueProperty⟩
    letI := hFC_to_compact hfc
    exact boundedCliqueProperty_of_compact
  · refine ⟨fun hbc => ⟨hFC_to_compact hbc.finiteCliqueProperty⟩, fun ⟨hc⟩ => ?_⟩
    letI := hc
    exact boundedCliqueProperty_of_compact

end CliqueSize
