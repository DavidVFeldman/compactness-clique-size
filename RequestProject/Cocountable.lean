import RequestProject.Covers
import RequestProject.Compactness

/-!
# A Note on Compactness and Clique Size — the co-countable topology

This file formalizes the example given after Corollary 3 in the source note *A Note on
Compactness and Clique Size* (D. V. Feldman and A. Wilce):

> For `T₁` spaces, this reduces to the known fact that countable compactness implies strong
> star-compactness.  The converse is false (e.g., `ℝ` with the co-countable topology is strongly
> star-compact but not countably compact), and thus, so is the converse to Corollary 3.

We construct the co-countable topology on an arbitrary type (its open sets are the empty set
together with the sets of countable complement), show that on an uncountable type — such as `ℝ` —
it is strongly star-compact but not countably compact, and deduce that the converse to Corollary
3 fails.
-/

namespace CliqueSize

open Set Filter Topology

/-- The *co-countable topology* on a type `X`: the open sets are the empty set together with the
sets whose complement is countable.  (Section 2 of the note: "`ℝ` with the co-countable
topology".) -/
def cocountableTopology (X : Type*) : TopologicalSpace X where
  IsOpen U := U = ∅ ∨ (Uᶜ).Countable
  isOpen_univ := Or.inr (by simp)
  isOpen_inter := by
    rintro s t (rfl | hs) (rfl | ht)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr (by rw [Set.compl_inter]; exact hs.union ht)
  isOpen_sUnion := by
    intro S hS
    by_cases h : ∃ U ∈ S, U ≠ ∅
    · obtain ⟨U, hUS, hUne⟩ := h
      rcases hS U hUS with rfl | hU
      · exact absurd rfl hUne
      · refine Or.inr (hU.mono ?_)
        exact Set.compl_subset_compl.2 (Set.subset_sUnion_of_mem hUS)
    · push_neg at h
      refine Or.inl (Set.eq_empty_of_forall_notMem ?_)
      rintro x ⟨U, hUS, hxU⟩
      rw [h U hUS] at hxU
      exact hxU

/-- A type carrying the co-countable topology (a type synonym, so that the co-countable topology
does not clash with an existing topology such as the usual one on `ℝ`). -/
def Cocountable (X : Type*) : Type _ := X

/-- The type synonym `Cocountable X` of the discussion after Corollary 3 of the note carries the
co-countable topology. -/
instance (X : Type*) : TopologicalSpace (Cocountable X) := cocountableTopology X

/-- Unfolding of the co-countable topology used in the discussion after Corollary 3 of the note:
a set is open iff it is empty or has countable complement. -/
theorem isOpen_cocountable_iff {X : Type*} {U : Set (Cocountable X)} :
    IsOpen U ↔ U = ∅ ∨ ((U : Set X)ᶜ).Countable := Iff.rfl

/-- In the co-countable topology, a nonempty open set has countable complement. -/
theorem countable_compl_of_isOpen_of_nonempty {X : Type*} {U : Set (Cocountable X)}
    (hU : IsOpen U) (hne : U.Nonempty) : ((U : Set X)ᶜ).Countable := by
  rcases isOpen_cocountable_iff.1 hU with rfl | h
  · exact absurd hne (by simp)
  · exact h

/-- The note's example: an uncountable set with the co-countable topology is strongly
star-compact (Section 2 of the note). -/
theorem stronglyStarCompact_cocountable (X : Type*) [Uncountable X] :
    StronglyStarCompact (Cocountable X) := by
  classical
  intro U hU
  -- choose, for each point, a member of the cover containing it
  have hpick : ∀ y : Cocountable X, ∃ V ∈ U, y ∈ V := by
    intro y
    obtain ⟨V, hV, hyV⟩ := Set.mem_sUnion.mp (hU.2 ▸ Set.mem_univ y)
    exact ⟨V, hV, hyV⟩
  choose V hVU hVmem using hpick
  obtain ⟨y₀⟩ : Nonempty X := inferInstance
  set U₀ : Set (Cocountable X) := V y₀ with hU₀
  have hC : ((U₀ : Set X)ᶜ).Countable :=
    countable_compl_of_isOpen_of_nonempty (hU.1 _ (hVU y₀)) ⟨y₀, hVmem y₀⟩
  -- the countably many points outside `U₀`, and the countably many points outside the sets
  -- covering them, form a countable set, so some point avoids all of them
  set D : Set X := (U₀ : Set X)ᶜ ∪ ⋃ y ∈ ((U₀ : Set X)ᶜ), ((V y : Set X)ᶜ) with hD
  have hDcount : D.Countable := by
    refine hC.union (Set.Countable.biUnion hC fun y _ => ?_)
    exact countable_compl_of_isOpen_of_nonempty (hU.1 _ (hVU y)) ⟨y, hVmem y⟩
  obtain ⟨x, hx⟩ : ∃ x : X, x ∉ D := by
    by_contra hcon
    push_neg at hcon
    exact (Set.not_countable_univ (α := X)) (hDcount.mono fun z _ => hcon z)
  refine ⟨{x}, Set.finite_singleton x, Set.eq_univ_of_forall fun z => ?_⟩
  have hxU₀ : x ∈ U₀ := by
    by_contra hcon
    exact hx (Or.inl hcon)
  by_cases hz : z ∈ U₀
  · exact Set.mem_biUnion (show U₀ ∈ {W ∈ U | ({x} ∩ W).Nonempty} from
      ⟨hVU y₀, ⟨x, rfl, hxU₀⟩⟩) hz
  · have hxVz : x ∈ V z := by
      by_contra hcon
      exact hx (Or.inr (Set.mem_biUnion (show z ∈ (U₀ : Set X)ᶜ from hz) hcon))
    exact Set.mem_biUnion (show V z ∈ {W ∈ U | ({x} ∩ W).Nonempty} from
      ⟨hVU z, ⟨x, rfl, hxVz⟩⟩) (hVmem z)

/-- The note's example: an infinite set with the co-countable topology is not countably compact
(Section 2 of the note). -/
theorem not_countablyCompact_cocountable (X : Type*) [Infinite X] :
    ¬ CountablyCompact (Cocountable X) := by
  classical
  intro hcc
  set d : ℕ ↪ X := Infinite.natEmbedding X with hd
  set W : ℕ → Set (Cocountable X) :=
    fun n => (Set.range d)ᶜ ∪ (d '' (Set.Iic n)) with hW
  have hWopen : ∀ n, IsOpen (W n) := by
    intro n
    refine Or.inr ?_
    have : ((W n : Set X))ᶜ ⊆ Set.range d := by
      intro z hz
      by_contra hcon
      exact hz (Or.inl hcon)
    refine Set.Countable.mono this ?_
    exact Set.countable_range d
  have hWcover : (⋃ n, W n) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    by_cases hz : (z : X) ∈ Set.range d
    · obtain ⟨n, rfl⟩ := hz
      exact Set.mem_iUnion.2 ⟨n, Or.inr ⟨n, le_refl n, rfl⟩⟩
    · exact Set.mem_iUnion.2 ⟨0, Or.inl hz⟩
  obtain ⟨N, hN⟩ := hcc W hWopen hWcover
  have hmem : (d N : Cocountable X) ∈ (⋃ n ∈ Finset.range N, W n) := by rw [hN]; trivial
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hmem
  obtain ⟨n, hnN, hn⟩ := hmem
  rcases hn with hn | ⟨k, hk, hkd⟩
  · exact hn ⟨N, rfl⟩
  · have hkN : k = N := d.injective hkd
    simp only [Set.mem_Iic] at hk
    omega

/-- The co-countable topology is `T₁`, since singletons are countable. -/
instance (X : Type*) : T1Space (Cocountable X) :=
  ⟨fun x => ⟨Or.inr (by simp)⟩⟩

/-- **Section 2 of the note**: the converse to Corollary 3 is false — there is a strongly
star-compact `T₁` space that is not countably compact, and hence (by Lemma 2) does not have
finite cliques.  The example is `ℝ` with the co-countable topology. -/
theorem exists_stronglyStarCompact_not_finiteCliqueProperty :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T1Space Y),
      StronglyStarCompact Y ∧ ¬ CountablyCompact Y ∧ ¬ FiniteCliqueProperty Y := by
  refine ⟨Cocountable ℝ, inferInstance, inferInstance, stronglyStarCompact_cocountable ℝ,
    not_countablyCompact_cocountable ℝ, fun hfcp => ?_⟩
  exact not_countablyCompact_cocountable ℝ (finiteCliqueProperty_iff_countablyCompact_t1.1 hfcp)

end CliqueSize
