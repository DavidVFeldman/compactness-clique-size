import RequestProject.Structure

/-!
# A Note on Compactness and Clique Size — Section 5: Chromatic questions, and the open questions

This file formalizes the chromatic notions of Section 5 of the source note
*A Note on Compactness and Clique Size* (D. V. Feldman and A. Wilce), together with the
statements of the open questions raised in the note:

* the *open chromatic number* $\chi_{\mathrm{op}}(R)$ of Remark 1(i) and Section 5;
* the implications `compact ⇒ finite χ_op ⇒ bounded cliques` of Section 5;
* **Question 1** (`mainq`), the main open question of the note, and the dichotomy of Remark 3;
* **Question 2** of Section 5.
-/

universe u v

namespace CliqueSize

open Set Filter Topology

variable {X : Type u} [TopologicalSpace X]

/-! ## The open chromatic number -/

/-- The **open chromatic number** $\chi_{\mathrm{op}}(R)$ of Remark 1(i) and Section 5 of the
note: the least cardinality of a cover of `X` by `R`-free open sets.  Cardinalities are measured
in `ℕ∞`, which is all that is needed here: the note only ever asks whether
$\chi_{\mathrm{op}}(R)$ is finite, and infinite covers get the value `⊤`. -/
noncomputable def chiOp (R : X → X → Prop) : ℕ∞ :=
  sInf {c : ℕ∞ | ∃ U : Set (Set X), (∀ V ∈ U, IsOpen V ∧ IsRFree R V) ∧ ⋃₀ U = Set.univ ∧
    U.encard = c}

/-- **`X` has finite open chromatic number** (Section 5 of the note): $\chi_{\mathrm{op}}(R)$ is
finite for every closed orthogonality relation `R`. -/
def FiniteOpenChromatic (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ R : X → X → Prop, IsOrthogonality R → chiOp R ≠ ⊤

/-- Remark 1(i) of the note: every `R`-clique `A` satisfies `|A| ≤ χ_op(R)`, because a clique
meets each `R`-free set of a cover at most once. -/
theorem encard_le_chiOp {R : X → X → Prop} {A : Set X} (hA : IsClique R A) :
    A.encard ≤ chiOp R := by
  refine le_sInf ?_
  rintro c ⟨U, hUfree, hUcover, rfl⟩
  -- send each point of `A` to a member of the cover containing it
  have hmem : ∀ a : X, ∃ V ∈ U, a ∈ V := by
    intro a
    obtain ⟨V, hV, haV⟩ := Set.mem_sUnion.mp (hUcover ▸ Set.mem_univ a)
    exact ⟨V, hV, haV⟩
  choose f hfU hfmem using hmem
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    by_contra hne
    exact (hUfree (f a) (hfU a)).2 a (hfmem a) b (hab ▸ hfmem b) (hA ha hb hne)
  calc A.encard = (f '' A).encard := (hinj.encard_image).symm
    _ ≤ U.encard := Set.encard_le_encard (by rintro _ ⟨a, -, rfl⟩; exact hfU a)

/-- Section 5 of the note, first implication: a compact space has finite open chromatic
number (this is what the proof of Lemma 1 actually shows). -/
theorem finiteOpenChromatic_of_compact [CompactSpace X] : FiniteOpenChromatic X := by
  intro R hR
  choose W hWopen hxW hWfree using hR.exists_rFree_nhds
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover W hWopen (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  have hle : chiOp R ≤ (W '' (s : Set X)).encard := by
    refine sInf_le ⟨W '' (s : Set X), ?_, ?_, rfl⟩
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨hWopen x, hWfree x⟩
    · refine Set.eq_univ_of_forall fun y => ?_
      have hy := hs (Set.mem_univ y)
      simp only [Set.mem_iUnion, exists_prop] at hy
      obtain ⟨x, hxs, hyx⟩ := hy
      exact ⟨W x, ⟨x, hxs, rfl⟩, hyx⟩
  have hcard : (W '' (s : Set X)).encard ≤ (s.card : ℕ∞) := by
    calc (W '' (s : Set X)).encard ≤ (s : Set X).encard := Set.encard_image_le _ _
      _ = s.card := by simp [Set.encard_coe_eq_coe_finsetCard]
  intro htop
  rw [htop] at hle
  exact (not_le.mpr (lt_of_le_of_lt hcard (WithTop.coe_lt_top _))) hle

/-- Section 5 of the note, second implication: a space with finite open chromatic number has
bounded cliques. -/
theorem boundedCliqueProperty_of_finiteOpenChromatic (hX : FiniteOpenChromatic X) :
    BoundedCliqueProperty X := by
  intro R hR
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hX R hR)
  exact ⟨n, fun A hA => hn ▸ encard_le_chiOp hA⟩

/-! ## The open questions of the note -/

/-- **Question 1** (`mainq`), the main open question of the note: is there a countably compact
`T1` space with a closed orthogonality relation having finite but unbounded cliques?  This
definition states the proposition whose truth value is asked for; it is left unresolved here, as
it is in the note. -/
def MainQuestion : Prop :=
  ∃ (Y : Type v) (_ : TopologicalSpace Y) (_ : T1Space Y) (R : Y → Y → Prop),
    CountablyCompact Y ∧ IsOrthogonality R ∧ HasFiniteCliques R ∧ ¬ HasBoundedCliques R

/-- **Remark 2 of the note**, the non-`T1` version of Question 1: is there an `ω`-limit point
compact space carrying a closed, irreflexive (hence, after symmetrization, orthogonality)
relation with cliques of arbitrary finite size?  This definition states the proposition whose
truth value is asked for; it is left unresolved here, as it is in the note. -/
def MainQuestionNonT1 : Prop :=
  ∃ (Y : Type v) (_ : TopologicalSpace Y) (R : Y → Y → Prop),
    OmegaLimitPointCompact Y ∧ IsOrthogonality R ∧ ¬ HasBoundedCliques R

/-- **Remark 2 of the note**: in the general, non-`T1` setting, it is not known whether
`ω`-limit point compactness is *necessary* for the finite clique property.  This definition
states the proposition whose truth value is asked for; it is left unresolved here, as it is in
the note. -/
def OmegaLimitPointCompactNecessaryQuestion : Prop :=
  ∀ (Y : Type v) (_ : TopologicalSpace Y), FiniteCliqueProperty Y → OmegaLimitPointCompact Y

/-- **Remark 3** (the dichotomy) of the note: either Question 1 has a positive answer, or the
bounded clique property coincides, for `T1` spaces, with countable compactness. -/
theorem mainQuestion_or_boundedCliqueProperty_iff_countablyCompact :
    (MainQuestion.{v}) ∨
      ∀ (Y : Type v) (_ : TopologicalSpace Y) (_ : T1Space Y),
        BoundedCliqueProperty Y ↔ CountablyCompact Y := by
  by_cases hq : MainQuestion.{v}
  · exact Or.inl hq
  refine Or.inr fun Y _ _ => ⟨fun hbcp => ?_, fun hcc => ?_⟩
  · exact (finiteCliqueProperty_iff_countablyCompact_t1).mp hbcp.finiteCliqueProperty
  · intro R hR
    by_contra hunb
    exact hq ⟨Y, inferInstance, inferInstance, R, hcc, hR,
      finiteCliqueProperty_of_countablyCompact hcc R hR, hunb⟩

/-- **Question 2** of Section 5 of the note: is the implication "finite open chromatic number ⇒
bounded cliques" strict, i.e. is there a space with bounded cliques but with a closed
orthogonality relation of infinite open chromatic number?  This definition states the
proposition whose truth value is asked for; it is left unresolved here, as it is in the note. -/
def ChromaticQuestion : Prop :=
  ∃ (Y : Type v) (_ : TopologicalSpace Y),
    BoundedCliqueProperty Y ∧ ¬ FiniteOpenChromatic Y

end CliqueSize
