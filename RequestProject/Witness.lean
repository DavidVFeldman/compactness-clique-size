import RequestProject.BetaOmega
import RequestProject.Chromatic
import RequestProject.Compactness

/-!
# A Note on Compactness and Clique Size — the conditional witness of Section 4

This file formalizes the final assertion of Section 4 of the source note *A Note on Compactness
and Clique Size* (D. V. Feldman and A. Wilce):

> *If there is a dense countably compact `Y ⊆ ω*` with `Y ⊆ G`, then `X := ω ∪ Y`, with
> `R := closure R₀ ∩ X²`, answers Question 1 positively*: `R` is a closed orthogonality on `X`
> (irreflexivity at points of `Y` is exactly `Y ⊆ G`; points of `ω` are isolated), the cells `A_n`
> are cliques of every size, and `X` is countably compact.  For density, it in fact suffices that
> `Y` meet `Ŝ` for every infinite partial section `S`, since every basic clopen `B̂` contains such
> an `Ŝ`.

Here `βω` is `Ultrafilter ℕ`, `ω` sits inside it as the principal ultrafilters, and the
hypotheses on `Y` are formalized as follows:

* `Y ⊆ ω*`: every `u ∈ Y` is free;
* `Y ⊆ G`: every `u ∈ Y` contains a partial section;
* density (in the weaker form the note says suffices): `Y` meets `Ŝ` for every infinite partial
  section `S`;
* countable compactness of `Y`: every infinite subset of `Y` has an `ω`-limit point in `Y`,
  measured with neighbourhoods in `βω` (equivalently, in the subspace `Y`).  This is the
  `ω`-limit point form of countable compactness, shown equivalent to it in
  `RequestProject/Compactness.lean`.

The conclusion is `MainQuestion` — the proposition of Question 1 of the note.
-/

namespace CliqueSize

namespace BetaOmega

open Set Filter Topology

variable (Y : Set (Ultrafilter ℕ))

/-- The space `X := ω ∪ Y` of Section 4 of the note, as a subset of `βω = Ultrafilter ℕ`. -/
def omegaUnion : Set (Ultrafilter ℕ) := {v | (∃ n : ℕ, v = pure n) ∨ v ∈ Y}

/-- The relation `R := closure R₀ ∩ X²` of Section 4 of the note, as a relation on
`X = ω ∪ Y`. -/
def RW : omegaUnion Y → omegaUnion Y → Prop :=
  fun a b => ((a : Ultrafilter ℕ), (b : Ultrafilter ℕ)) ∈ closure betaR0

variable {Y}

/-- In the candidate witness `X = ω ∪ Y` of Section 4 of the note, every point of `ω` (that is,
every principal ultrafilter) belongs to `X`. -/
theorem pure_mem_omegaUnion (n : ℕ) : (pure n : Ultrafilter ℕ) ∈ omegaUnion Y :=
  Or.inl ⟨n, rfl⟩

/-- Singletons are partial sections in the sense of Section 4 of the note; this is what makes the
points of `ω` harmless in the candidate witness `X = ω ∪ Y`. -/
theorem isPartialSection_singleton (n : ℕ) : IsPartialSection ({n} : Set ℕ) := by
  intro x hx y hy _
  rw [Set.mem_singleton_iff] at hx hy
  rw [hx, hy]

/-- Every member of a free ultrafilter on `ω` is infinite. -/
theorem infinite_of_mem_free {u : Ultrafilter ℕ} (hu : (u : Filter ℕ) ≤ Filter.cofinite)
    {C : Set ℕ} (hC : C ∈ u) : C.Infinite := by
  intro hfin
  have : Cᶜ ∈ u := hu (Filter.mem_cofinite.2 (by simpa using hfin))
  exact (u.compl_notMem_iff.2 hC) this

/-- The relation `R₀`, viewed inside `(βω)²`, is symmetric. -/
theorem swap_mem_betaR0 {p : Ultrafilter ℕ × Ultrafilter ℕ} (h : p ∈ betaR0) :
    p.swap ∈ betaR0 := by
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := h
  exact ⟨(y, x), ⟨Ne.symm hxy.1, hxy.2.symm⟩, rfl⟩

/-- The closure of `R₀` in `(βω)²` is symmetric, since `R₀` is. -/
theorem symmetric_closure_betaR0 {a b : Ultrafilter ℕ} (h : (a, b) ∈ closure betaR0) :
    (b, a) ∈ closure betaR0 := by
  have himg : Prod.swap '' betaR0 = betaR0 := by
    refine Set.Subset.antisymm ?_ fun p hp => ⟨p.swap, swap_mem_betaR0 hp, by simp⟩
    rintro _ ⟨p, hp, rfl⟩
    exact swap_mem_betaR0 hp
  have hsub := image_closure_subset_closure_image
    (f := (Prod.swap : Ultrafilter ℕ × Ultrafilter ℕ → Ultrafilter ℕ × Ultrafilter ℕ))
    (s := betaR0) continuous_swap
  rw [himg] at hsub
  exact hsub ⟨(a, b), h, rfl⟩

/-- Section 4 of the note: `R = closure R₀ ∩ X²` is a closed orthogonality relation on
`X = ω ∪ Y`.  Irreflexivity at points of `Y` is exactly the hypothesis `Y ⊆ G`; at points of `ω`
it holds because a singleton is a partial section. -/
theorem isOrthogonality_RW (hYG : ∀ u ∈ Y, ∃ S ∈ u, IsPartialSection S) :
    IsOrthogonality (RW Y) := by
  refine ⟨fun a b h => symmetric_closure_betaR0 h, ?_, ?_⟩
  · rintro ⟨v, hv⟩ h
    rw [RW, mem_closure_betaR0_iff] at h
    rcases hv with ⟨n, rfl⟩ | hvY
    · exact h {n} (Ultrafilter.mem_pure.2 rfl) (isPartialSection_singleton n)
    · obtain ⟨S, hSv, hSsec⟩ := hYG v hvY
      exact h S hSv hSsec
  · have hcont : Continuous fun p : omegaUnion Y × omegaUnion Y =>
        ((p.1 : Ultrafilter ℕ), (p.2 : Ultrafilter ℕ)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact isClosed_closure.preimage hcont

/-- Section 4 of the note: the cells `A_n` give `R`-cliques of every finite size inside
`X = ω ∪ Y`, so `R` does not have bounded cliques. -/
theorem not_hasBoundedCliques_RW : ¬ HasBoundedCliques (RW Y) := by
  rintro ⟨n, hn⟩
  set f : ℕ → omegaUnion Y := fun m => ⟨pure m, pure_mem_omegaUnion m⟩ with hf
  have hinj : Set.InjOn f (cell (n + 1) : Set ℕ) := by
    intro x _ y _ hxy
    have : (pure x : Ultrafilter ℕ) = pure y := congrArg Subtype.val hxy
    exact Ultrafilter.pure_injective this
  have hclique : IsClique (RW Y) (f '' (cell (n + 1) : Set ℕ)) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    have hxy : x ≠ y := fun h => hne (by rw [h])
    have : ((pure x : Ultrafilter ℕ), (pure y : Ultrafilter ℕ)) ∈ betaR0 :=
      ⟨(x, y), ⟨hxy, by rw [cellIndex_of_mem_cell hx, cellIndex_of_mem_cell hy]⟩, rfl⟩
    exact subset_closure this
  have hcard := hn _ hclique
  rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard, card_cell] at hcard
  exact absurd hcard (by exact_mod_cast by omega)

/-- An `ω`-limit point of a subset of a subspace, computed in the ambient space, is an
`ω`-limit point in the subspace. -/
theorem isOmegaLimitPoint_subtype {Z : Set (Ultrafilter ℕ)} {A : Set Z} {u : Z}
    (h : ∀ V ∈ 𝓝 (u : Ultrafilter ℕ), (V ∩ (Subtype.val '' A)).Infinite) :
    IsOmegaLimitPoint u A := by
  intro V hV
  rw [mem_nhds_subtype] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  have hsub : W ∩ (Subtype.val '' A) ⊆ Subtype.val '' (V ∩ A) := by
    rintro x ⟨hxW, a, haA, rfl⟩
    exact ⟨a, ⟨hWV hxW, haA⟩, rfl⟩
  exact Set.Infinite.of_image Subtype.val ((h W hW).mono hsub)

/-- Section 4 of the note: under the stated hypotheses on `Y`, the space `X = ω ∪ Y` is
`ω`-limit point compact, hence countably compact. -/
theorem omegaLimitPointCompact_omegaUnion
    (hYfree : ∀ u ∈ Y, (u : Filter ℕ) ≤ Filter.cofinite)
    (hYdense : ∀ S : Set ℕ, S.Infinite → IsPartialSection S → ∃ u ∈ Y, S ∈ u)
    (hYcc : ∀ A ⊆ Y, A.Infinite → ∃ u ∈ Y, ∀ V ∈ 𝓝 u, (V ∩ A).Infinite) :
    OmegaLimitPointCompact (omegaUnion Y) := by
  intro A hA
  by_cases hB : {n : ℕ | (pure n : Ultrafilter ℕ) ∈ Subtype.val '' A}.Infinite
  · -- infinitely many points of `A` come from `ω`
    obtain ⟨S, hSB, hSinf, hSsec⟩ := exists_infinite_isPartialSection_subset hB
    obtain ⟨u, huY, hSu⟩ := hYdense S hSinf hSsec
    refine ⟨⟨u, Or.inr huY⟩, isOmegaLimitPoint_subtype ?_⟩
    intro V hV
    obtain ⟨o, ho, huo, hoV⟩ := (ultrafilterBasis_is_basis (α := ℕ)).mem_nhds_iff.1 hV
    obtain ⟨C, rfl⟩ := ho
    have hCu : C ∈ u := huo
    have hCS : (C ∩ S).Infinite := infinite_of_mem_free (hYfree u huY) (Filter.inter_mem hCu hSu)
    have hmap : (fun n : ℕ => (pure n : Ultrafilter ℕ)) '' (C ∩ S) ⊆
        V ∩ (Subtype.val '' A) := by
      rintro _ ⟨n, ⟨hnC, hnS⟩, rfl⟩
      exact ⟨hoV (Ultrafilter.mem_pure.2 hnC), hSB hnS⟩
    exact Set.Infinite.mono hmap (hCS.image (Ultrafilter.pure_injective.injOn))
  · -- all but finitely many points of `A` lie in `Y`
    rw [Set.not_infinite] at hB
    have hAY : ((Subtype.val '' A) ∩ Y).Infinite := by
      have hsub : (Subtype.val '' A) \ ((fun n : ℕ => (pure n : Ultrafilter ℕ)) ''
          {n : ℕ | (pure n : Ultrafilter ℕ) ∈ Subtype.val '' A}) ⊆ (Subtype.val '' A) ∩ Y := by
        rintro v ⟨⟨a, haA, rfl⟩, hvnot⟩
        refine ⟨⟨a, haA, rfl⟩, ?_⟩
        rcases a.2 with ⟨n, hn⟩ | hY
        · refine absurd ⟨n, ?_, hn.symm⟩ hvnot
          show (pure n : Ultrafilter ℕ) ∈ Subtype.val '' A
          rw [← hn]
          exact ⟨a, haA, rfl⟩
        · exact hY
      refine Set.Infinite.mono hsub (Set.Infinite.diff ?_ (hB.image _))
      exact hA.image (Subtype.val_injective.injOn)
    obtain ⟨u, huY, hu⟩ := hYcc _ Set.inter_subset_right hAY
    refine ⟨⟨u, Or.inr huY⟩, isOmegaLimitPoint_subtype fun V hV => ?_⟩
    exact (hu V hV).mono (Set.inter_subset_inter_right _ Set.inter_subset_left)

/-- **Section 4 of the note**, the conditional construction: if there is a `Y ⊆ ω*` inside the
"good set" `G` (each of its members contains a partial section) which is countably compact and
meets `Ŝ` for every infinite partial section `S`, then `X := ω ∪ Y` with
`R := closure R₀ ∩ X²` answers Question 1 of the note positively. -/
theorem mainQuestion_of_exists_countablyCompact_dense_subset_goodSet
    (hYfree : ∀ u ∈ Y, (u : Filter ℕ) ≤ Filter.cofinite)
    (hYG : ∀ u ∈ Y, ∃ S ∈ u, IsPartialSection S)
    (hYdense : ∀ S : Set ℕ, S.Infinite → IsPartialSection S → ∃ u ∈ Y, S ∈ u)
    (hYcc : ∀ A ⊆ Y, A.Infinite → ∃ u ∈ Y, ∀ V ∈ 𝓝 u, (V ∩ A).Infinite) :
    MainQuestion.{0} := by
  have hcc : CountablyCompact (omegaUnion Y) :=
    omegaLimitPointCompact_iff_countablyCompact.1
      (omegaLimitPointCompact_omegaUnion hYfree hYdense hYcc)
  refine ⟨omegaUnion Y, inferInstance, inferInstance, RW Y, hcc, isOrthogonality_RW hYG, ?_,
    not_hasBoundedCliques_RW⟩
  exact finiteCliqueProperty_of_countablyCompact hcc _ (isOrthogonality_RW hYG)

end BetaOmega

end CliqueSize
