import RequestProject.Powers

/-!
# A Note on Compactness and Clique Size — Section 4: The structure of the problem

This file formalizes the preservation results of Section 4 of the source note
*A Note on Compactness and Clique Size* (D. V. Feldman and A. Wilce):

* **Proposition 2** (`preserve`): bounded cliques is closed-hereditary and is preserved by
  continuous surjections;
* **Proposition 3** (`separable`): separable reflection for the main question.
-/

universe u

namespace CliqueSize

open Set Filter Topology

variable {X : Type u} [TopologicalSpace X]

/-! ## Auxiliary: closed subspaces -/

/-- A closed subspace of an $\omega$-limit point compact space is $\omega$-limit point compact.
(Used for the countable compactness of the subspace `Y` in Proposition 3 of the note.) -/
theorem OmegaLimitPointCompact.of_isClosed (hX : OmegaLimitPointCompact X) {C : Set X}
    (hC : IsClosed C) : OmegaLimitPointCompact C := by
  intro A hA
  have hAimg : (Subtype.val '' A : Set X).Infinite :=
    hA.image (Set.injOn_of_injective Subtype.val_injective)
  obtain ⟨x, hx⟩ := hX _ hAimg
  have hxC : x ∈ C := by
    have hxcl : x ∈ closure (Subtype.val '' A : Set X) :=
      mem_closure_iff_nhds.mpr fun U hU => (hx U hU).nonempty
    refine hC.closure_subset_iff.mpr ?_ hxcl
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  refine ⟨⟨x, hxC⟩, fun U hU => ?_⟩
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype C ⟨x, hxC⟩ U).mp hU
  have hinf : (V ∩ Subtype.val '' A).Infinite := hx V hV
  have hsub : V ∩ Subtype.val '' A ⊆ (Subtype.val '' (U ∩ A) : Set X) := by
    rintro y ⟨hyV, ⟨a, haA, rfl⟩⟩
    exact ⟨a, ⟨hVU hyV, haA⟩, rfl⟩
  exact (hinf.mono hsub).of_image _

/-! ## Proposition 2: preservation -/

/-- **Proposition 2(i)** (`preserve`) of the note: bounded cliques is closed-hereditary. -/
theorem BoundedCliqueProperty.of_isClosed (hX : BoundedCliqueProperty X) {C : Set X}
    (hC : IsClosed C) : BoundedCliqueProperty C := by
  intro R hR
  -- extend `R` to `X` by declaring points outside `C` unrelated
  set R' : X → X → Prop := fun a b => ∃ (ha : a ∈ C) (hb : b ∈ C), R ⟨a, ha⟩ ⟨b, hb⟩ with hR'
  have hR'ortho : IsOrthogonality R' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro a b ⟨ha, hb, hab⟩
      exact ⟨hb, ha, hR.symm hab⟩
    · rintro a ⟨ha, ha', haa⟩
      exact hR.irrefl ⟨a, ha⟩ haa
    · have hind : Topology.IsInducing (Prod.map (Subtype.val : C → X) (Subtype.val : C → X)) :=
        Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal
      obtain ⟨t, htclosed, hteq⟩ := hind.isClosed_iff.mp hR.isClosed
      have hset : {p : X × X | R' p.1 p.2} = t ∩ (C ×ˢ C) := by
        ext ⟨a, b⟩
        constructor
        · rintro ⟨ha, hb, hab⟩
          have hmem : ((⟨a, ha⟩ : C), (⟨b, hb⟩ : C)) ∈ {q : C × C | R q.1 q.2} := hab
          rw [← hteq] at hmem
          exact ⟨hmem, ha, hb⟩
        · rintro ⟨ht, ha, hb⟩
          refine ⟨ha, hb, ?_⟩
          have hmem : ((⟨a, ha⟩ : C), (⟨b, hb⟩ : C)) ∈
              (Prod.map (Subtype.val : C → X) (Subtype.val : C → X)) ⁻¹' t := ht
          rw [hteq] at hmem
          exact hmem
      rw [hset]
      exact htclosed.inter (hC.prod hC)
  obtain ⟨n, hn⟩ := hX R' hR'ortho
  refine ⟨n, fun A hA => ?_⟩
  have himg : IsClique R' (Subtype.val '' A) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact ⟨a.2, b.2, by simpa using hA ha hb (fun h => hab (by rw [h]))⟩
  calc A.encard = (Subtype.val '' A).encard :=
        ((Set.injOn_of_injective Subtype.val_injective).encard_image).symm
    _ ≤ n := hn _ himg

/-- **Proposition 2(ii)** (`preserve`) of the note: bounded cliques is preserved by continuous
surjections. -/
theorem BoundedCliqueProperty.image {Y : Type*} [TopologicalSpace Y] (hX : BoundedCliqueProperty X)
    {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    BoundedCliqueProperty Y := by
  intro R hR
  -- the pullback of `R` along `f`
  set R' : X → X → Prop := fun a b => R (f a) (f b) with hR'
  have hR'ortho : IsOrthogonality R' := by
    refine ⟨fun a b hab => hR.symm hab, fun a h => hR.irrefl (f a) h, ?_⟩
    exact hR.isClosed.preimage (hf.prodMap hf)
  obtain ⟨n, hn⟩ := hX R' hR'ortho
  refine ⟨n, fun A hA => ?_⟩
  -- choose a preimage for each element of an `R`-clique
  choose g hg using hsurj
  have hginj : Set.InjOn g A := by
    intro a _ b _ hab
    rw [← hg a, ← hg b, hab]
  have hclique : IsClique R' (g '' A) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have hne : a ≠ b := fun h => hab (by rw [h])
    simpa [hR', hg] using hA ha hb hne
  calc A.encard = (g '' A).encard := (hginj.encard_image).symm
    _ ≤ n := hn _ hclique

/-! ## Proposition 3: separable reflection -/

/-- **Proposition 3** (`separable`) of the note: if some countably compact `T1` space carries a
closed orthogonality relation with finite, unbounded cliques, then some *separable* such space
does. -/
theorem separable_reflection [T1Space X] (hcc : CountablyCompact X) {R : X → X → Prop}
    (hR : IsOrthogonality R) (hfin : HasFiniteCliques R) (hunb : ¬ HasBoundedCliques R) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T1Space Y)
      (_ : TopologicalSpace.SeparableSpace Y) (S : Y → Y → Prop),
      CountablyCompact Y ∧ IsOrthogonality S ∧ HasFiniteCliques S ∧ ¬ HasBoundedCliques S := by
  -- arbitrarily large finite cliques
  have hne : Nonempty X := by
    simp only [HasBoundedCliques, not_exists, not_forall] at hunb
    obtain ⟨A, hA, hA0⟩ := hunb 0
    have hAne : A.Nonempty := by
      rw [← Set.encard_ne_zero]
      intro h0
      exact hA0 (by simp [h0])
    exact ⟨hAne.choose⟩
  obtain ⟨x, hx⟩ := exists_clique_enumeration hunb
  -- the countable set `D` of all the points involved, and its closure `Y`
  set D : Set X := Set.range (fun p : ℕ × ℕ => x p.1 p.2) with hD
  have hDcount : D.Countable := Set.countable_range _
  set Y : Set X := closure D with hY
  have hYclosed : IsClosed Y := isClosed_closure
  have hDY : D ⊆ Y := subset_closure
  refine ⟨Y, inferInstance, inferInstance, ?_, fun a b => R (a : X) (b : X), ?_, ?_, ?_, ?_⟩
  · -- separability: the trace of `D` on `Y` is countable and dense
    refine ⟨⟨Subtype.val ⁻¹' D, hDcount.preimage Subtype.val_injective, ?_⟩⟩
    refine dense_iff_inter_open.mpr fun U hU hUne => ?_
    obtain ⟨V, hVopen, rfl⟩ := (Topology.IsInducing.subtypeVal.isOpen_iff).mp hU
    obtain ⟨y, hyV⟩ := hUne
    have hyY : (y : X) ∈ closure D := y.2
    obtain ⟨d, hdV, hdD⟩ := mem_closure_iff.mp hyY V hVopen hyV
    exact ⟨⟨d, hDY hdD⟩, hdV, hdD⟩
  · -- countable compactness of the closed subspace `Y`
    exact (hcc.omegaLimitPointCompact.of_isClosed hYclosed).countablyCompact
  · -- the restricted relation is a closed orthogonality
    refine ⟨fun a b hab => hR.symm hab, fun a h => hR.irrefl (a : X) h, ?_⟩
    exact hR.isClosed.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  · -- its cliques are finite, being cliques of `R`
    intro A hA
    have himg : IsClique R (Subtype.val '' A) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      exact hA ha hb (fun h => hab (by rw [h]))
    exact (hfin _ himg).of_finite_image (Set.injOn_of_injective Subtype.val_injective)
  · -- but they are unbounded, since all the cliques `C_n` lie in `Y`
    simp only [HasBoundedCliques, not_exists, not_forall]
    intro n
    have hmemY : ∀ i, x n i ∈ Y := fun i => hDY ⟨(n, i), rfl⟩
    have hinj : Set.InjOn (fun i : ℕ => (⟨x n i, hmemY i⟩ : Y)) ↑(Finset.Iic n) := by
      intro i hi j hj hij
      simp only [Finset.coe_Iic, Set.mem_Iic] at hi hj
      by_contra hne'
      have hRij := hx n i j hi hj hne'
      have hxx : x n i = x n j := congrArg Subtype.val hij
      rw [hxx] at hRij
      exact hR.irrefl (x n j) hRij
    refine ⟨(fun i : ℕ => (⟨x n i, hmemY i⟩ : Y)) '' ↑(Finset.Iic n), ?_, ?_⟩
    · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hab
      simp only [Finset.coe_Iic, Set.mem_Iic] at hi hj
      exact hx n i j hi hj (fun h => hab (by rw [h]))
    · rw [hinj.encard_image]
      simp only [Set.encard_coe_eq_coe_finsetCard, Nat.card_Iic, not_le]
      exact_mod_cast Nat.lt_succ_self n

end CliqueSize
