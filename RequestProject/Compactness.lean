import RequestProject.Basic

/-!
# A Note on Compactness and Clique Size — compactness notions and Lemma 2

This file formalizes the compactness notions used in Section 1 of the source note
*A Note on Compactness and Clique Size* (D. V. Feldman and A. Wilce), namely

* $\omega$-limit points and $\omega$-limit point compactness,
* (ordinary) limit point compactness,
* countable compactness,

together with

* the footnote claim that $\omega$-limit point compactness is equivalent to countable
  compactness for arbitrary spaces;
* the remark that in a $T_1$ space ordinary limit points are $\omega$-limit points;
* **Lemma 2** (`finitecc`) of the note and its consequence for $T_1$ spaces.
-/

namespace CliqueSize

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## Limit point notions -/

/-- **$\omega$-limit point** (Section 1 of the note): `x` is an $\omega$-limit point of `A ⊆ X`
iff every open neighbourhood of `x` has infinite intersection with `A`. -/
def IsOmegaLimitPoint (x : X) (A : Set X) : Prop := ∀ U ∈ 𝓝 x, (U ∩ A).Infinite

/-- **$\omega$-limit point compactness** (Section 1 of the note): every infinite subset of `X`
has an $\omega$-limit point. -/
def OmegaLimitPointCompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ A : Set X, A.Infinite → ∃ x : X, IsOmegaLimitPoint x A

/-- **Limit point compactness** (Section 1 of the note): every infinite subset of `X` has a
limit point, i.e. an accumulation point in the sense of `AccPt`. -/
def LimitPointCompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ A : Set X, A.Infinite → ∃ x : X, AccPt x (𝓟 A)

/-- **Countable compactness** (Section 1 of the note): every countable open cover of `X` has a
finite subcover. Countable covers are indexed by `ℕ`. -/
def CountablyCompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) → (⋃ n, U n) = Set.univ →
    ∃ N : ℕ, (⋃ n ∈ Finset.range N, U n) = Set.univ

/-- Every sequence in `X` has a cluster point.  This is the form in which countable compactness
is used in the proof of Theorem 1 of the note. -/
def SeqClusterCompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ z : ℕ → X, ∃ q : X, MapClusterPt q Filter.atTop z

/-- An unwinding of `SeqClusterCompact`: `q` is a cluster point of the sequence `z` iff every
neighbourhood of `q` contains `z k` for arbitrarily large `k`. -/
theorem mapClusterPt_atTop_iff {q : X} {z : ℕ → X} :
    MapClusterPt q Filter.atTop z ↔ ∀ U ∈ 𝓝 q, ∀ n : ℕ, ∃ k, n ≤ k ∧ z k ∈ U := by
  rw [mapClusterPt_iff_frequently]
  refine forall₂_congr fun U _ => ?_
  rw [Filter.frequently_atTop]

/-- An $\omega$-limit point of a set is in particular a limit point of that set
(Section 1 of the note). -/
theorem IsOmegaLimitPoint.accPt {x : X} {A : Set X} (h : IsOmegaLimitPoint x A) :
    AccPt x (𝓟 A) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨y, hy⟩ := ((h U hU).diff (Set.finite_singleton x)).nonempty
  exact ⟨y, hy.1, by simpa using hy.2⟩

/-- In a `T1` space, ordinary limit points are $\omega$-limit points (Section 1 of the note:
"In a $T_1$ space, ordinary limit points are also $\omega$-limit points"). -/
theorem AccPt.isOmegaLimitPoint [T1Space X] {x : X} {A : Set X} (h : AccPt x (𝓟 A)) :
    IsOmegaLimitPoint x A := by
  intro U hU
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hFfin : ((U ∩ A) \ {x}).Finite := hfin.diff
  have hmem : U \ ((U ∩ A) \ {x}) ∈ 𝓝 x := by
    refine Filter.inter_mem hU (hFfin.isClosed.isOpen_compl.mem_nhds ?_)
    simp
  obtain ⟨y, hy, hyx⟩ := (accPt_iff_nhds.mp h) _ hmem
  exact hy.1.2 ⟨⟨hy.1.1, hy.2⟩, hyx⟩

/-- In a `T1` space, limit point compactness and $\omega$-limit point compactness agree
(Section 1 of the note). -/
theorem limitPointCompact_iff_omegaLimitPointCompact [T1Space X] :
    LimitPointCompact X ↔ OmegaLimitPointCompact X := by
  constructor
  · intro h A hA
    obtain ⟨x, hx⟩ := h A hA
    exact ⟨x, AccPt.isOmegaLimitPoint hx⟩
  · intro h A hA
    obtain ⟨x, hx⟩ := h A hA
    exact ⟨x, hx.accPt⟩

/-! ## Countable compactness and $\omega$-limit point compactness

The footnote in Section 1 of the note asserts that, for arbitrary spaces, $\omega$-limit point
compactness is equivalent to countable compactness. Both directions are proved below. -/

/-- First half of the footnote in Section 1 of the note, in its sequential form: in a countably
compact space every sequence has a cluster point.  (This is the form of countable compactness
actually used in the proof of Theorem 1 of the note.) -/
theorem CountablyCompact.seqClusterCompact (hX : CountablyCompact X) :
    SeqClusterCompact X := by
  intro a
  -- the closed sets `F n = closure {a k | k ≥ n}` are nested and nonempty
  set F : ℕ → Set X := fun n => closure {x | ∃ k, n ≤ k ∧ a k = x} with hFdef
  have hFclosed : ∀ n, IsClosed (F n) := fun n => isClosed_closure
  have hmemF : ∀ n, a n ∈ F n := fun n => subset_closure ⟨n, le_rfl, rfl⟩
  have hanti : Antitone F := by
    intro m n hmn
    exact closure_mono (fun x hx => ⟨hx.choose, le_trans hmn hx.choose_spec.1,
      hx.choose_spec.2⟩)
  have hnonempty : (⋂ n, F n).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hcover : (⋃ n, (F n)ᶜ) = Set.univ := by
      rw [← Set.compl_iInter, hempty, Set.compl_empty]
    obtain ⟨N, hN⟩ := hX (fun n => (F n)ᶜ) (fun n => (hFclosed n).isOpen_compl) hcover
    have hmem : a N ∈ (⋃ n ∈ Finset.range N, (F n)ᶜ) := hN ▸ Set.mem_univ _
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Finset.mem_range, exists_prop] at hmem
    obtain ⟨n, hn, hna⟩ := hmem
    exact hna (hanti (le_of_lt hn) (hmemF N))
  obtain ⟨x, hx⟩ := hnonempty
  refine ⟨x, mapClusterPt_atTop_iff.mpr fun U hU n => ?_⟩
  obtain ⟨y, hyU, k, hk, hky⟩ := mem_closure_iff_nhds.mp (Set.mem_iInter.mp hx n) U hU
  exact ⟨k, hk, by rw [hky]; exact hyU⟩

/-- A space in which every sequence has a cluster point is $\omega$-limit point compact
(Section 1 of the note). -/
theorem SeqClusterCompact.omegaLimitPointCompact (hX : SeqClusterCompact X) :
    OmegaLimitPointCompact X := by
  intro A hA
  -- choose a countable injective sequence inside `A`
  set e := Set.Infinite.natEmbedding A hA with he
  set a : ℕ → X := fun n => (e n : X) with hadef
  have ha : ∀ n, a n ∈ A := fun n => (e n).2
  have hainj : Function.Injective a := fun i j hij => e.injective (Subtype.ext hij)
  obtain ⟨x, hx⟩ := hX a
  rw [mapClusterPt_atTop_iff] at hx
  refine ⟨x, fun U hU => ?_⟩
  -- the indices `k` with `a k ∈ U` are unbounded, hence infinite, and `a` is injective
  have hidx : {k : ℕ | a k ∈ U}.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨N, hN⟩
    obtain ⟨k, hk, hkU⟩ := hx U hU (N + 1)
    have := hN (show k ∈ {k : ℕ | a k ∈ U} from hkU)
    omega
  have hsub : a '' {k : ℕ | a k ∈ U} ⊆ U ∩ A := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨hk, ha k⟩
  exact ((hidx.image (fun i _ j _ hij => hainj hij)).mono hsub)

/-- First half of the footnote in Section 1 of the note: a countably compact space is
$\omega$-limit point compact. -/
theorem CountablyCompact.omegaLimitPointCompact (hX : CountablyCompact X) :
    OmegaLimitPointCompact X :=
  hX.seqClusterCompact.omegaLimitPointCompact

/-- Second half of the footnote in Section 1 of the note: an $\omega$-limit point compact space is
countably compact. -/
theorem OmegaLimitPointCompact.countablyCompact (hX : OmegaLimitPointCompact X) :
    CountablyCompact X := by
  intro U hUopen hUcover
  by_contra hno
  push_neg at hno
  -- `V n = U 0 ∪ ⋯ ∪ U n` is an increasing sequence of proper open sets with union `X`
  set V : ℕ → Set X := fun n => ⋃ k ∈ Finset.range (n + 1), U k with hVdef
  have hVopen : ∀ n, IsOpen (V n) := fun n => isOpen_biUnion fun k _ => hUopen k
  have hVne : ∀ n, V n ≠ Set.univ := fun n => hno (n + 1)
  have hVmono : Monotone V := by
    intro m n hmn
    refine Set.iUnion₂_subset fun k hk => ?_
    simp only [Finset.mem_range] at hk
    exact Set.subset_biUnion_of_mem (u := U) (Finset.mem_range.mpr (by omega))
  have hcov : ∀ p : X, ∃ N, p ∈ V N := by
    intro p
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hUcover ▸ Set.mem_univ p)
    exact ⟨n, Set.mem_biUnion (Finset.self_mem_range_succ n) hn⟩
  have hchoice : ∀ n, ∃ p : X, p ∉ V n := by
    intro n
    by_contra hall
    push_neg at hall
    exact hVne n (Set.eq_univ_of_forall hall)
  choose x hx using hchoice
  set A : Set X := Set.range x with hAdef
  -- each point of `X` occurs only finitely often in the sequence
  have hfew : ∀ p : X, ∀ N : ℕ, p ∈ V N → ∀ n, N ≤ n → x n ≠ p := by
    intro p N hp n hn hxp
    exact hx n (hxp ▸ hVmono hn hp)
  have hAinf : A.Infinite := by
    intro hfinA
    obtain ⟨p, hp⟩ : ∃ p : X, {n : ℕ | x n = p}.Infinite := by
      by_contra hcon
      push_neg at hcon
      have huniv : (Set.univ : Set ℕ) = ⋃ p ∈ A, {n : ℕ | x n = p} := by
        ext n
        simp [hAdef]
      exact Set.infinite_univ (α := ℕ)
        (huniv ▸ Set.Finite.biUnion hfinA fun p _ => hcon p)
    obtain ⟨N, hN⟩ := hcov p
    obtain ⟨n, hn, hnN⟩ := hp.exists_gt N
    exact hfew p N hN n (le_of_lt hnN) hn
  obtain ⟨q, hq⟩ := hX A hAinf
  obtain ⟨N, hN⟩ := hcov q
  have hinf := hq (V N) ((hVopen N).mem_nhds hN)
  -- but `V N ∩ A` is contained in the finite set `{x 0, …, x (N-1)}`
  have hsub : V N ∩ A ⊆ x '' (Set.Iio N) := by
    rintro y ⟨hyV, n, rfl⟩
    by_cases hn : n < N
    · exact ⟨n, hn, rfl⟩
    · exact absurd rfl (hfew (x n) N hyV n (by omega))
  exact hinf (Set.Finite.subset ((Set.finite_Iio N).image x) hsub)

/-- The footnote equivalence of Section 1 of the note: for an arbitrary space, $\omega$-limit
point compactness is equivalent to countable compactness. -/
theorem omegaLimitPointCompact_iff_countablyCompact :
    OmegaLimitPointCompact X ↔ CountablyCompact X :=
  ⟨fun h => h.countablyCompact, fun h => h.omegaLimitPointCompact⟩

/-! ## Lemma 2 -/

/-- The relation used in the proof of Lemma 2(a) of the note: for a closed set `A` all of whose
points are isolated in `A` (i.e. a closed discrete set), the relation `A × A \ Δ_A` is a closed
orthogonality relation. -/
theorem isOrthogonality_of_closed_discrete {A : Set X} (hAclosed : IsClosed A)
    (hAdisc : ∀ a ∈ A, ∃ U ∈ 𝓝 a, U ∩ A = {a}) :
    IsOrthogonality (fun y z : X => y ∈ A ∧ z ∈ A ∧ y ≠ z) := by
  refine ⟨fun y z h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun y h => h.2.2 rfl, ?_⟩
  rw [← isOpen_compl_iff, isOpen_prod_iff]
  intro y z hyz
  by_cases hy : y ∈ A
  · by_cases hz : z ∈ A
    · -- then necessarily `y = z`, and we use discreteness at `y`
      have hyzeq : y = z := by
        by_contra hne
        exact hyz ⟨hy, hz, hne⟩
      subst hyzeq
      obtain ⟨U, hU, hUA⟩ := hAdisc y hy
      obtain ⟨W, hWsub, hWopen, hyW⟩ := mem_nhds_iff.mp hU
      refine ⟨W, W, hWopen, hWopen, hyW, hyW, ?_⟩
      rintro ⟨p, q⟩ ⟨hp, hq⟩ hpq
      have hpy : p = y := by
        have : p ∈ U ∩ A := ⟨hWsub hp, hpq.1⟩
        simpa [hUA] using this
      have hqy : q = y := by
        have : q ∈ U ∩ A := ⟨hWsub hq, hpq.2.1⟩
        simpa [hUA] using this
      exact hpq.2.2 (by rw [hpy, hqy])
    · refine ⟨Set.univ, Aᶜ, isOpen_univ, hAclosed.isOpen_compl, Set.mem_univ _, hz, ?_⟩
      rintro ⟨p, q⟩ ⟨-, hq⟩ hpq
      exact hq hpq.2.1
  · refine ⟨Aᶜ, Set.univ, hAclosed.isOpen_compl, isOpen_univ, hy, Set.mem_univ _, ?_⟩
    rintro ⟨p, q⟩ ⟨hp, -⟩ hpq
    exact hp hpq.1

/-- **Lemma 2(a)** of the note: if `X` has finite cliques, then `X` is limit point compact. -/
theorem limitPointCompact_of_finiteCliqueProperty (hX : FiniteCliqueProperty X) :
    LimitPointCompact X := by
  intro A hA
  by_contra hno
  push_neg at hno
  -- `A` has no limit point, hence is closed and discrete
  have hdisc : ∀ a : X, ∃ U ∈ 𝓝 a, U ∩ (A \ {a}) = ∅ := by
    intro a
    have hacc := hno a
    rw [accPt_iff_nhds] at hacc
    push_neg at hacc
    obtain ⟨U, hU, hUA⟩ := hacc
    refine ⟨U, hU, ?_⟩
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro y ⟨hyU, hyA, hya⟩
    exact hya (hUA y ⟨hyU, hyA⟩)
  have hAclosed : IsClosed A := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    by_contra hyA
    obtain ⟨U, hU, hUA⟩ := hdisc y
    obtain ⟨z, hzU, hzA⟩ := mem_closure_iff_nhds.mp hy U hU
    have hmem : z ∈ U ∩ (A \ {y}) := ⟨hzU, hzA, fun h => hyA (h ▸ hzA)⟩
    rw [hUA] at hmem
    exact hmem
  have hdisc' : ∀ a ∈ A, ∃ U ∈ 𝓝 a, U ∩ A = {a} := by
    intro a ha
    obtain ⟨U, hU, hUA⟩ := hdisc a
    refine ⟨U, hU, Set.Subset.antisymm ?_ ?_⟩
    · rintro y ⟨hyU, hyA⟩
      by_contra hya
      have hmem : y ∈ U ∩ (A \ {a}) := ⟨hyU, hyA, hya⟩
      rw [hUA] at hmem
      exact hmem
    · rintro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨mem_of_mem_nhds hU, ha⟩
  have hortho := isOrthogonality_of_closed_discrete hAclosed hdisc'
  have hclique : IsClique (fun y z : X => y ∈ A ∧ z ∈ A ∧ y ≠ z) A :=
    fun _ hy _ hz hyz => ⟨hy, hz, hyz⟩
  exact hA (hX _ hortho A hclique)

/-- **Lemma 2(b)** of the note: if `X` is $\omega$-limit point compact (equivalently, countably
compact), then `X` has finite cliques. -/
theorem finiteCliqueProperty_of_omegaLimitPointCompact (hX : OmegaLimitPointCompact X) :
    FiniteCliqueProperty X := by
  intro R hR A hA
  rcases A.finite_or_infinite with hfin | hAinf
  · exact hfin
  exfalso
  obtain ⟨x, hx⟩ := hX A hAinf
  -- `(x, x)` lies in the closure of `R`, contradicting irreflexivity and closedness
  have hmem : (x, x) ∈ closure {p : X × X | R p.1 p.2} := by
    rw [mem_closure_iff_nhds]
    intro N hN
    obtain ⟨U, V, hUopen, hxU, hVopen, hxV, hUV⟩ := mem_nhds_prod_iff'.mp hN
    have hinf : ((U ∩ V) ∩ A).Infinite := hx (U ∩ V) ((hUopen.inter hVopen).mem_nhds ⟨hxU, hxV⟩)
    obtain ⟨y, hy, z, hz, hyz⟩ := hinf.nontrivial
    exact ⟨(y, z), hUV (Set.mk_mem_prod hy.1.1 hz.1.2), hA hy.2 hz.2 hyz⟩
  rw [hR.isClosed.closure_eq] at hmem
  exact hR.irrefl x hmem

/-- **Lemma 2** of the note, second consequence: a countably compact space has finite cliques. -/
theorem finiteCliqueProperty_of_countablyCompact (hX : CountablyCompact X) :
    FiniteCliqueProperty X :=
  finiteCliqueProperty_of_omegaLimitPointCompact hX.omegaLimitPointCompact

/-- **Lemma 2** of the note, final statement: a `T1` space has finite cliques iff it is limit
point compact iff it is countably compact. -/
theorem finiteCliqueProperty_iff_limitPointCompact_t1 [T1Space X] :
    FiniteCliqueProperty X ↔ LimitPointCompact X := by
  refine ⟨limitPointCompact_of_finiteCliqueProperty, fun h => ?_⟩
  exact finiteCliqueProperty_of_omegaLimitPointCompact
    (limitPointCompact_iff_omegaLimitPointCompact.mp h)

/-- **Lemma 2** of the note, final statement: a `T1` space has finite cliques iff it is countably
compact. -/
theorem finiteCliqueProperty_iff_countablyCompact_t1 [T1Space X] :
    FiniteCliqueProperty X ↔ CountablyCompact X := by
  rw [finiteCliqueProperty_iff_limitPointCompact_t1,
    limitPointCompact_iff_omegaLimitPointCompact, omegaLimitPointCompact_iff_countablyCompact]

end CliqueSize
