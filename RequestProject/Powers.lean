import RequestProject.Covers

/-!
# A Note on Compactness and Clique Size — Section 3: Cliques and Powers

This file formalizes Section 3 of the source note *A Note on Compactness and Clique Size*
(D. V. Feldman and A. Wilce):

* **Theorem 1** (`omegapower`): if `X^ω` is countably compact then `X` has bounded cliques;
* **Corollary 4** (`suffconds`): each of (a) sequential compactness, (b) $\omega$-boundedness,
  (c) $\mathfrak u$-compactness for a free ultrafilter $\mathfrak u$ on $\omega$, implies that
  `X` has bounded cliques.
-/

namespace CliqueSize

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## Extracting arbitrarily large finite cliques -/

omit [TopologicalSpace X] in
/-- If `R` fails to have bounded cliques then, for every `n`, there are `n + 1` distinct,
pairwise `R`-related points `x n 0, …, x n n`: this is the family of cliques
`C_n = {x^n_1, …, x^n_n}` used in the proof of Theorem 1 of the note. -/
theorem exists_clique_enumeration [Nonempty X] {R : X → X → Prop} (h : ¬ HasBoundedCliques R) :
    ∃ x : ℕ → ℕ → X, ∀ n i j : ℕ, i ≤ n → j ≤ n → i ≠ j → R (x n i) (x n j) := by
  simp only [HasBoundedCliques, not_exists, not_forall] at h
  have key : ∀ n : ℕ, ∃ f : ℕ → X, ∀ i j : ℕ, i ≤ n → j ≤ n → i ≠ j → R (f i) (f j) := by
    intro n
    obtain ⟨A, hA, hAn⟩ := h n
    have hlt : (n : ℕ∞) < A.encard := not_le.mp hAn
    have hle : ((n : ℕ∞) + 1) ≤ A.encard := Order.add_one_le_of_lt hlt
    have hcard : (Set.univ : Set (Fin (n + 1))).encard ≤ A.encard := by
      simpa [Set.encard_univ, Nat.cast_add] using hle
    obtain ⟨g, hgmap, hginj⟩ :=
      (Set.finite_univ (α := Fin (n + 1))).exists_injOn_of_encard_le hcard
    refine ⟨fun i => g ⟨min i n, by omega⟩, fun i j hi hj hij => ?_⟩
    have hne : (⟨min i n, by omega⟩ : Fin (n + 1)) ≠ ⟨min j n, by omega⟩ := by
      simp only [ne_eq, Fin.mk.injEq]
      omega
    refine hA (hgmap (Set.mem_univ _)) (hgmap (Set.mem_univ _)) fun hEq => hne ?_
    exact hginj (Set.mem_univ _) (Set.mem_univ _) hEq
  choose x hx using key
  exact ⟨x, hx⟩

/-! ## Theorem 1 -/

/-- The core of **Theorem 1** (`omegapower`) of the note, using countable compactness of `X^ω`
in the form actually consumed by the proof: if every sequence in `X^ω` has a cluster point,
then `X` has bounded cliques. -/
theorem boundedCliqueProperty_of_seqClusterCompact_pi (h : SeqClusterCompact (ℕ → X)) :
    BoundedCliqueProperty X := by
  -- `X` itself has all sequences clustering, being a continuous image of `X^ω`
  intro R hR
  by_contra hbdd
  have hne : Nonempty X := by
    simp only [HasBoundedCliques, not_exists, not_forall] at hbdd
    obtain ⟨A, hA, hA0⟩ := hbdd 0
    have : A.Nonempty := by
      rw [← Set.encard_ne_zero]
      intro h0
      exact hA0 (by simp [h0])
    exact ⟨this.choose⟩
  obtain ⟨x, hx⟩ := exists_clique_enumeration hbdd
  -- the sequence `y_n` of the proof of Theorem 1
  set g : ℕ → (ℕ → X) := fun n i => x n (min i n) with hg
  obtain ⟨q, hq⟩ := h g
  rw [mapClusterPt_atTop_iff] at hq
  -- every two distinct coordinates of a cluster point `q` are `R`-related
  have hqR : ∀ i j : ℕ, i ≠ j → R (q i) (q j) := by
    intro i j hij
    have hmem : (q i, q j) ∈ closure {p : X × X | R p.1 p.2} := by
      rw [mem_closure_iff_nhds]
      intro N hN
      obtain ⟨U, V, hUopen, hqU, hVopen, hqV, hUV⟩ := mem_nhds_prod_iff'.mp hN
      have hW : ((fun z : ℕ → X => z i) ⁻¹' U) ∩ ((fun z : ℕ → X => z j) ⁻¹' V) ∈ 𝓝 q :=
        Filter.inter_mem ((continuous_apply i).continuousAt.preimage_mem_nhds
            (hUopen.mem_nhds hqU))
          ((continuous_apply j).continuousAt.preimage_mem_nhds (hVopen.mem_nhds hqV))
      obtain ⟨k, hk, hgk⟩ := hq _ hW (max i j)
      have hik : i ≤ k := le_trans (le_max_left i j) hk
      have hjk : j ≤ k := le_trans (le_max_right i j) hk
      refine ⟨(x k i, x k j), hUV ?_, hx k i j hik hjk hij⟩
      refine Set.mk_mem_prod ?_ ?_
      · have := hgk.1
        simpa [hg, min_eq_left hik] using this
      · have := hgk.2
        simpa [hg, min_eq_left hjk] using this
    rw [hR.isClosed.closure_eq] at hmem
    exact hmem
  -- hence the coordinates of `q` form an infinite `R`-clique
  have hqinj : Function.Injective q := by
    intro i j hij
    by_contra hne'
    exact hR.irrefl (q i) (hij ▸ hqR i j hne')
  have hclique : IsClique R (Set.range q) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne'
    exact hqR i j fun hij => hne' (by rw [hij])
  -- but `X` has finite cliques, since every sequence in `X` has a cluster point
  have hXcl : SeqClusterCompact X := by
    intro z
    obtain ⟨Q, hQ⟩ := h (fun n _ => z n)
    exact ⟨Q 0, MapClusterPt.continuousAt_comp (continuous_apply (0 : ℕ)).continuousAt hQ⟩
  have hfin := finiteCliqueProperty_of_omegaLimitPointCompact hXcl.omegaLimitPointCompact
    R hR (Set.range q) hclique
  exact (Set.infinite_range_of_injective hqinj) hfin

/-- **Theorem 1** (`omegapower`) of the note: if `X^ω` is countably compact, then `X` has
bounded cliques. -/
theorem boundedCliqueProperty_of_countablyCompact_pi (h : CountablyCompact (ℕ → X)) :
    BoundedCliqueProperty X :=
  boundedCliqueProperty_of_seqClusterCompact_pi h.seqClusterCompact

/-! ## Corollary 4 -/

/-- Corollary 4(a) of the note, key step: a countable power of a sequentially compact space has
the property that every sequence in it has a cluster point (sequential compactness is countably
productive, by the usual diagonal argument). -/
theorem seqClusterCompact_pi_of_seqCompactSpace [SeqCompactSpace X] :
    SeqClusterCompact (ℕ → X) := by
  intro Z
  -- successively extract subsequences making more and more coordinates converge
  have step : ∀ (w : ℕ → ℕ) (i : ℕ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ l : X, Tendsto (fun n => Z (w (φ n)) i) atTop (𝓝 l) := by
    intro w i
    obtain ⟨l, φ, hφ, hconv⟩ := SeqCompactSpace.tendsto_subseq (fun n => Z (w n) i)
    exact ⟨φ, hφ, l, hconv⟩
  choose φ hφmono l hl using step
  -- `e i` is the extraction obtained after `i` successive steps
  let e : ℕ → (ℕ → ℕ) := fun i => Nat.rec (id : ℕ → ℕ) (fun i wi => wi ∘ φ wi i) i
  have hesucc : ∀ i, e (i + 1) = e i ∘ φ (e i) i := fun _ => rfl
  have hemono : ∀ i, StrictMono (e i) := by
    intro i
    induction i with
    | zero => exact strictMono_id
    | succ i ih => exact ih.comp (hφmono (e i) i)
  have hanti : Antitone (fun i => Set.range (e i)) := by
    refine antitone_nat_of_succ_le fun i => ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨φ (e i) i n, rfl⟩
  -- the `i`-th coordinate converges along the `(i+1)`-st extraction
  set q : ℕ → X := fun i => l (e i) i with hqdef
  have hconv : ∀ i, Tendsto (fun n => Z (e (i + 1) n) i) atTop (𝓝 (q i)) := fun i => hl (e i) i
  -- the filter generated by the tails of `ℕ` together with the ranges of the extractions
  set F : Filter ℕ := ⨅ i, (atTop ⊓ 𝓟 (Set.range (e i))) with hF
  have hFle : ∀ i, F ≤ atTop ⊓ 𝓟 (Set.range (e i)) := fun i => iInf_le _ i
  have hFatTop : F ≤ atTop := le_trans (hFle 0) inf_le_left
  have hFne : F.NeBot := by
    refine Filter.iInf_neBot_of_directed ?_ ?_
    · intro i j
      exact ⟨max i j, inf_le_inf_left _ (Filter.principal_mono.2 (hanti (le_max_left i j))),
        inf_le_inf_left _ (Filter.principal_mono.2 (hanti (le_max_right i j)))⟩
    · intro i
      refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
      obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp hU
      exact ⟨e i N, hN _ (hemono i).le_apply, ⟨N, rfl⟩⟩
  have htend : Tendsto Z F (𝓝 q) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [Filter.tendsto_def]
    intro U hU
    obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (hconv i hU)
    have hmem : (Set.Ici (e (i + 1) N) ∩ Set.range (e (i + 1))) ∈
        atTop ⊓ 𝓟 (Set.range (e (i + 1))) :=
      Filter.inter_mem_inf (Filter.Ici_mem_atTop _) (Filter.mem_principal_self _)
    refine Filter.mem_of_superset (hFle (i + 1) hmem) ?_
    rintro n ⟨hn1, m, rfl⟩
    have hmN : N ≤ m := by
      by_contra hlt
      push_neg at hlt
      exact absurd (hemono (i + 1) hlt) (not_lt.mpr hn1)
    exact hN m hmN
  haveI := hFne
  exact ⟨q, (htend.mapClusterPt).mono hFatTop⟩

/-- **Corollary 4(a)** (`suffconds`) of the note: a sequentially compact space has bounded
cliques. -/
theorem boundedCliqueProperty_of_seqCompactSpace [SeqCompactSpace X] :
    BoundedCliqueProperty X :=
  boundedCliqueProperty_of_seqClusterCompact_pi seqClusterCompact_pi_of_seqCompactSpace

/-- **$\omega$-boundedness** (Corollary 4(b) of the note): every countable subset of `X` has
compact closure. -/
def OmegaBounded (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ D : Set X, D.Countable → IsCompact (closure D)

/-- Corollary 4(b) of the note, key step: if `X` is $\omega$-bounded then every sequence in
`X^\omega` has a cluster point, since such a sequence lies in the compact product of the
closures of its coordinate projections. -/
theorem seqClusterCompact_pi_of_omegaBounded (hX : OmegaBounded X) :
    SeqClusterCompact (ℕ → X) := by
  intro Z
  set K : ℕ → Set X := fun i => closure (Set.range fun n => Z n i) with hK
  have hKcompact : ∀ i, IsCompact (K i) := fun i =>
    hX _ (Set.countable_range fun n => Z n i)
  have hprod : IsCompact {f : ℕ → X | ∀ i, f i ∈ K i} := isCompact_pi_infinite hKcompact
  have hmem : ∀ n, Z n ∈ {f : ℕ → X | ∀ i, f i ∈ K i} := fun n i =>
    subset_closure ⟨n, rfl⟩
  obtain ⟨a, -, ha⟩ := hprod (f := Filter.map Z Filter.atTop)
    (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' hmem)))
  exact ⟨a, ha⟩

/-- **Corollary 4(b)** (`suffconds`) of the note: an $\omega$-bounded space has bounded
cliques. -/
theorem boundedCliqueProperty_of_omegaBounded (hX : OmegaBounded X) :
    BoundedCliqueProperty X :=
  boundedCliqueProperty_of_seqClusterCompact_pi (seqClusterCompact_pi_of_omegaBounded hX)

/-- **$\mathfrak u$-compactness** (Corollary 4(c) of the note): for an ultrafilter `u` on
`ω = ℕ`, every sequence in `X` has a `u`-limit. -/
def UltrafilterCompact (u : Ultrafilter ℕ) (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ z : ℕ → X, ∃ x : X, Filter.Tendsto z (u : Filter ℕ) (𝓝 x)

/-- Corollary 4(c) of the note: `u`-compactness is (countably) productive. -/
theorem ultrafilterCompact_pi {u : Ultrafilter ℕ} (hX : UltrafilterCompact u X) :
    UltrafilterCompact u (ℕ → X) := by
  intro Z
  choose q hq using fun i => hX (fun n => Z n i)
  exact ⟨q, tendsto_pi_nhds.2 hq⟩

/-- Corollary 4(c) of the note: for a *free* ultrafilter `u` on `ω`, `u`-compactness implies
that every sequence has a cluster point (in particular it implies countable compactness). -/
theorem seqClusterCompact_of_ultrafilterCompact {u : Ultrafilter ℕ}
    (hfree : (u : Filter ℕ) ≤ Filter.cofinite) (hX : UltrafilterCompact u X) :
    SeqClusterCompact X := by
  intro z
  obtain ⟨x, hx⟩ := hX z
  refine ⟨x, MapClusterPt.mono hx.mapClusterPt ?_⟩
  rwa [← Nat.cofinite_eq_atTop]

/-- **Corollary 4(c)** (`suffconds`) of the note: if `X` is $\mathfrak u$-compact for some free
ultrafilter $\mathfrak u$ on $\omega$, then `X` has bounded cliques. -/
theorem boundedCliqueProperty_of_ultrafilterCompact {u : Ultrafilter ℕ}
    (hfree : (u : Filter ℕ) ≤ Filter.cofinite) (hX : UltrafilterCompact u X) :
    BoundedCliqueProperty X :=
  boundedCliqueProperty_of_seqClusterCompact_pi
    (seqClusterCompact_of_ultrafilterCompact hfree (ultrafilterCompact_pi hX))

end CliqueSize
