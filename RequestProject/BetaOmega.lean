import RequestProject.Basic

/-!
# A Note on Compactness and Clique Size — the `βω` construction of Section 4

This file formalizes the combinatorial content of the construction proposed at the end of
Section 4 ("The structure of the problem") of the source note *A Note on Compactness and Clique
Size* (D. V. Feldman and A. Wilce):

> Partition `ω` into sets `A_n` with `|A_n| = n`, and let `R₀` join distinct points of a common
> cell.  Call `S ⊆ ω` a *partial section* if `|S ∩ A_n| ≤ 1` for all `n`.  For a free ultrafilter
> `u`, a direct computation with basic neighborhoods gives
> `(u,u) ∈ closure R₀` (closure in `(βω)²`) iff no member of `u` is a partial section.
> (Note here that if some `B ∈ u` meets every cell at most `k` times, then `B` splits into at most
> `k` partial sections, one of which lies in `u`; so bounded transversals already witness
> membership in the good set.)
> Let `G := { u ∈ ω* : u contains a partial section }`.  Then `G` is open (a union of basic clopen
> sets `Ŝ = {u | S ∈ u}`, `S` a partial section) and dense (every infinite `B ⊆ ω` meets
> infinitely many cells, since cells are finite, and hence contains an infinite partial section),
> while `ω* \ G` is nonempty (complements of finitely many partial sections `S₁, …, S_k` retain at
> least `n - k` points of `A_n` for `n > k`, so these complements have the finite intersection
> property) and closed nowhere dense.

Here `βω` is realized, as usual, as the space `Ultrafilter ℕ` of ultrafilters on `ℕ` with its
Stone topology, `ω` sits inside it via `pure`, and `ω*` is the set of *free* ultrafilters.

The partition is realized concretely: `cell n` is the block of `n + 1` consecutive natural numbers
starting at the `n`-th triangular number, so the cells have all finite sizes, exactly as in the
note (the indexing is shifted by one so that cells are indexed by all of `ℕ`).
-/

namespace CliqueSize

namespace BetaOmega

open Set Filter Topology

/-- The `n`-th triangular number `0 + 1 + ⋯ + n`, used to lay out the cells `A_n` of the partition
of `ω` in Section 4 of the note. -/
def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + (n + 1)

/-- The cell `A_n` of the partition of `ω` from Section 4 of the note, realized as the block of
`n + 1` consecutive natural numbers `[tri n, tri (n+1))`. -/
def cell (n : ℕ) : Finset ℕ := Finset.Ico (tri n) (tri (n + 1))

/-- The triangular numbers laying out the cells `A_n` of Section 4 of the note are strictly
increasing at each step, so the cells are nonempty. -/
theorem tri_lt_tri_succ (n : ℕ) : tri n < tri (n + 1) := by
  simp [tri]

/-- The triangular numbers laying out the cells `A_n` of Section 4 of the note are strictly
monotone. -/
theorem tri_strictMono : StrictMono tri :=
  strictMono_nat_of_lt_succ tri_lt_tri_succ

/-- Auxiliary bound on the layout of the cells `A_n` of Section 4 of the note: the `n`-th
triangular number is at least `n`. -/
theorem le_tri (n : ℕ) : n ≤ tri n := by
  induction n with
  | zero => simp [tri]
  | succ n ih => simp [tri]

/-- Each cell `A_n` of the partition of Section 4 of the note has exactly `n + 1` elements; in
particular the cells realize all finite sizes. -/
theorem card_cell (n : ℕ) : (cell n).card = n + 1 := by
  simp [cell, tri]

/-- Membership in the cell `A_n` of the partition of `ω` from Section 4 of the note. -/
theorem mem_cell_iff {m n : ℕ} : m ∈ cell n ↔ tri n ≤ m ∧ m < tri (n + 1) := by
  simp [cell]

/-- The index of the cell containing `m`. -/
def cellIndex (m : ℕ) : ℕ := Nat.findGreatest (fun n => tri n ≤ m) m

/-- The index of the cell of Section 4 of the note containing `m` satisfies the lower bound
defining it. -/
theorem tri_cellIndex_le (m : ℕ) : tri (cellIndex m) ≤ m :=
  Nat.findGreatest_spec (P := fun n => tri n ≤ m) (Nat.zero_le m) (by simp [tri])

/-- The index of the cell of Section 4 of the note containing `m` satisfies the upper bound
defining it. -/
theorem lt_tri_cellIndex_succ (m : ℕ) : m < tri (cellIndex m + 1) := by
  by_contra h
  push_neg at h
  have h1 : cellIndex m + 1 ≤ m := le_trans (le_tri _) h
  have h2 : cellIndex m + 1 ≤ cellIndex m :=
    Nat.le_findGreatest (P := fun n => tri n ≤ m) h1 h
  omega

/-- The cells of Section 4 of the note partition `ω`: `m` lies in `A_n` exactly when `n` is the
cell index of `m`. -/
theorem cellIndex_eq_iff {m n : ℕ} : cellIndex m = n ↔ m ∈ cell n := by
  constructor
  · rintro rfl
    exact mem_cell_iff.2 ⟨tri_cellIndex_le m, lt_tri_cellIndex_succ m⟩
  · intro hm
    rw [mem_cell_iff] at hm
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : tri (cellIndex m + 1) ≤ tri n := tri_strictMono.monotone (Nat.succ_le_of_lt h)
      have := lt_tri_cellIndex_succ m
      omega
    · have h1 : tri (n + 1) ≤ tri (cellIndex m) := tri_strictMono.monotone (Nat.succ_le_of_lt h)
      have := tri_cellIndex_le m
      omega

/-- Every natural number lies in its own cell of the partition of `ω` of Section 4 of the note. -/
theorem mem_cell_cellIndex (m : ℕ) : m ∈ cell (cellIndex m) := cellIndex_eq_iff.1 rfl

/-- The cells of the partition of `ω` of Section 4 of the note are pairwise disjoint: a number
lying in `A_n` has cell index `n`. -/
theorem cellIndex_of_mem_cell {m n : ℕ} (h : m ∈ cell n) : cellIndex m = n := cellIndex_eq_iff.2 h

/-- The cells `A_n` of Section 4 of the note march off to infinity: every element of `A_n` is at
least `n`. -/
theorem le_of_mem_cell {m n : ℕ} (h : m ∈ cell n) : n ≤ m :=
  le_trans (le_tri n) (mem_cell_iff.1 h).1

/-- A *partial section* (Section 4 of the note): a set `S ⊆ ω` with `|S ∩ A_n| ≤ 1` for every
cell `A_n` of the partition. -/
def IsPartialSection (S : Set ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, cellIndex x = cellIndex y → x = y

/-- The definition of a partial section, in the note's original phrasing: `S` meets each cell in
at most one point. -/
theorem isPartialSection_iff {S : Set ℕ} :
    IsPartialSection S ↔ ∀ n : ℕ, ((cell n : Set ℕ) ∩ S).Subsingleton := by
  constructor
  · intro hS n x hx y hy
    exact hS x hx.2 y hy.2
      (by rw [cellIndex_of_mem_cell hx.1, cellIndex_of_mem_cell hy.1])
  · intro hS x hx y hy hxy
    exact hS (cellIndex x) ⟨mem_cell_cellIndex x, hx⟩ ⟨hxy ▸ mem_cell_cellIndex y, hy⟩

/-- The relation `R₀` of Section 4 of the note: distinct points of a common cell are related. -/
def R0 (x y : ℕ) : Prop := x ≠ y ∧ cellIndex x = cellIndex y

/-- `R₀` is a closed orthogonality relation on the discrete space `ω`, in the sense of Section 1
of the note. -/
theorem isOrthogonality_R0 : IsOrthogonality R0 :=
  ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩, fun _ h => h.1 rfl, isClosed_discrete _⟩

/-- Section 4 of the note: each cell `A_n` is an `R₀`-clique, of size `n + 1`. -/
theorem isClique_cell (n : ℕ) : IsClique R0 (cell n : Set ℕ) := by
  intro x hx y hy hxy
  exact ⟨hxy, by rw [cellIndex_of_mem_cell hx, cellIndex_of_mem_cell hy]⟩

/-- Section 4 of the note: the cells give `R₀`-cliques of every finite size, so `R₀` does not have
bounded cliques. -/
theorem not_hasBoundedCliques_R0 : ¬ HasBoundedCliques R0 := by
  rintro ⟨n, hn⟩
  have h := hn _ (isClique_cell (n + 1))
  rw [Set.encard_coe_eq_coe_finsetCard, card_cell] at h
  exact absurd h (by exact_mod_cast by omega)

/-- Section 4 of the note: every `R₀`-clique lies inside a single (finite) cell, so `R₀` has
finite cliques. -/
theorem hasFiniteCliques_R0 : HasFiniteCliques R0 := by
  intro A hA
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact Set.finite_empty
  · refine Set.Finite.subset (cell (cellIndex a)).finite_toSet fun x hx => ?_
    rcases eq_or_ne x a with rfl | hne
    · exact mem_cell_cellIndex x
    · exact cellIndex_eq_iff.1 (hA hx ha hne).2

/-- The cells `A_n` of Section 4 of the note are finite, hence so are their intersections with
arbitrary subsets of `ω`. -/
theorem finite_cellSet_inter (n : ℕ) (B : Set ℕ) : ((cell n : Set ℕ) ∩ B).Finite :=
  ((cell n).finite_toSet).subset Set.inter_subset_left

/-- Section 4 of the note (density of `G`): every infinite `B ⊆ ω` contains an infinite partial
section, because the cells are finite and so `B` meets infinitely many of them.  The partial
section produced is canonical: it consists of the cellwise minima of `B`. -/
theorem exists_infinite_isPartialSection_subset {B : Set ℕ} (hB : B.Infinite) :
    ∃ S ⊆ B, S.Infinite ∧ IsPartialSection S := by
  classical
  refine ⟨{b ∈ B | ∀ c ∈ B, cellIndex c = cellIndex b → b ≤ c}, fun b hb => hb.1, ?_, ?_⟩
  · refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨b, hbB, hb⟩ := hB.exists_gt (tri (N + 1))
    have hNn : N + 1 ≤ cellIndex b := by
      by_contra hcon
      push_neg at hcon
      have h1 : tri (cellIndex b + 1) ≤ tri (N + 1) := tri_strictMono.monotone (by omega)
      have h2 := lt_tri_cellIndex_succ b
      omega
    have hne : {c | c ∈ B ∧ cellIndex c = cellIndex b}.Nonempty := ⟨b, hbB, rfl⟩
    set m := sInf {c | c ∈ B ∧ cellIndex c = cellIndex b} with hm
    obtain ⟨hmB, hmn⟩ := Nat.sInf_mem hne
    refine ⟨m, ⟨hmB, fun c hcB hc => ?_⟩, ?_⟩
    · exact Nat.sInf_le ⟨hcB, by rw [hc, hmn]⟩
    · have : cellIndex b ≤ m := le_of_mem_cell (cellIndex_eq_iff.1 hmn)
      omega
  · intro x hx y hy hxy
    exact le_antisymm (hx.2 y hy.1 hxy.symm) (hy.2 x hx.1 hxy)

/-- Section 4 of the note, the parenthetical remark: if some `B ∈ u` meets every cell at most `k`
times, then `B` splits into at most `k` partial sections, one of which lies in `u`; so bounded
transversals already witness membership in the good set `G`.  The splitting used here is the
canonical, choice-free one by cellwise rank. -/
theorem exists_isPartialSection_mem_of_ncard_le {u : Ultrafilter ℕ} {B : Set ℕ} (hB : B ∈ u)
    {k : ℕ} (hk : ∀ n : ℕ, ((cell n : Set ℕ) ∩ B).ncard ≤ k) :
    ∃ S ∈ u, S ⊆ B ∧ IsPartialSection S := by
  classical
  set rank : ℕ → ℕ := fun b => {c | c ∈ B ∧ cellIndex c = cellIndex b ∧ c < b}.ncard with hrank
  have hsub : ∀ b, {c | c ∈ B ∧ cellIndex c = cellIndex b ∧ c < b} ⊆
      (cell (cellIndex b) : Set ℕ) ∩ B := by
    intro b c hc
    exact ⟨cellIndex_eq_iff.1 hc.2.1, hc.1⟩
  have hrank_lt : ∀ b ∈ B, rank b < k := by
    intro b hb
    have hssub : {c | c ∈ B ∧ cellIndex c = cellIndex b ∧ c < b} ⊂
        (cell (cellIndex b) : Set ℕ) ∩ B := by
      refine ⟨hsub b, fun hcon => ?_⟩
      have hbmem : b ∈ (cell (cellIndex b) : Set ℕ) ∩ B := ⟨mem_cell_cellIndex b, hb⟩
      exact absurd (hcon hbmem).2.2 (lt_irrefl b)
    exact lt_of_lt_of_le (Set.ncard_lt_ncard hssub (finite_cellSet_inter _ _))
      (hk (cellIndex b))
  have hcover : B = ⋃ j ∈ Set.Iio k, {b | b ∈ B ∧ rank b = j} := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun hb => ⟨rank b, hrank_lt b hb, hb, rfl⟩, fun ⟨_, _, hb, _⟩ => hb⟩
  rw [hcover] at hB
  obtain ⟨j, -, hj⟩ := (Ultrafilter.finite_biUnion_mem_iff (Set.finite_Iio k)).1 hB
  refine ⟨{b | b ∈ B ∧ rank b = j}, hj, fun b hb => hb.1, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  -- the element of smaller value has strictly smaller rank
  have key : ∀ a b : ℕ, a ∈ B → b ∈ B → cellIndex a = cellIndex b → a < b → rank a < rank b := by
    intro a b haB hbB hab hlt
    have hssub : {c | c ∈ B ∧ cellIndex c = cellIndex a ∧ c < a} ⊂
        {c | c ∈ B ∧ cellIndex c = cellIndex b ∧ c < b} := by
      refine ⟨fun c hc => ⟨hc.1, by rw [hc.2.1, hab], lt_trans hc.2.2 hlt⟩, fun hcon => ?_⟩
      have : a ∈ {c | c ∈ B ∧ cellIndex c = cellIndex b ∧ c < b} := ⟨haB, hab, hlt⟩
      exact absurd (hcon this).2.2 (lt_irrefl a)
    exact Set.ncard_lt_ncard hssub
      (((cell (cellIndex b)).finite_toSet).subset fun c hc => cellIndex_eq_iff.1 hc.2.1)
  rcases lt_or_gt_of_ne hne with h | h
  · have := key x y hx.1 hy.1 hxy h
    rw [hx.2, hy.2] at this
    exact absurd this (lt_irrefl j)
  · have := key y x hy.1 hx.1 hxy.symm h
    rw [hx.2, hy.2] at this
    exact absurd this (lt_irrefl j)

/-- Section 4 of the note: finitely many partial sections `S₁, …, S_k` leave at least `n - k`
points of the cell `A_n` untouched; in particular, for `n ≥ k` some point of `A_n` avoids all of
them. -/
theorem exists_mem_cell_notMem (T : Finset (Set ℕ)) (hT : ∀ S ∈ T, IsPartialSection S) {n : ℕ}
    (hn : T.card ≤ n) : ∃ m ∈ cell n, ∀ S ∈ T, m ∉ S := by
  classical
  have hbad : ((cell n).filter (fun m => ∃ S ∈ T, m ∈ S)).card ≤ T.card := by
    have hsub : (cell n).filter (fun m => ∃ S ∈ T, m ∈ S) ⊆
        T.biUnion (fun S => (cell n).filter (fun m => m ∈ S)) := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨S, hST, hmS⟩ := hm.2
      exact Finset.mem_biUnion.2 ⟨S, hST, Finset.mem_filter.2 ⟨hm.1, hmS⟩⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_biUnion_le) ?_)
    have hone : ∀ S ∈ T, ((cell n).filter (fun m => m ∈ S)).card ≤ 1 := ?_
    · calc ∑ S ∈ T, ((cell n).filter (fun m => m ∈ S)).card ≤ ∑ _S ∈ T, 1 :=
            Finset.sum_le_sum hone
        _ = T.card := by simp
    intro S hS
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    exact hT S hS a ha.2 b hb.2
      (by rw [cellIndex_of_mem_cell ha.1, cellIndex_of_mem_cell hb.1])
  have hlt : ((cell n).filter (fun m => ∃ S ∈ T, m ∈ S)).card < (cell n).card := by
    rw [card_cell]
    omega
  obtain ⟨m, hm, hm'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨m, hm, fun S hS hmS => hm' (Finset.mem_filter.2 ⟨hm, ⟨S, hS, hmS⟩⟩)⟩

/-- Section 4 of the note: the complements of finitely many partial sections have infinite
intersection; hence the family of complements of partial sections has the finite intersection
property. -/
theorem infinite_notMem_of_finset (T : Finset (Set ℕ)) (hT : ∀ S ∈ T, IsPartialSection S) :
    {m : ℕ | ∀ S ∈ T, m ∉ S}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨m, hm, hm'⟩ := exists_mem_cell_notMem T hT (le_max_left T.card (N + 1))
  exact ⟨m, hm', lt_of_lt_of_le (by omega)
    (le_of_mem_cell hm |>.trans' (le_max_right T.card (N + 1)))⟩

/-- Section 4 of the note: `ω* \ G` is nonempty — there is a free ultrafilter on `ω` no member of
which is a partial section. -/
theorem exists_free_ultrafilter_no_isPartialSection :
    ∃ u : Ultrafilter ℕ, ((u : Filter ℕ) ≤ Filter.cofinite) ∧ ∀ S ∈ u, ¬ IsPartialSection S := by
  classical
  set G : Set (Set ℕ) := {A : Set ℕ | ∃ S, IsPartialSection S ∧ A = Sᶜ} with hG
  have hNeBot : (Filter.cofinite ⊓ Filter.generate G).NeBot := by
    rw [← Filter.forall_mem_nonempty_iff_neBot]
    intro s hs
    rw [Filter.mem_inf_iff] at hs
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := hs
    rw [Filter.mem_generate_iff] at ht₂
    obtain ⟨t, htG, htfin, htsub⟩ := ht₂
    have hchoice : ∀ a ∈ t, ∃ S, IsPartialSection S ∧ a = Sᶜ := fun a ha => htG ha
    choose! f hf1 hf2 using hchoice
    set T : Finset (Set ℕ) := htfin.toFinset.image f with hTdef
    have hTsec : ∀ S ∈ T, IsPartialSection S := by
      intro S hS
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hS
      exact hf1 a (htfin.mem_toFinset.1 ha)
    have hsub : {m : ℕ | ∀ S ∈ T, m ∉ S} ⊆ ⋂₀ t := by
      intro m hm a ha
      have : m ∉ f a := hm (f a) (Finset.mem_image.2 ⟨a, htfin.mem_toFinset.2 ha, rfl⟩)
      rw [hf2 a ha]
      exact this
    have hinf : ({m : ℕ | ∀ S ∈ T, m ∉ S} \ t₁ᶜ).Infinite :=
      (infinite_notMem_of_finset T hTsec).diff (Filter.mem_cofinite.1 ht₁)
    obtain ⟨m, hm⟩ := hinf.nonempty
    exact ⟨m, not_notMem.1 hm.2, htsub (hsub hm.1)⟩
  obtain ⟨u, hu⟩ := Filter.exists_ultrafilter_le (Filter.cofinite ⊓ Filter.generate G)
  refine ⟨u, le_trans hu inf_le_left, fun S hS hSsec => ?_⟩
  have hcompl : Sᶜ ∈ u :=
    hu (Filter.mem_inf_of_right (Filter.mem_generate_of_mem (show Sᶜ ∈ G from ⟨S, hSsec, rfl⟩)))
  exact (u.compl_notMem_iff.2 hS) hcompl

/-- Section 4 of the note: the set `G` of ultrafilters containing a partial section is open in
`βω`, being a union of the basic clopen sets `Ŝ` for `S` a partial section. -/
theorem isOpen_goodSet : IsOpen {u : Ultrafilter ℕ | ∃ S ∈ u, IsPartialSection S} := by
  have hEq : {u : Ultrafilter ℕ | ∃ S ∈ u, IsPartialSection S}
      = ⋃ S ∈ {S : Set ℕ | IsPartialSection S}, {u : Ultrafilter ℕ | S ∈ u} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨S, hSu, hS⟩ => ⟨S, hS, hSu⟩, fun ⟨S, hS, hSu⟩ => ⟨S, hSu, hS⟩⟩
  rw [hEq]
  exact isOpen_biUnion fun S _ => ultrafilter_isOpen_basic S

/-- Section 4 of the note: `G` is dense in `ω*` — every basic clopen set determined by an infinite
set `B ⊆ ω` contains a free ultrafilter that contains a partial section (indeed an infinite
partial section contained in `B`). -/
theorem exists_free_ultrafilter_mem_goodSet {B : Set ℕ} (hB : B.Infinite) :
    ∃ u : Ultrafilter ℕ, ((u : Filter ℕ) ≤ Filter.cofinite) ∧ B ∈ u ∧ ∃ S ∈ u, IsPartialSection S := by
  obtain ⟨S, hSB, hSinf, hSsec⟩ := exists_infinite_isPartialSection_subset hB
  have : (Filter.cofinite ⊓ Filter.principal S).NeBot :=
    Filter.cofinite_inf_principal_neBot_iff.2 hSinf
  obtain ⟨u, hu⟩ := Filter.exists_ultrafilter_le (Filter.cofinite ⊓ Filter.principal S)
  have hSu : S ∈ u := hu (Filter.mem_inf_of_right (Filter.mem_principal_self S))
  exact ⟨u, le_trans hu inf_le_left, Filter.mem_of_superset hSu hSB, S, hSu, hSsec⟩

/-- The image of the relation `R₀` inside `(βω)²`, i.e. `R₀` viewed as a set of pairs of principal
ultrafilters (Section 4 of the note). -/
def betaR0 : Set (Ultrafilter ℕ × Ultrafilter ℕ) :=
  (fun p : ℕ × ℕ => ((pure p.1 : Ultrafilter ℕ), (pure p.2 : Ultrafilter ℕ))) '' {p | R0 p.1 p.2}

/-- **Section 4 of the note**, the "direct computation with basic neighborhoods": for an
ultrafilter `u` on `ω`, the pair `(u, u)` lies in the closure of `R₀` in `(βω)²` if and only if no
member of `u` is a partial section. -/
theorem mem_closure_betaR0_iff (u : Ultrafilter ℕ) :
    ((u, u) ∈ closure betaR0) ↔ ∀ S ∈ u, ¬ IsPartialSection S := by
  have hbasis := (ultrafilterBasis_is_basis (α := ℕ)).prod (ultrafilterBasis_is_basis (α := ℕ))
  rw [hbasis.mem_closure_iff]
  constructor
  · intro h S hSu hSsec
    obtain ⟨p, hp, hpR⟩ := h ({v : Ultrafilter ℕ | S ∈ v} ×ˢ {v : Ultrafilter ℕ | S ∈ v})
      (Set.mem_image2_of_mem ⟨S, rfl⟩ ⟨S, rfl⟩) ⟨hSu, hSu⟩
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hpR
    have hx : x ∈ S := Ultrafilter.mem_pure.1 hp.1
    have hy : y ∈ S := Ultrafilter.mem_pure.1 hp.2
    exact hxy.1 (hSsec x hx y hy hxy.2)
  · rintro h o ⟨-, ⟨A, rfl⟩, -, ⟨B, rfl⟩, rfl⟩ ⟨hA, hB⟩
    have hAB : A ∩ B ∈ u := Filter.inter_mem hA hB
    have hnot := h (A ∩ B) hAB
    rw [IsPartialSection] at hnot
    push_neg at hnot
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := hnot
    exact ⟨(pure x, pure y), ⟨Ultrafilter.mem_pure.2 hx.1, Ultrafilter.mem_pure.2 hy.2⟩,
      ⟨(x, y), ⟨hne, hxy⟩, rfl⟩⟩

end BetaOmega

end CliqueSize
