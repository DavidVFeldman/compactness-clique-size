import RequestProject.Basic

/-!
# A Note on Compactness and Clique Size — the uniform and metric folklore of Section 1

This file formalizes the discussion following the proof of Lemma 1 in the source note
*A Note on Compactness and Clique Size* (D. V. Feldman and A. Wilce), namely the two "folkloric"
arguments that the note describes as easy but hard to find in the literature:

> If `R` is a nonempty closed orthogonality on a compact metric space `X`, then since `R` is
> itself compact, the metric takes a minimum value `ε > 0` on `R` (non-zero since `d` is zero
> only on the diagonal, which `R` misses).  Every `R`-clique is thus `ε`-separated, and so has
> size at most the `ε/2` packing number of `X`.

> For compact Hausdorff spaces, Lemma 1 follows from the fact that the complements of
> orthogonalities are precisely the open symmetric entourages for the unique compatible
> uniformity.  Any clique `A` for the complement of such an entourage `E` is `E`-discrete
> (`A × A ∩ E ⊆ Δ`), and `E`-discrete sets, for a fixed entourage `E`, in a totally bounded
> uniform space are boundedly finite.

together with the footnote proof of the last assertion:

> Suppose `A` is `E`-discrete.  Choose a smaller symmetric entourage `D` with `D ∘ D ⊆ E`: since
> `X` is totally bounded, there is some finite set `F ⊆ X` with `X = D[F]`.  If `x, y ∈ A ∩ D[a]`,
> then `(a,x), (a,y) ∈ D`; as `D = D⁻¹`, we also have `(x,a) ∈ D`, whence `(x,y) ∈ D ∘ D ⊆ E`.
> But then, as `A` is `E`-discrete, `x = y`.  Thus each set `D[a]` contains at most one point of
> `A`, whence `|A| ≤ |F|`.
-/

namespace CliqueSize

open Set Filter Topology Uniformity

variable {X : Type*}

/-- A set `A` is *`E`-discrete* for an entourage `E` (Section 1 of the note):
`A × A ∩ E ⊆ Δ`. -/
def IsEDiscrete (E : SetRel X X) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, (x, y) ∈ E → x = y

/-- The footnote of Section 1 of the note: for a fixed entourage `E` of a totally bounded uniform
space, the `E`-discrete sets are boundedly finite. -/
theorem exists_encard_bound_of_isEDiscrete [UniformSpace X]
    (hX : TotallyBounded (Set.univ : Set X)) {E : SetRel X X} (hE : E ∈ 𝓤 X) :
    ∃ n : ℕ, ∀ A : Set X, IsEDiscrete E A → A.encard ≤ n := by
  obtain ⟨D, hD, hDsymm, hDcomp⟩ := comp_symm_of_uniformity hE
  obtain ⟨F, -, hFfin, hFcover⟩ := totallyBounded_iff_subset.mp hX D hD
  have hpick : ∀ x : X, ∃ a ∈ F, (x, a) ∈ D := by
    intro x
    have hx : x ∈ ⋃ y ∈ F, {z | (z, y) ∈ D} := hFcover (mem_univ x)
    simpa using hx
  choose f hfF hfD using hpick
  refine ⟨hFfin.toFinset.card, fun A hA => ?_⟩
  have hle : A.encard ≤ F.encard :=
    encard_le_encard_of_injOn (fun x _ => hfF x) (by
      intro x hx y hy hxy
      have h1 : (x, f x) ∈ D := hfD x
      have h2 : (y, f y) ∈ D := hfD y
      have h2' : (f x, y) ∈ D := by
        rw [hxy]; exact hDsymm h2
      have : (x, y) ∈ SetRel.comp D D := SetRel.mem_comp.2 ⟨f x, h1, h2'⟩
      exact hA x hx y hy (hDcomp this))
  refine hle.trans ?_
  rw [hFfin.encard_eq_coe_toFinset_card]

/-- Section 1 of the note, compact metric case: a nonempty closed orthogonality relation `R` on a
compact metric space `X` attains a strictly positive minimum distance `ε`; hence every `R`-clique
is `ε`-separated. -/
theorem exists_pos_le_dist_of_isOrthogonality [MetricSpace X] [CompactSpace X]
    {R : X → X → Prop} (hR : IsOrthogonality R) :
    ∃ ε > 0, ∀ x y, R x y → ε ≤ dist x y := by
  set S : Set (X × X) := {p : X × X | R p.1 p.2} with hS
  rcases S.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, fun x y hxy => ?_⟩
    exact absurd (show (x, y) ∈ S from hxy) (by rw [hempty]; exact notMem_empty _)
  · have hcompact : IsCompact S := hR.isClosed.isCompact
    obtain ⟨p, hpS, hpmin⟩ :=
      hcompact.exists_isMinOn hne (Continuous.continuousOn
        (by fun_prop : Continuous fun q : X × X => dist q.1 q.2))
    have hppos : 0 < dist p.1 p.2 := by
      have hne' : p.1 ≠ p.2 := by
        rintro h
        exact hR.irrefl p.1 (by simpa [hS, h] using hpS)
      exact dist_pos.2 hne'
    exact ⟨dist p.1 p.2, hppos, fun x y hxy => hpmin (show (x, y) ∈ S from hxy)⟩

/-- Section 1 of the note: in a compact Hausdorff space, with its unique compatible uniformity,
the complement of a closed orthogonality relation is an entourage (indeed an open symmetric
one). -/
theorem compl_mem_uniformity_of_isOrthogonality [UniformSpace X] [CompactSpace X] [T2Space X]
    {R : X → X → Prop} (hR : IsOrthogonality R) :
    {p : X × X | ¬ R p.1 p.2} ∈ 𝓤 X := by
  have hopen : IsOpen {p : X × X | ¬ R p.1 p.2} := by
    simpa [compl_setOf] using hR.isClosed.isOpen_compl
  rw [compactSpace_uniformity]
  refine mem_iSup.2 fun x => ?_
  exact hopen.mem_nhds (hR.irrefl x)

/-- Section 1 of the note: an `R`-clique is `E`-discrete for the entourage `E` complementary to
the closed orthogonality relation `R`. -/
theorem isEDiscrete_compl_of_isClique {R : X → X → Prop} {A : Set X} (hA : IsClique R A) :
    IsEDiscrete {p : X × X | ¬ R p.1 p.2} A := by
  intro x hx y hy hxy
  by_contra hne
  exact hxy (hA hx hy hne)

/-- Section 1 of the note: the uniform-space proof of Lemma 1 in the compact Hausdorff case —
cliques of a closed orthogonality relation are `E`-discrete for the complementary entourage `E`,
and `E`-discrete sets in a totally bounded uniform space are boundedly finite. -/
theorem hasBoundedCliques_of_compact_uniform [UniformSpace X] [CompactSpace X] [T2Space X]
    {R : X → X → Prop} (hR : IsOrthogonality R) : HasBoundedCliques R := by
  obtain ⟨n, hn⟩ := exists_encard_bound_of_isEDiscrete
    (isCompact_univ.totallyBounded) (compl_mem_uniformity_of_isOrthogonality hR)
  exact ⟨n, fun A hA => hn A (isEDiscrete_compl_of_isClique hA)⟩

end CliqueSize
