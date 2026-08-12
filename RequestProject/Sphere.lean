import RequestProject.Chromatic

/-!
# A Note on Compactness and Clique Size — the sphere example

This file formalizes the assertion about spheres made in Section 5 of the source note
*A Note on Compactness and Clique Size* (D. V. Feldman and A. Wilce):

> For `X = S^{n-1} ⊆ ℝ^n` with literal orthogonality, cliques are orthonormal systems, so the
> clique number is exactly `n`.

The same relation is the "motivating example" of Section 1 of the note (`X` the unit sphere of
`ℝ^n` and `R` literal orthogonality).

It also formalizes the ingredients of Section 5 that are self-contained: the bound
`n ≤ χ_op(S^{n-1}, ⊥)` coming from the clique number, and the fact that the open octants ("the
eight open octants are orthogonality-free and cover `S² \ C`, where `C` is the union of the three
coordinate great circles") are open, orthogonality-free, and cover the points of the sphere all
of whose coordinates are nonzero.

The full chromatic estimate `4 = χ(S², ⊥) ≤ χ_op(S², ⊥) ≤ 24` of Section 5, and Question 3 of
the note (the value of `χ_op(S^{n-1}, ⊥)`), are *not* formalized here: the note leaves the latter
open, the lower bound `4` rests on results from the literature (Godsil–Zaks) that lie well
outside the scope of this formalization, and the upper bound `24` uses a genericity argument for
rotations of the coordinate circles.
-/

namespace CliqueSize

open Set Filter Topology

/-- The unit sphere `S^{n-1} ⊆ ℝ^n` of the motivating example of Section 1 (and of Section 5) of
the note. -/
abbrev EuclideanSphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- **Literal orthogonality** on the unit sphere `S^{n-1} ⊆ ℝ^n`: the motivating example of the
note (Section 1), and the relation discussed for `S²` in Section 5. -/
def sphereOrth (n : ℕ) : EuclideanSphere n → EuclideanSphere n → Prop :=
  fun x y => inner ℝ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n)) = 0

/-- Points of the unit sphere have norm one. -/
theorem norm_eq_one_of_mem_euclideanSphere {n : ℕ} (x : EuclideanSphere n) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.2

/-- Literal orthogonality on the unit sphere `S^{n-1}` is a closed orthogonality relation in the
sense of Section 1 of the note. -/
theorem isOrthogonality_sphereOrth (n : ℕ) : IsOrthogonality (sphereOrth n) := by
  refine ⟨fun x y h => ?_, fun x h => ?_, ?_⟩
  · simpa [sphereOrth, real_inner_comm] using h
  · rw [sphereOrth, real_inner_self_eq_norm_sq, norm_eq_one_of_mem_euclideanSphere x] at h
    norm_num at h
  · have hcont : Continuous fun p : EuclideanSphere n × EuclideanSphere n =>
        inner ℝ (p.1 : EuclideanSpace ℝ (Fin n)) (p.2 : EuclideanSpace ℝ (Fin n)) :=
      continuous_inner.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
    exact isClosed_eq hcont continuous_const

/-- The note's observation that "cliques are orthonormal systems": a clique of literal
orthogonality on `S^{n-1}` is an orthonormal family in `ℝ^n` (Section 5 of the note). -/
theorem orthonormal_of_isClique_sphereOrth {n : ℕ} {A : Set (EuclideanSphere n)}
    (hA : IsClique (sphereOrth n) A) :
    Orthonormal ℝ (fun x : A => ((x : EuclideanSphere n) : EuclideanSpace ℝ (Fin n))) := by
  constructor
  · intro i
    exact norm_eq_one_of_mem_euclideanSphere _
  · intro i j hij
    exact hA i.2 j.2 (fun h => hij (Subtype.ext h))

/-- **Section 5 of the note**, upper bound: every clique of literal orthogonality on `S^{n-1}`
has at most `n` elements, since cliques are orthonormal systems in `ℝ^n`. -/
theorem encard_le_of_isClique_sphereOrth {n : ℕ} {A : Set (EuclideanSphere n)}
    (hA : IsClique (sphereOrth n) A) : A.encard ≤ n := by
  set B : Set (EuclideanSpace ℝ (Fin n)) := (fun x : EuclideanSphere n => (x : _)) '' A with hB
  have hinj : Set.InjOn (fun x : EuclideanSphere n => (x : EuclideanSpace ℝ (Fin n))) A :=
    fun x _ y _ h => Subtype.ext h
  have hon : Orthonormal ℝ (fun x : B => (x : EuclideanSpace ℝ (Fin n))) := by
    rw [orthonormal_subtype_iff_ite] at *
    rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩
    by_cases h : (p : EuclideanSpace ℝ (Fin n)) = (q : EuclideanSpace ℝ (Fin n))
    · have : p = q := Subtype.ext h
      subst this
      simp [norm_eq_one_of_mem_euclideanSphere p]
    · have hne : p ≠ q := fun hpq => h (by rw [hpq])
      simpa [h] using hA hp hq hne
  have hli := hon.linearIndependent
  have hfin : B.Finite :=
    Set.finite_coe_iff.mp (Cardinal.lt_aleph0_iff_finite.mp hli.lt_aleph0_of_finite)
  have : Fintype B := hfin.fintype
  have hcard := hli.fintype_card_le_finrank
  rw [finrank_euclideanSpace_fin] at hcard
  have hBcard : B.encard ≤ (n : ℕ∞) := by
    rw [Set.encard_eq_coe_toFinset_card, Set.toFinset_card]
    exact_mod_cast hcard
  rwa [hB, hinj.encard_image] at hBcard

/-- **Section 5 of the note**, sharpness: literal orthogonality on `S^{n-1}` has a clique with
exactly `n` elements, namely the standard orthonormal basis of `ℝ^n`. Together with
`encard_le_of_isClique_sphereOrth` this says that the clique number of `(S^{n-1}, ⊥)` is
exactly `n`. -/
theorem exists_isClique_sphereOrth_encard_eq (n : ℕ) :
    ∃ A : Set (EuclideanSphere n), IsClique (sphereOrth n) A ∧ A.encard = n := by
  have hmem : ∀ i : Fin n, EuclideanSpace.single i (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro i
    simp [EuclideanSpace.norm_single]
  refine ⟨Set.range (fun i : Fin n => (⟨EuclideanSpace.single i (1 : ℝ), hmem i⟩ :
    EuclideanSphere n)), ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hne : i ≠ j := by
      rintro rfl; exact hij rfl
    simp [sphereOrth, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, hne]
  · have hinj : Function.Injective
        (fun i : Fin n => (⟨EuclideanSpace.single i (1 : ℝ), hmem i⟩ : EuclideanSphere n)) := by
      intro i j h
      have h' : EuclideanSpace.single i (1 : ℝ) = EuclideanSpace.single j (1 : ℝ) :=
        congrArg Subtype.val h
      by_contra hne
      have hval : EuclideanSpace.single i (1 : ℝ) i = EuclideanSpace.single j (1 : ℝ) i := by
        rw [h']
      simp [EuclideanSpace.single_apply, hne] at hval
    rw [← Set.image_univ, Set.InjOn.encard_image hinj.injOn]
    simp

/-- **Section 5 of the note**: the clique number of the unit sphere `S^{n-1} ⊆ ℝ^n` under literal
orthogonality is exactly `n`: every clique has at most `n` elements and some clique has exactly
`n` elements. -/
theorem sphere_clique_number (n : ℕ) :
    (∀ A : Set (EuclideanSphere n), IsClique (sphereOrth n) A → A.encard ≤ n) ∧
      ∃ A : Set (EuclideanSphere n), IsClique (sphereOrth n) A ∧ A.encard = n :=
  ⟨fun _ hA => encard_le_of_isClique_sphereOrth hA, exists_isClique_sphereOrth_encard_eq n⟩

/-- **Section 5 of the note**: since the clique number of `(S^{n-1}, ⊥)` is `n` and every clique is
bounded by the open chromatic number (Remark 1(i)), we get `n ≤ χ_op(S^{n-1}, ⊥)`.  For `n = 3`
this is the (trivial) part `3 ≤ χ_op(S², ⊥)` of the note's estimate
`4 = χ(S², ⊥) ≤ χ_op(S², ⊥) ≤ 24`. -/
theorem le_chiOp_sphereOrth (n : ℕ) : (n : ℕ∞) ≤ chiOp (sphereOrth n) := by
  obtain ⟨A, hA, hcard⟩ := exists_isClique_sphereOrth_encard_eq n
  calc (n : ℕ∞) = A.encard := hcard.symm
    _ ≤ chiOp (sphereOrth n) := encard_le_chiOp hA

/-- The open octant of `S^{n-1}` determined by a vector of signs `s` (Section 5 of the note: "the
eight open octants" of `S²`): the set of points `x` of the sphere with `s i * x i > 0` for every
coordinate `i`. -/
def octant (n : ℕ) (s : Fin n → ℝ) : Set (EuclideanSphere n) :=
  {x | ∀ i, 0 < s i * (x : EuclideanSpace ℝ (Fin n)) i}

/-- Section 5 of the note: the open octants are open. -/
theorem isOpen_octant (n : ℕ) (s : Fin n → ℝ) : IsOpen (octant n s) := by
  have : octant n s = ⋂ i : Fin n,
      {x : EuclideanSphere n | 0 < s i * (x : EuclideanSpace ℝ (Fin n)) i} := by
    ext x
    simp [octant]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  have hcont : Continuous fun x : EuclideanSphere n => s i * (x : EuclideanSpace ℝ (Fin n)) i := by
    fun_prop
  exact isOpen_lt continuous_const hcont

/-- **Section 5 of the note**: the open octants are orthogonality-free (`R`-free in the sense of
Section 2), since the inner product of two points of a common octant is strictly positive. -/
theorem isRFree_octant (n : ℕ) (s : Fin n → ℝ) : IsRFree (sphereOrth n) (octant n s) := by
  intro x hx y hy hxy
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hnorm := norm_eq_one_of_mem_euclideanSphere x
    rw [show (x : EuclideanSpace ℝ (Fin 0)) = 0 from Subsingleton.elim _ _] at hnorm
    simp at hnorm
  · have hpos : ∀ i : Fin n, 0 < (x : EuclideanSpace ℝ (Fin n)) i *
        (y : EuclideanSpace ℝ (Fin n)) i := by
      intro i
      have hxi := hx i
      have hyi := hy i
      have hs : s i ≠ 0 := by
        rintro h
        rw [h] at hxi
        simp at hxi
      have hprod : 0 < (s i * (x : EuclideanSpace ℝ (Fin n)) i) *
          (s i * (y : EuclideanSpace ℝ (Fin n)) i) := mul_pos hxi hyi
      nlinarith [sq_nonneg (s i), (mul_self_pos.2 hs)]
    have hsum : 0 < ∑ i : Fin n, (x : EuclideanSpace ℝ (Fin n)) i *
        (y : EuclideanSpace ℝ (Fin n)) i := by
      refine Finset.sum_pos (fun i _ => hpos i) ?_
      exact Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
    have hinner : inner ℝ (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n)) =
        ∑ i : Fin n, (x : EuclideanSpace ℝ (Fin n)) i * (y : EuclideanSpace ℝ (Fin n)) i := by
      simp [PiLp.inner_apply, mul_comm]
    rw [sphereOrth, hinner] at hxy
    exact absurd hxy (ne_of_gt hsum)

/-- **Section 5 of the note**: the open octants cover the complement of the union of the
coordinate great circles — every point of `S^{n-1}` all of whose coordinates are nonzero lies in
the octant determined by the signs of its coordinates (a vector of signs `±1`). -/
theorem exists_mem_octant {n : ℕ} (x : EuclideanSphere n)
    (hx : ∀ i, (x : EuclideanSpace ℝ (Fin n)) i ≠ 0) :
    ∃ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧ x ∈ octant n s := by
  refine ⟨fun i => if 0 < (x : EuclideanSpace ℝ (Fin n)) i then 1 else -1, fun i => ?_, fun i => ?_⟩
  · by_cases h : 0 < (x : EuclideanSpace ℝ (Fin n)) i <;> simp [h]
  · by_cases h : 0 < (x : EuclideanSpace ℝ (Fin n)) i
    · simp [h]
    · have hlt : (x : EuclideanSpace ℝ (Fin n)) i < 0 := lt_of_le_of_ne (not_lt.1 h) (hx i)
      simpa [h] using hlt

end CliqueSize
