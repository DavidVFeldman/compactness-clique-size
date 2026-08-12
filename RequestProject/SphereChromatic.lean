import RequestProject.Sphere

/-!
# A Note on Compactness and Clique Size — the upper bound `χ_op(S², ⊥) ≤ 24`

This file formalizes the upper bound of the estimate

> `4 = χ(S², ⊥) ≤ χ_op(S², ⊥) ≤ 24`

of Section 5 of the source note *A Note on Compactness and Clique Size* (D. V. Feldman and
A. Wilce).

The note's argument runs as follows:

> The eight open octants are orthogonality-free and cover `S² \ C`, where `C` is the union of the
> three coordinate great circles.  Rotations take orthogonality-free opens to orthogonality-free
> opens.  Choosing `ρ₂`, `ρ₃` with `C ∩ ρ₂(C) ∩ ρ₃(C) = ∅` (a generic `ρ₂` gives `C ∩ ρ₂(C)`
> finite; then choose a `ρ₃` with `ρ₃(C)` avoiding these finitely many points) gives us
> `χ_op(S², ⊥) ≤ 24`.

Here the genericity argument for the rotations is replaced by three *explicit* orthonormal frames
of `ℝ³` (the standard one and two frames with rational entries, coming from rational rotation
matrices), for which the required disjointness `C ∩ ρ₂(C) ∩ ρ₃(C) = ∅` is checked by a finite
computation: any three rows, one taken from each frame, are linearly independent, so no unit
vector can be orthogonal to a row of each of the three frames.  Each frame contributes eight open
"octants" (the sets on which all three coordinates in that frame have prescribed strict signs),
which are open and orthogonality-free, and the resulting `24` sets cover `S²`.

The lower bound `4 = χ(S², ⊥)` rests on the Godsil–Zaks theorem from the literature and is not
formalized; Question 3 of the note (the exact value of `χ_op(S^{n-1}, ⊥)`) is left open, as it is
in the note.
-/

namespace CliqueSize

open Set Filter Topology

namespace SphereChromatic

/-- The nine rows of the three orthonormal frames of `ℝ³` used in Section 5 of the note.

`frameRow 0` is the standard frame (whose "octants" are the eight open octants of the note),
while `frameRow 1` and `frameRow 2` are the rows of two rational rotation matrices, playing the
role of the rotated frames `ρ₂`, `ρ₃` of the note's argument. -/
noncomputable def frameRow : Fin 3 → Fin 3 → ℝ × ℝ × ℝ
  | 0, 0 => (1, 0, 0)
  | 0, 1 => (0, 1, 0)
  | 0, _ => (0, 0, 1)
  | 1, 0 => (1/3, 2/3, 2/3)
  | 1, 1 => (2/3, 1/3, -2/3)
  | 1, _ => (-2/3, 2/3, -1/3)
  | 2, 0 => (3/7, 2/7, -6/7)
  | 2, 1 => (-6/7, 3/7, -2/7)
  | 2, _ => (2/7, 6/7, 3/7)

/-- The coordinate of a vector `x ∈ ℝ³` along the `i`-th row of the `t`-th frame of Section 5 of
the note, i.e. the inner product `⟪frameRow t i, x⟫`. -/
noncomputable def frameForm (t i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  (frameRow t i).1 * x 0 + (frameRow t i).2.1 * x 1 + (frameRow t i).2.2 * x 2

/-- Each of the three frames of Section 5 of the note is orthonormal: Parseval's identity holds
for the coordinates it defines. -/
theorem frameForm_parseval (t : Fin 3) (x y : Fin 3 → ℝ) :
    ∑ i, frameForm t i x * frameForm t i y = ∑ m, x m * y m := by
  fin_cases t <;> simp only [frameForm, frameRow, Fin.sum_univ_three] <;> ring

set_option maxHeartbeats 1000000 in
/-- The disjointness `C ∩ ρ₂(C) ∩ ρ₃(C) = ∅` of Section 5 of the note, in the form actually
used: any three rows, one from each of the three frames, are linearly independent, so a vector
orthogonal to one row of each frame is zero.  (Verified by a finite computation over the `27`
possible triples of rows.) -/
theorem eq_zero_of_frameForm_eq_zero (x : Fin 3 → ℝ) (i j k : Fin 3)
    (h0 : frameForm 0 i x = 0) (h1 : frameForm 1 j x = 0) (h2 : frameForm 2 k x = 0) :
    x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [frameForm, frameRow] at h0 h1 h2 <;>
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The sign `±1` attached to a boolean, used to index the eight "octants" of a frame in
Section 5 of the note. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- The signs `±1` indexing the octants of a frame in Section 5 of the note square to `1`. -/
theorem sign_sq (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

/-- The open "octant" of `S²` cut out by the `t`-th frame of Section 5 of the note and a choice
`s` of signs: the set of unit vectors whose coordinates in that frame all have the prescribed
strict sign.  For `t = 0` these are literally "the eight open octants" of the note. -/
def frameOctant (t : Fin 3) (s : Fin 3 → Bool) : Set (EuclideanSphere 3) :=
  {x | ∀ i, 0 < sign (s i) *
    frameForm t i fun m => (x : EuclideanSpace ℝ (Fin 3)) m}

/-- Section 5 of the note: the octants of a frame are open. -/
theorem isOpen_frameOctant (t : Fin 3) (s : Fin 3 → Bool) : IsOpen (frameOctant t s) := by
  have hcoord : ∀ m : Fin 3,
      Continuous fun x : EuclideanSphere 3 => (x : EuclideanSpace ℝ (Fin 3)) m := by
    intro m
    exact (PiLp.continuous_apply 2 (fun _ => ℝ) m).comp continuous_subtype_val
  have : frameOctant t s = ⋂ i : Fin 3,
      {x : EuclideanSphere 3 | 0 < sign (s i) *
        frameForm t i fun m => (x : EuclideanSpace ℝ (Fin 3)) m} := by
    ext x
    simp [frameOctant]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  refine isOpen_lt continuous_const ?_
  unfold frameForm
  exact (continuous_const.mul (((continuous_const.mul (hcoord 0)).add
    (continuous_const.mul (hcoord 1))).add (continuous_const.mul (hcoord 2))))

/-- **Section 5 of the note**: the octants of a frame are orthogonality-free (`R`-free in the
sense of Section 2).  Indeed by Parseval's identity the inner product of two points of a common
octant is a sum of three strictly positive terms. -/
theorem isRFree_frameOctant (t : Fin 3) (s : Fin 3 → Bool) :
    IsRFree (sphereOrth 3) (frameOctant t s) := by
  intro x hx y hy hxy
  set u : Fin 3 → ℝ := fun m => (x : EuclideanSpace ℝ (Fin 3)) m with hu
  set v : Fin 3 → ℝ := fun m => (y : EuclideanSpace ℝ (Fin 3)) m with hv
  have hpos : ∀ i : Fin 3, 0 < frameForm t i u * frameForm t i v := by
    intro i
    have hxi := hx i
    have hyi := hy i
    have hs := sign_sq (s i)
    nlinarith [mul_pos hxi hyi]
  have hsum : 0 < ∑ i, frameForm t i u * frameForm t i v :=
    Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  rw [frameForm_parseval] at hsum
  have hinner : inner ℝ (x : EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 3)) =
      ∑ m, u m * v m := by
    simp [PiLp.inner_apply, mul_comm, hu, hv]
  rw [sphereOrth, hinner] at hxy
  exact absurd hxy (ne_of_gt hsum)

/-- **Section 5 of the note**: the `24` octants of the three frames cover `S²`.  A unit vector
missed by all of them would be orthogonal to a row of each of the three frames, hence zero. -/
theorem exists_mem_frameOctant (x : EuclideanSphere 3) :
    ∃ (t : Fin 3) (s : Fin 3 → Bool), x ∈ frameOctant t s := by
  set u : Fin 3 → ℝ := fun m => (x : EuclideanSpace ℝ (Fin 3)) m with hu
  by_cases hall : ∀ t : Fin 3, ∃ i : Fin 3, frameForm t i u = 0
  · obtain ⟨i, hi⟩ := hall 0
    obtain ⟨j, hj⟩ := hall 1
    obtain ⟨k, hk⟩ := hall 2
    obtain ⟨h0, h1, h2⟩ := eq_zero_of_frameForm_eq_zero u i j k hi hj hk
    have hx0 : (x : EuclideanSpace ℝ (Fin 3)) = 0 := by
      refine PiLp.ext fun m => ?_
      fin_cases m
      · exact h0
      · exact h1
      · exact h2
    have hnorm := norm_eq_one_of_mem_euclideanSphere x
    rw [hx0] at hnorm
    simp at hnorm
  · push_neg at hall
    obtain ⟨t, ht⟩ := hall
    refine ⟨t, fun i => decide (0 < frameForm t i u), fun i => ?_⟩
    have hne := ht i
    by_cases hpos : 0 < frameForm t i u
    · simp only [hpos, decide_true, sign, if_true]
      simpa using hpos
    · have hlt : frameForm t i u < 0 := lt_of_le_of_ne (not_lt.1 hpos) hne
      simp only [hpos, decide_false, sign]
      simpa using hlt

/-- The family of `24` open orthogonality-free subsets of `S²` produced by the three frames of
Section 5 of the note. -/
def frameCover : Set (Set (EuclideanSphere 3)) :=
  Set.range fun p : Fin 3 × (Fin 3 → Bool) => frameOctant p.1 p.2

/-- Section 5 of the note: the cover of `S²` by the octants of the three frames consists of at
most `3 × 2³ = 24` sets. -/
theorem frameCover_encard_le : frameCover.encard ≤ 24 := by
  have himg : frameCover =
      (fun p : Fin 3 × (Fin 3 → Bool) => frameOctant p.1 p.2) ''
        ((Finset.univ : Finset (Fin 3 × (Fin 3 → Bool))) : Set (Fin 3 × (Fin 3 → Bool))) := by
    simp [frameCover, Set.image_univ]
  rw [himg]
  calc ((fun p : Fin 3 × (Fin 3 → Bool) => frameOctant p.1 p.2) ''
        ((Finset.univ : Finset (Fin 3 × (Fin 3 → Bool))) : Set (Fin 3 × (Fin 3 → Bool)))).encard
      ≤ (((Finset.univ : Finset (Fin 3 × (Fin 3 → Bool)))) :
          Set (Fin 3 × (Fin 3 → Bool))).encard := Set.encard_image_le _ _
    _ = ((Finset.univ : Finset (Fin 3 × (Fin 3 → Bool))).card : ℕ∞) := by
        simp
    _ = 24 := by simp

end SphereChromatic

open SphereChromatic in
/-- **Section 5 of the note**, the upper bound of `4 = χ(S², ⊥) ≤ χ_op(S², ⊥) ≤ 24`: the open
chromatic number of literal orthogonality on the sphere `S² ⊆ ℝ³` is at most `24`, since the
eight open octants of each of three suitably chosen orthonormal frames are open,
orthogonality-free, and together cover `S²`. -/
theorem chiOp_sphereOrth_three_le : chiOp (sphereOrth 3) ≤ 24 := by
  have hle : chiOp (sphereOrth 3) ≤ frameCover.encard := by
    refine sInf_le ⟨frameCover, ?_, ?_, rfl⟩
    · rintro _ ⟨p, rfl⟩
      exact ⟨isOpen_frameOctant p.1 p.2, isRFree_frameOctant p.1 p.2⟩
    · refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨t, s, hts⟩ := exists_mem_frameOctant x
      exact ⟨frameOctant t s, ⟨(t, s), rfl⟩, hts⟩
  exact hle.trans frameCover_encard_le

/-- **Section 5 of the note**: combining the clique bound `3 ≤ χ_op(S², ⊥)` with the covering by
the octants of three frames, the open chromatic number of literal orthogonality on `S²` lies
between `3` and `24`.  (The note's sharper lower bound `4`, from the Godsil–Zaks theorem on the
chromatic number of the orthogonality graph of `S²`, is not formalized here.) -/
theorem chiOp_sphereOrth_three_bounds : 3 ≤ chiOp (sphereOrth 3) ∧ chiOp (sphereOrth 3) ≤ 24 :=
  ⟨by simpa using le_chiOp_sphereOrth 3, chiOp_sphereOrth_three_le⟩

end CliqueSize
