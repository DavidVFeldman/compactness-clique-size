import RequestProject.Powers
import RequestProject.Chromatic

/-!
# A Note on Compactness and Clique Size — the space `ω₁`

This file formalizes the assertions about `ω₁` made in the source note *A Note on Compactness and
Clique Size* (D. V. Feldman and A. Wilce):

> The first implication is strict.  In fact, `ω₁` is an example of a non-compact space with
> bounded cliques.  This follows from Theorem 1 below.  (Section 1 of the note.)

> Theorem 1 implies that any sequentially compact but non-compact space `X` has bounded cliques.
> The classic example is `ω₁`.  […]  Note the displayed statement is best possible: `R` itself
> need not be order-bounded, as the closed cofinal orthogonality
> `R = ({0} × (0, ω₁)) ∪ ((0, ω₁) × {0})` shows (its cliques have size `2`; closedness at `(0,0)`
> holds because `{0}` is clopen).  (Remark 4 of the note.)

It also formalizes the discussion of `ω₁` in Section 5 of the note:

> The first implication is strict: see the discussion of `ω₁` in Remark 4 in §3; split at the `α`
> of the Remark and use the compactness of `[0, α]` …  The remaining piece `(α, ω₁)` is itself
> open and `R`-free, and so serves as one further color class.

The space `ω₁` is realized as the set of countable ordinals with its order topology, i.e. as the
subtype `{o : Ordinal // o < ω_ 1}` of the ordinals.  That it has bounded cliques is obtained in
two ways: from the note's own Corollary 4(b) (`ω₁` is `ω`-bounded, because a countable set of
countable ordinals is bounded by a countable ordinal — regularity of `ℵ₁` — and initial segments
of `ω₁` are compact), and by the direct argument of Remark 4.
-/

namespace CliqueSize

open Set Filter Topology Ordinal Cardinal

/-- The space `ω₁` of countable ordinals, with its order topology (Section 1 and Remark 4 of the
note). -/
abbrev OmegaOne : Type 1 := {o : Ordinal.{0} // o < ω_ 1}

namespace OmegaOne

/-- `ω₁` of Remark 4 of the note is a limit ordinal: the successor of a countable ordinal is
countable. -/
theorem succ_lt {w : Ordinal.{0}} (h : w < ω_ 1) : w + 1 < ω_ 1 := by
  have hl : Order.IsSuccLimit (ω_ 1 : Ordinal.{0}) := isSuccLimit_omega 1
  simpa [Order.succ] using hl.succ_lt h

/-- The space `ω₁` of Remark 4 of the note is nonempty (it contains `0`). -/
instance : Nonempty OmegaOne := ⟨⟨0, omega_pos 1⟩⟩

/-- Remark 4 of the note: `ω₁` has no largest element. -/
theorem exists_gt (a : OmegaOne) : ∃ b : OmegaOne, a < b :=
  ⟨⟨(a : Ordinal.{0}) + 1, succ_lt a.2⟩, by exact lt_add_one (a : Ordinal.{0})⟩

/-- Initial segments of `ω₁` are compact. -/
theorem isCompact_Iic (a : OmegaOne) : IsCompact {w : OmegaOne | w ≤ a} := by
  have h2 : Subtype.val '' {w : OmegaOne | w ≤ a} = Set.Icc (⊥ : Ordinal.{0}) (a : Ordinal) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨bot_le, hw⟩
    · rintro ⟨-, hx⟩
      exact ⟨⟨x, lt_of_le_of_lt hx a.2⟩, hx, rfl⟩
  refine (Topology.IsEmbedding.isCompact_iff
    (IsEmbedding.subtypeVal (p := fun o : Ordinal.{0} => o < ω_ 1))).2 ?_
  rw [h2]
  exact isCompact_Icc

/-- Regularity of `ℵ₁`: a countable set of countable ordinals is bounded by a countable
ordinal. -/
theorem exists_upper_bound_of_countable {S : Set OmegaOne} (hS : S.Countable) :
    ∃ a : OmegaOne, ∀ s ∈ S, s ≤ a := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⟨0, omega_pos 1⟩, by simp⟩
  · obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
    have hlt : (⨆ n : ℕ, (f n : Ordinal.{0})) < ω_ 1 := by
      refine Ordinal.iSup_lt_ord_lift ?_ fun n => (f n).2
      have hcof : (ω_ 1 : Ordinal.{0}).cof = Cardinal.aleph 1 := by
        rw [← Cardinal.ord_aleph 1]
        exact Cardinal.isRegular_aleph_one.cof_eq
      rw [hcof]
      simpa using Cardinal.aleph0_lt_aleph_one
    refine ⟨⟨⨆ n : ℕ, (f n : Ordinal.{0}), hlt⟩, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact Ordinal.le_iSup (fun n : ℕ => (f n : Ordinal.{0})) n

/-- **Corollary 4(b) applied to `ω₁`** (Section 1 and Remark 4 of the note): `ω₁` is
`ω`-bounded — every countable subset has compact closure. -/
theorem omegaBounded : OmegaBounded OmegaOne := by
  intro D hD
  obtain ⟨a, ha⟩ := exists_upper_bound_of_countable hD
  refine IsCompact.of_isClosed_subset (isCompact_Iic a) isClosed_closure ?_
  refine closure_minimal ha ?_
  exact isClosed_Iic

/-- **Section 1 and Remark 4 of the note**: `ω₁` has bounded cliques. -/
theorem boundedCliqueProperty : BoundedCliqueProperty OmegaOne :=
  boundedCliqueProperty_of_omegaBounded omegaBounded

/-- **Section 1 of the note**: `ω₁` is not compact, so the implication "compact ⇒ bounded
cliques" of Lemma 1 is strict. -/
theorem not_compactSpace : ¬ CompactSpace OmegaOne := by
  classical
  intro h
  obtain ⟨F, hF⟩ := (isCompact_univ (X := OmegaOne)).elim_finite_subcover
    (fun a : OmegaOne => {w : OmegaOne | w < a}) (fun a => isOpen_Iio) (fun w _ => by
      obtain ⟨b, hb⟩ := exists_gt w
      exact Set.mem_iUnion.2 ⟨b, hb⟩)
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · obtain ⟨w⟩ := (inferInstance : Nonempty OmegaOne)
    have := hF (Set.mem_univ w)
    simp at this
  · set m := F.max' hFne with hm
    have hmem := hF (Set.mem_univ m)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
    obtain ⟨a, haF, hma⟩ := hmem
    exact absurd (lt_of_lt_of_le hma (F.le_max' a haF)) (lt_irrefl m)

/-- **Section 1 and Remark 4 of the note**: `ω₁` is a non-compact space with bounded cliques,
so the first implication of the note's diagram (compact ⇒ bounded cliques) is strict. -/
theorem exists_boundedCliqueProperty_not_compactSpace :
    ∃ (Y : Type 1) (_ : TopologicalSpace Y), BoundedCliqueProperty Y ∧ ¬ CompactSpace Y :=
  ⟨OmegaOne, inferInstance, boundedCliqueProperty, not_compactSpace⟩

/-! ### The direct argument of Remark 4 -/

/-- The space `ω₁` of Remark 4 of the note carries the order topology, inherited from the
ordinals as an order-connected subset. -/
instance : OrderTopology OmegaOne :=
  haveI : ({o : Ordinal.{0} | o < ω_ 1}).OrdConnected := Set.ordConnected_Iio
  orderTopology_of_ordConnected (t := {o : Ordinal.{0} | o < ω_ 1})

/-- The supremum of a sequence of countable ordinals is countable (regularity of `ℵ₁`). -/
theorem iSup_lt (f : ℕ → OmegaOne) : (⨆ n : ℕ, (f n : Ordinal.{0})) < ω_ 1 := by
  refine Ordinal.iSup_lt_ord_lift ?_ fun n => (f n).2
  have hcof : (ω_ 1 : Ordinal.{0}).cof = Cardinal.aleph 1 := by
    rw [← Cardinal.ord_aleph 1]
    exact Cardinal.isRegular_aleph_one.cof_eq
  rw [hcof]
  simpa using Cardinal.aleph0_lt_aleph_one

/-- **Remark 4 of the note**, the displayed statement: for a closed orthogonality relation `R` on
`ω₁` there is a countable ordinal `α` with `R ∩ ((α, ω₁) × (α, ω₁)) = ∅`.  Otherwise one
recursively chooses related pairs `(aₙ, bₙ)` marching up `ω₁`, and their common supremum `γ`
satisfies `(γ, γ) ∈ closure R = R`, contradicting irreflexivity. -/
theorem exists_bound_of_isOrthogonality {R : OmegaOne → OmegaOne → Prop} (hR : IsOrthogonality R) :
    ∃ α : OmegaOne, ∀ x y : OmegaOne, α < x → α < y → ¬ R x y := by
  by_contra hcon
  push_neg at hcon
  choose f g hf hg hRel using hcon
  -- the recursively chosen pairs, marching up `ω₁`
  set c : ℕ → OmegaOne := fun n => Nat.rec (⟨0, omega_pos 1⟩ : OmegaOne)
    (fun _ w => max (f w) (g w)) n with hc
  have hc0 : ∀ n, c n < f (c n) := fun n => hf (c n)
  have hc1 : ∀ n, c n < g (c n) := fun n => hg (c n)
  have hfle : ∀ n, f (c n) ≤ c (n + 1) := fun n => le_max_left _ _
  have hgle : ∀ n, g (c n) ≤ c (n + 1) := fun n => le_max_right _ _
  have hcmono : StrictMono c := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    exact lt_of_lt_of_le (hc0 n) (hfle n)
  set gamma : OmegaOne := ⟨⨆ n : ℕ, (c n : Ordinal.{0}), iSup_lt c⟩ with hgamma
  have hcle : ∀ n, c n ≤ gamma := fun n =>
    Ordinal.le_iSup (fun n : ℕ => (c n : Ordinal.{0})) n
  have hlt_gamma : ∀ z : OmegaOne, z < gamma → ∃ n, z < c n := by
    intro z hz
    exact Ordinal.lt_iSup_iff.1 hz
  -- both sequences converge to `γ`
  have htend : ∀ h : ℕ → OmegaOne, (∀ n, c n < h n) → (∀ n, h n ≤ c (n + 1)) →
      Filter.Tendsto h Filter.atTop (𝓝 gamma) := by
    intro h hlow hhigh
    refine tendsto_order.2 ⟨fun z hz => ?_, fun z hz => ?_⟩
    · obtain ⟨N, hN⟩ := hlt_gamma z hz
      refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      exact lt_of_lt_of_le (lt_of_lt_of_le hN (hcmono.monotone hn)) (le_of_lt (hlow n))
    · exact Filter.Eventually.of_forall fun n =>
        lt_of_le_of_lt (le_trans (hhigh n) (hcle (n + 1))) hz
  have hta := htend (fun n => f (c n)) hc0 hfle
  have htb := htend (fun n => g (c n)) hc1 hgle
  have hmem : (gamma, gamma) ∈ closure {p : OmegaOne × OmegaOne | R p.1 p.2} :=
    mem_closure_of_tendsto (hta.prodMk_nhds htb)
      (Filter.Eventually.of_forall fun n => hRel (c n))
  rw [hR.isClosed.closure_eq] at hmem
  exact hR.irrefl gamma hmem

/-- **Remark 4 of the note**, the direct argument: a clique of a closed orthogonality `R` on `ω₁`
has at most one member above the bound `α` of `exists_bound_of_isOrthogonality`, and its remainder
is a clique of the restriction of `R` to the compact space `[0, α]`, which is bounded by Lemma 1.
This gives a direct proof that `ω₁` has bounded cliques. -/
theorem hasBoundedCliques_direct {R : OmegaOne → OmegaOne → Prop} (hR : IsOrthogonality R) :
    HasBoundedCliques R := by
  obtain ⟨α, hα⟩ := exists_bound_of_isOrthogonality hR
  haveI : CompactSpace {w : OmegaOne // w ∈ {w : OmegaOne | w ≤ α}} :=
    isCompact_iff_compactSpace.1 (isCompact_Iic α)
  set S := {w : OmegaOne | w ≤ α} with hS
  set R' : S → S → Prop := fun x y => R (x : OmegaOne) (y : OmegaOne) with hR'def
  have hR' : IsOrthogonality R' := by
    refine ⟨fun x y h => hR.symm h, fun x h => hR.irrefl _ h, ?_⟩
    have hcont : Continuous fun p : S × S => ((p.1 : OmegaOne), (p.2 : OmegaOne)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact hR.isClosed.preimage hcont
  obtain ⟨n, hn⟩ := hasBoundedCliques_of_compact hR'
  refine ⟨n + 1, fun A hA => ?_⟩
  have hlow : (A ∩ S).encard ≤ n := by
    have hclique : IsClique R' (Subtype.val ⁻¹' A : Set S) := by
      intro x hx y hy hxy
      exact hA hx hy fun h => hxy (Subtype.ext h)
    have himg : Subtype.val '' (Subtype.val ⁻¹' A : Set S) = A ∩ S := by
      rw [Subtype.image_preimage_coe]
      exact Set.inter_comm _ _
    calc (A ∩ S).encard = (Subtype.val '' (Subtype.val ⁻¹' A : Set S)).encard := by rw [himg]
      _ = (Subtype.val ⁻¹' A : Set S).encard :=
          Set.InjOn.encard_image Subtype.val_injective.injOn
      _ ≤ n := hn _ hclique
  have hhigh : (A \ S).encard ≤ 1 := by
    refine Set.encard_le_one_iff_subsingleton.2 fun x hx y hy => ?_
    by_contra hxy
    have hxα : α < x := lt_of_not_ge hx.2
    have hyα : α < y := lt_of_not_ge hy.2
    exact hα x y hxα hyα (hA hx.1 hy.1 hxy)
  have hsub : A ⊆ (A ∩ S) ∪ (A \ S) := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  calc A.encard ≤ ((A ∩ S) ∪ (A \ S)).encard := Set.encard_mono hsub
    _ ≤ (A ∩ S).encard + (A \ S).encard := Set.encard_union_le _ _
    _ ≤ (n : ℕ∞) + 1 := by gcongr
    _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-- **Section 5 of the note**: `ω₁` has finite open chromatic number.  Split at the `α` of
Remark 4: the initial segment `[0, α]` is compact, so finitely many `R`-free open sets cover it,
while the remaining piece `(α, ω₁)` is itself open and `R`-free, and serves as one further colour
class.  Combined with `not_compactSpace`, this shows that the implication
"compact ⇒ finite open chromatic number" is strict. -/
theorem finiteOpenChromatic : FiniteOpenChromatic OmegaOne := by
  intro R hR
  obtain ⟨α, hα⟩ := exists_bound_of_isOrthogonality hR
  choose W hWopen hxW hWfree using hR.exists_rFree_nhds
  obtain ⟨s, hs⟩ := (isCompact_Iic α).elim_finite_subcover W hWopen
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  set V : Set OmegaOne := {w : OmegaOne | α < w} with hV
  set U : Set (Set OmegaOne) := insert V ((fun x => W x) '' (s : Set OmegaOne)) with hU
  have hUfin : U.Finite := (s.finite_toSet.image _).insert V
  have hUprop : ∀ T ∈ U, IsOpen T ∧ IsRFree R T := by
    rintro T (rfl | ⟨x, -, rfl⟩)
    · exact ⟨isOpen_Ioi, fun a ha b hb => hα a b ha hb⟩
    · exact ⟨hWopen x, hWfree x⟩
  have hUcover : ⋃₀ U = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    by_cases hw : w ≤ α
    · obtain ⟨x, hx, hwx⟩ : ∃ x ∈ s, w ∈ W x := by
        have := hs (show w ∈ {w : OmegaOne | w ≤ α} from hw)
        simpa using this
      exact ⟨W x, Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩, hwx⟩
    · exact ⟨V, Set.mem_insert _ _, lt_of_not_ge hw⟩
  have hle : chiOp R ≤ U.encard := sInf_le ⟨U, hUprop, hUcover, rfl⟩
  exact ne_top_of_le_ne_top hUfin.encard_lt_top.ne hle

/-- **Section 5 of the note**: the implication "compact ⇒ finite open chromatic number" is
strict, as witnessed by `ω₁`. -/
theorem exists_finiteOpenChromatic_not_compactSpace :
    ∃ (Y : Type 1) (_ : TopologicalSpace Y), FiniteOpenChromatic Y ∧ ¬ CompactSpace Y :=
  ⟨OmegaOne, inferInstance, finiteOpenChromatic, not_compactSpace⟩

/-! ### The cofinal closed orthogonality of Remark 4 -/

/-- The relation `R = ({0} × (0, ω₁)) ∪ ((0, ω₁) × {0})` of Remark 4 of the note: `0` is related
to every nonzero countable ordinal, and to nothing else. -/
def cofinalRel (x y : OmegaOne) : Prop :=
  ((x : Ordinal.{0}) = 0 ∧ (y : Ordinal.{0}) ≠ 0) ∨ ((x : Ordinal.{0}) ≠ 0 ∧ (y : Ordinal.{0}) = 0)

/-- In `ω₁`, the singleton `{0}` is clopen (`0` is not a limit ordinal). -/
theorem isClopen_zero : IsClopen {w : OmegaOne | (w : Ordinal.{0}) = 0} := by
  constructor
  · have : {w : OmegaOne | (w : Ordinal.{0}) = 0} = {(⟨0, omega_pos 1⟩ : OmegaOne)} := by
      ext w
      simp [Subtype.ext_iff]
    rw [this]
    exact isClosed_singleton
  · have : {w : OmegaOne | (w : Ordinal.{0}) = 0} =
        {w : OmegaOne | w < (⟨1, by simpa using succ_lt (omega_pos 1)⟩ : OmegaOne)} := by
      ext w
      simp only [Set.mem_setOf_eq, ← Subtype.coe_lt_coe]
      exact ⟨fun h => by rw [h]; exact zero_lt_one, fun h => by
        simpa [Ordinal.lt_one_iff_zero] using h⟩
    rw [this]
    exact isOpen_Iio

/-- **Remark 4 of the note**: the cofinal relation `R` is a closed orthogonality relation on
`ω₁`; closedness at `(0,0)` holds because `{0}` is clopen. -/
theorem isOrthogonality_cofinalRel : IsOrthogonality cofinalRel := by
  refine ⟨fun x y h => ?_, fun x h => ?_, ?_⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h2, h1⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 h1
    · exact h1 h2
  · have hz := isClopen_zero
    have hset : {p : OmegaOne × OmegaOne | cofinalRel p.1 p.2} =
        (({w : OmegaOne | (w : Ordinal.{0}) = 0} ×ˢ {w : OmegaOne | (w : Ordinal.{0}) = 0}ᶜ) ∪
          ({w : OmegaOne | (w : Ordinal.{0}) = 0}ᶜ ×ˢ {w : OmegaOne | (w : Ordinal.{0}) = 0})) := by
      ext ⟨x, y⟩
      simp [cofinalRel, Set.mem_prod, and_comm]
    rw [hset]
    exact ((hz.1.prod hz.2.isClosed_compl).union (hz.2.isClosed_compl.prod hz.1))

/-- **Remark 4 of the note**: the cliques of the cofinal relation have at most two elements. -/
theorem encard_le_two_of_isClique_cofinalRel {A : Set OmegaOne} (hA : IsClique cofinalRel A) :
    A.encard ≤ 2 := by
  set z0 : OmegaOne := ⟨0, omega_pos 1⟩ with hz0
  have hsub1 : (A \ {z0}).encard ≤ 1 := by
    refine Set.encard_le_one_iff_subsingleton.2 ?_
    intro a ha b hb
    by_contra hab
    have ha0 : (a : Ordinal.{0}) ≠ 0 := fun h => ha.2 (Subtype.ext h)
    have hb0 : (b : Ordinal.{0}) ≠ 0 := fun h => hb.2 (Subtype.ext h)
    rcases hA ha.1 hb.1 hab with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ha0 h1
    · exact hb0 h2
  have hAsub : A ⊆ insert z0 (A \ {z0}) := by
    intro x hx
    by_cases h : x = z0
    · exact Set.mem_insert_iff.2 (Or.inl h)
    · exact Set.mem_insert_iff.2 (Or.inr ⟨hx, h⟩)
  calc A.encard ≤ (insert z0 (A \ {z0})).encard := Set.encard_mono hAsub
    _ ≤ (A \ {z0}).encard + 1 := Set.encard_insert_le _ _
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num

/-- **Remark 4 of the note**: the cofinal relation is not order-bounded — it has related pairs
with a coordinate above any given countable ordinal, even though (by the displayed statement of
the remark) every closed orthogonality vanishes above some countable ordinal on *both*
coordinates. -/
theorem cofinalRel_cofinal (a : OmegaOne) :
    ∃ x y : OmegaOne, cofinalRel x y ∧ a < y := by
  obtain ⟨b, hb⟩ := exists_gt a
  obtain ⟨c, hc⟩ := exists_gt b
  refine ⟨⟨0, omega_pos 1⟩, c, Or.inl ⟨rfl, ?_⟩, lt_trans hb hc⟩
  intro h0
  have hlt : (a : Ordinal.{0}) < 0 := by
    rw [← h0]
    exact lt_trans hb hc
  simp at hlt

end OmegaOne

end CliqueSize
