import RequestProject.Compactness

/-!
# A Note on Compactness and Clique Size — Section 2: A Galois Connection

This file formalizes Section 2 of the source note *A Note on Compactness and Clique Size*
(D. V. Feldman and A. Wilce):

* the orthogonality relation `⊥_𝒰` attached to an open cover `𝒰`, and the notion of a
  `𝒰`-separated set;
* the cover `Cov(R)` of all totally non-`R`-related open sets;
* **Proposition 1** (`galois`): `(⊥, Cov)` is an antitone Galois connection;
* **Corollary 2** (`covers`): reduction of the finite/bounded clique properties to covers;
* strong star-compactness and **Corollary 3** (`starcompact`).
-/

namespace CliqueSize

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## Covers and the relation `⊥_𝒰` -/

/-- An *open cover* of `X`: a family of open sets whose union is `X`. -/
def IsOpenCover (U : Set (Set X)) : Prop := (∀ V ∈ U, IsOpen V) ∧ ⋃₀ U = Set.univ

/-- The relation `x ⊥_𝒰 y` of Section 2 of the note: no member of the cover `𝒰` contains both
`x` and `y`. -/
def perpCover (U : Set (Set X)) (x y : X) : Prop := ¬ ∃ V ∈ U, x ∈ V ∧ y ∈ V

/-- A set is *`𝒰`-separated* (Section 2 of the note) iff no two distinct points of it lie in a
common member of `𝒰`; equivalently, it is a `⊥_𝒰`-clique. -/
def IsSeparatedBy (U : Set (Set X)) (A : Set X) : Prop := IsClique (perpCover U) A

/-- Section 2 of the note: for an open cover `𝒰`, the relation `⊥_𝒰` is a closed (possibly
empty) orthogonality relation. -/
theorem isOrthogonality_perpCover {U : Set (Set X)} (hU : IsOpenCover U) :
    IsOrthogonality (perpCover U) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x y h ⟨V, hV, hyV, hxV⟩
    exact h ⟨V, hV, hxV, hyV⟩
  · intro x hx
    have : x ∈ ⋃₀ U := hU.2 ▸ Set.mem_univ x
    obtain ⟨V, hV, hxV⟩ := this
    exact hx ⟨V, hV, hxV, hxV⟩
  · rw [← isOpen_compl_iff]
    have hEq : {p : X × X | perpCover U p.1 p.2}ᶜ = ⋃ V ∈ U, V ×ˢ V := by
      ext ⟨x, y⟩
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, perpCover, not_not, Set.mem_iUnion,
        Set.mem_prod, exists_prop]
    rw [hEq]
    exact isOpen_biUnion fun V hV => (hU.1 V hV).prod (hU.1 V hV)

/-- The cover `Cov(R)` of Section 2 of the note: the collection of all totally non-`R`-related
open subsets of `X`. -/
def Cov (R : X → X → Prop) : Set (Set X) := {U : Set X | IsOpen U ∧ IsRFree R U}

/-- Section 2 of the note: `Cov(R)` really is an open cover, by the argument of the proof of
Lemma 1. -/
theorem isOpenCover_cov {R : X → X → Prop} (hR : IsOrthogonality R) : IsOpenCover (Cov R) := by
  refine ⟨fun V hV => hV.1, Set.eq_univ_of_forall fun x => ?_⟩
  obtain ⟨W, hWopen, hxW, hWfree⟩ := hR.exists_rFree_nhds x
  exact ⟨W, ⟨hWopen, hWfree⟩, hxW⟩

/-! ## Proposition 1: the Galois connection -/

/-- **Proposition 1** (`galois`) of the note: `(⊥, Cov)` is an antitone Galois connection between
open covers and closed orthogonality relations, ordered by inclusion: for every open cover `𝒰`
and closed orthogonality `R`, `R ⊆ ⊥_𝒰 ↔ 𝒰 ⊆ Cov(R)`. -/
theorem galoisConnection_perpCover_cov {U : Set (Set X)} (hU : IsOpenCover U)
    {R : X → X → Prop} :
    (∀ x y, R x y → perpCover U x y) ↔ U ⊆ Cov R := by
  constructor
  · intro h V hV
    refine ⟨hU.1 V hV, fun x hx y hy hxy => ?_⟩
    exact h x y hxy ⟨V, hV, hx, hy⟩
  · rintro h x y hxy ⟨V, hV, hxV, hyV⟩
    exact (h hV).2 x hxV y hyV hxy

/-- Section 2 of the note: `R ⊆ ⊥_{Cov(R)}` always holds. -/
theorem subset_perpCover_cov {R : X → X → Prop} (hR : IsOrthogonality R) (x y : X) (hxy : R x y) :
    perpCover (Cov R) x y :=
  (galoisConnection_perpCover_cov (isOpenCover_cov hR)).mpr (le_refl _) x y hxy

/-! ## Corollary 2: reduction to covers -/

/-- **Corollary 2** (`covers`) of the note, finite version: `X` has finite cliques iff for every
open cover `𝒰`, every `𝒰`-separated set is finite. -/
theorem finiteCliqueProperty_iff_separated_finite :
    FiniteCliqueProperty X ↔
      ∀ U : Set (Set X), IsOpenCover U → ∀ A : Set X, IsSeparatedBy U A → A.Finite := by
  constructor
  · intro h U hU A hA
    exact h _ (isOrthogonality_perpCover hU) A hA
  · intro h R hR A hA
    refine h (Cov R) (isOpenCover_cov hR) A ?_
    intro x hx y hy hxy
    exact subset_perpCover_cov hR x y (hA hx hy hxy)

/-- **Corollary 2** (`covers`) of the note, bounded version: `X` has bounded cliques iff for
every open cover `𝒰` there is `n ∈ ℕ` with all `𝒰`-separated sets of size at most `n`. -/
theorem boundedCliqueProperty_iff_separated_bounded :
    BoundedCliqueProperty X ↔
      ∀ U : Set (Set X), IsOpenCover U → ∃ n : ℕ, ∀ A : Set X, IsSeparatedBy U A →
        A.encard ≤ n := by
  constructor
  · intro h U hU
    exact h _ (isOrthogonality_perpCover hU)
  · intro h R hR
    obtain ⟨n, hn⟩ := h (Cov R) (isOpenCover_cov hR)
    refine ⟨n, fun A hA => hn A ?_⟩
    intro x hx y hy hxy
    exact subset_perpCover_cov hR x y (hA hx hy hxy)

/-- Section 2 of the note: the reduction to covers re-proves Lemma 1 — a compact space has
bounded cliques, since a `𝒰`-separated set meets each member of a finite subcover at most
once. -/
theorem boundedCliqueProperty_of_compact_via_covers [CompactSpace X] :
    BoundedCliqueProperty X := by
  rw [boundedCliqueProperty_iff_separated_bounded]
  intro U hU
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : U => (V : Set X))
    (fun V => hU.1 V V.2) (fun x _ => by
      obtain ⟨V, hV, hxV⟩ := Set.mem_sUnion.mp (hU.2 ▸ Set.mem_univ x)
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxV⟩)
  refine ⟨s.card, fun A hA => ?_⟩
  have hmem : ∀ a : X, ∃ V ∈ s, a ∈ (V : Set X) := by
    intro a
    have := hs (Set.mem_univ a)
    simpa using this
  choose f hfs hfV using hmem
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    by_contra hne
    exact hA ha hb hne ⟨(f a : Set X), (f a).2, hfV a, hab ▸ hfV b⟩
  calc A.encard = (f '' A).encard := (hinj.encard_image).symm
    _ ≤ (s : Set U).encard := Set.encard_le_encard (by rintro _ ⟨a, -, rfl⟩; exact hfs a)
    _ = s.card := by simp [Set.encard_coe_eq_coe_finsetCard]

/-! ## Corollary 3: strong star-compactness -/

/-- The star `St(F, 𝒰)` of a set `F` with respect to a cover `𝒰` (Section 2 of the note): the
union of all members of `𝒰` that meet `F`. -/
def star (F : Set X) (U : Set (Set X)) : Set X := ⋃ V ∈ {V ∈ U | (F ∩ V).Nonempty}, V

/-- **Strong star-compactness** (Section 2 of the note): for every open cover `𝒰` there is a
finite set `F` with `St(F, 𝒰) = X`. -/
def StronglyStarCompact (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : Set (Set X), IsOpenCover U → ∃ F : Set X, F.Finite ∧ star F U = Set.univ

/-- Section 2 of the note: a maximal `𝒰`-separated set `F` satisfies `St(F, 𝒰) = X`. -/
theorem star_eq_univ_of_maximal_separated {U : Set (Set X)} (hU : IsOpenCover U) {F : Set X}
    (hF : Maximal (fun A : Set X => IsSeparatedBy U A) F) : star F U = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  by_contra hy
  -- if `y ∉ St(F, 𝒰)`, then `F ∪ {y}` is again `𝒰`-separated, contradicting maximality
  have hyF : y ∉ F := by
    intro hyF
    obtain ⟨V, hV, hyV⟩ := Set.mem_sUnion.mp (hU.2 ▸ Set.mem_univ y)
    exact hy (Set.mem_biUnion (show V ∈ {V ∈ U | (F ∩ V).Nonempty} from
      ⟨hV, ⟨y, hyF, hyV⟩⟩) hyV)
  have hsep : IsSeparatedBy U (insert y F) := by
    intro a ha b hb hab
    rintro ⟨V, hV, haV, hbV⟩
    rcases ha with ha | ha
    · subst ha
      rcases hb with hb | hb
      · exact hab hb.symm
      · exact hy (Set.mem_biUnion (show V ∈ {V ∈ U | (F ∩ V).Nonempty} from
          ⟨hV, ⟨b, hb, hbV⟩⟩) haV)
    · rcases hb with hb | hb
      · subst hb
        exact hy (Set.mem_biUnion (show V ∈ {V ∈ U | (F ∩ V).Nonempty} from
          ⟨hV, ⟨a, ha, haV⟩⟩) hbV)
      · exact hF.1 ha hb hab ⟨V, hV, haV, hbV⟩
  exact hyF (hF.2 hsep (Set.subset_insert y F) (Set.mem_insert y F))

omit [TopologicalSpace X] in
/-- Section 2 of the note: maximal `𝒰`-separated sets exist, by Zorn's lemma. -/
theorem exists_maximal_separated (U : Set (Set X)) :
    ∃ F : Set X, Maximal (fun A : Set X => IsSeparatedBy U A) F := by
  have h : ∀ c ⊆ {A : Set X | IsSeparatedBy U A}, IsChain (· ⊆ ·) c →
      ∃ ub ∈ {A : Set X | IsSeparatedBy U A}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hchain
    exact ⟨⋃₀ c, hchain.pairwise_sUnion.mpr fun s hs => hc hs,
      fun s hs => Set.subset_sUnion_of_mem hs⟩
  exact zorn_subset _ h

/-- **Corollary 3** (`starcompact`) of the note: a space with finite cliques is strongly
star-compact. -/
theorem stronglyStarCompact_of_finiteCliqueProperty (hX : FiniteCliqueProperty X) :
    StronglyStarCompact X := by
  intro U hU
  obtain ⟨F, hF⟩ := exists_maximal_separated U
  refine ⟨F, ?_, star_eq_univ_of_maximal_separated hU hF⟩
  exact hX _ (isOrthogonality_perpCover hU) F hF.1

end CliqueSize
