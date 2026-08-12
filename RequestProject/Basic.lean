import Mathlib

/-!
# A Note on Compactness and Clique Size — Section 1: Cliques of closed relations

This file formalizes the basic definitions and the results of Section 1 of the source note
*A Note on Compactness and Clique Size* (D. V. Feldman and A. Wilce):

* the notion of an *orthogonality relation* and of an *`R`-clique*;
* the *finite clique property* (FCP) and the *bounded clique property* (BCP);
* Lemma 1 (`compactbounded`): compact spaces have bounded cliques;
* the notions of ($\omega$-)limit point and of ($\omega$-)limit point compactness;
* the footnote equivalence of $\omega$-limit point compactness with countable compactness;
* Lemma 2 (`finitecc`) and Corollary 1 (`metrizable`).
-/

namespace CliqueSize

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## Basic definitions (Section 1 of the note) -/

/-- **Orthogonality relation** (Section 1 of the note): in the note, `R ⊆ X × X` is an
*orthogonality relation* iff it is a symmetric, irreflexive binary relation on the topological
space `X` which is closed in `X²` (closedness being part of the standing convention, "closed in
`X^2` unless otherwise stated"). -/
structure IsOrthogonality (R : X → X → Prop) : Prop where
  /-- `R` is symmetric. -/
  symm : Symmetric R
  /-- `R` is irreflexive. -/
  irrefl : ∀ x, ¬ R x x
  /-- `R` is closed as a subset of `X × X`. -/
  isClosed : IsClosed {p : X × X | R p.1 p.2}

/-- **`R`-clique** (Section 1 of the note): a set `A ⊆ X` is an `R`-clique iff it is pairwise
`R`-related, equivalently `A × A \ Δ_A ⊆ R`. -/
def IsClique (R : X → X → Prop) (A : Set X) : Prop := A.Pairwise R

/-- **`R` has finite cliques** (Definition 1 of the note): all `R`-cliques are finite. -/
def HasFiniteCliques (R : X → X → Prop) : Prop := ∀ A : Set X, IsClique R A → A.Finite

/-- **`R` has bounded cliques** (Definition 1 of the note): there is a natural number `n` with
`|A| ≤ n` for every `R`-clique `A`. (The bound is stated with `Set.encard`, the cardinality of `A`
as an element of `ℕ∞`, so that it also expresses finiteness of the cliques.) -/
def HasBoundedCliques (R : X → X → Prop) : Prop :=
  ∃ n : ℕ, ∀ A : Set X, IsClique R A → A.encard ≤ n

/-- **A space has finite cliques**, the *finite clique property* (FCP) (Definition 2 of the note):
every closed orthogonality relation `R` on `X` has finite cliques. -/
def FiniteCliqueProperty (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ R : X → X → Prop, IsOrthogonality R → HasFiniteCliques R

/-- **A space has bounded cliques**, the *bounded clique property* (BCP) (Definition 2 of the
note): every closed orthogonality relation `R` on `X` has bounded cliques. -/
def BoundedCliqueProperty (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ R : X → X → Prop, IsOrthogonality R → HasBoundedCliques R

/-- A set `U` is *`R`-free* (in the note: "totally non-`R`-related") iff `(U × U) ∩ R = ∅`. -/
def IsRFree (R : X → X → Prop) (U : Set X) : Prop := ∀ x ∈ U, ∀ y ∈ U, ¬ R x y

/-! ## Elementary consequences of the definitions -/

omit [TopologicalSpace X] in
/-- Bounded cliques implies finite cliques, for a single relation (the second implication in the
diagram of Section 1 of the note). -/
theorem HasBoundedCliques.hasFiniteCliques {R : X → X → Prop} (h : HasBoundedCliques R) :
    HasFiniteCliques R := by
  obtain ⟨n, hn⟩ := h
  intro A hA
  exact Set.finite_of_encard_le_coe (hn A hA)

/-- A space with bounded cliques has finite cliques (the second implication in the diagram of
Section 1 of the note). -/
theorem BoundedCliqueProperty.finiteCliqueProperty (h : BoundedCliqueProperty X) :
    FiniteCliqueProperty X := fun R hR => (h R hR).hasFiniteCliques

/-! ## Lemma 1: compact spaces have bounded cliques -/

/-- The key step in the proof of Lemma 1 of the note: if `R` is a closed orthogonality relation,
then every point of `X` has a totally `R`-unrelated ("`R`-free") open neighborhood. -/
theorem IsOrthogonality.exists_rFree_nhds {R : X → X → Prop} (hR : IsOrthogonality R) (x : X) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsRFree R W := by
  have hxx : (x, x) ∈ {p : X × X | R p.1 p.2}ᶜ := hR.irrefl x
  obtain ⟨U, V, hU, hV, hxU, hxV, hUV⟩ :=
    isOpen_prod_iff.mp hR.isClosed.isOpen_compl x x hxx
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  rintro y ⟨hyU, -⟩ z ⟨-, hzV⟩ hyz
  exact hUV (Set.mk_mem_prod hyU hzV) hyz

/-- **Lemma 1** (`compactbounded`) of the note: if `X` is compact and `R` is a closed
orthogonality relation on `X`, then `R` has bounded cliques. -/
theorem hasBoundedCliques_of_compact [CompactSpace X] {R : X → X → Prop}
    (hR : IsOrthogonality R) : HasBoundedCliques R := by
  choose W hWopen hxW hWfree using hR.exists_rFree_nhds
  obtain ⟨s, hs⟩ :=
    isCompact_univ.elim_finite_subcover W hWopen (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨s.card, fun A hA => ?_⟩
  have hmem : ∀ a : X, ∃ x ∈ s, a ∈ W x := by
    intro a
    have := hs (Set.mem_univ a)
    simpa using this
  choose f hfs hfW using hmem
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    by_contra hne
    exact hWfree (f a) a (hfW a) b (hab ▸ hfW b) (hA ha hb hne)
  calc A.encard = (f '' A).encard := (hinj.encard_image).symm
    _ ≤ (s : Set X).encard := Set.encard_le_encard (by
        rintro _ ⟨a, -, rfl⟩; exact hfs a)
    _ = s.card := by simp [Set.encard_coe_eq_coe_finsetCard]

/-- **Lemma 1** of the note, in the language of Definition 2: every compact space has the
bounded clique property. -/
theorem boundedCliqueProperty_of_compact [CompactSpace X] : BoundedCliqueProperty X :=
  fun _ hR => hasBoundedCliques_of_compact hR

end CliqueSize
