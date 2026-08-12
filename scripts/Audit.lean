/-
Axiom audit for *A Note on Compactness and Clique Size*.

Run from the repository root:

    lake env lean scripts/Audit.lean

Every declaration below must report exactly

    'X' depends on axioms: [propext, Classical.choice, Quot.sound]

(or a subset thereof).  Any other axiom -- in particular `sorryAx` -- is a failure.
The CI workflow parses this output and fails the build if anything else appears.
-/
import RequestProject.Main

open CliqueSize

-- Section 1: Lemmas 1 and 2, Corollary 1
#print axioms CliqueSize.boundedCliqueProperty_of_compact
#print axioms CliqueSize.hasBoundedCliques_of_compact
#print axioms CliqueSize.omegaLimitPointCompact_iff_countablyCompact
#print axioms CliqueSize.finiteCliqueProperty_of_omegaLimitPointCompact
#print axioms CliqueSize.limitPointCompact_of_finiteCliqueProperty
#print axioms CliqueSize.finiteCliqueProperty_iff_countablyCompact_t1
#print axioms CliqueSize.compactSpace_of_finiteCliqueProperty
#print axioms CliqueSize.hasBoundedCliques_of_compact_uniform

-- Section 1: Remark 2 (non-T1 example)
#print axioms CliqueSize.exists_limitPointCompact_not_finiteCliqueProperty

-- Section 2: the Galois connection, its corollaries, star-compactness
#print axioms CliqueSize.galoisConnection_perpCover_cov
#print axioms CliqueSize.finiteCliqueProperty_iff_separated_finite
#print axioms CliqueSize.boundedCliqueProperty_iff_separated_bounded
#print axioms CliqueSize.stronglyStarCompact_of_finiteCliqueProperty
#print axioms CliqueSize.exists_stronglyStarCompact_not_finiteCliqueProperty

-- Section 3: Theorem 1 and Corollary 4 (a), (b), (c)
#print axioms CliqueSize.boundedCliqueProperty_of_countablyCompact_pi
#print axioms CliqueSize.boundedCliqueProperty_of_seqCompactSpace
#print axioms CliqueSize.boundedCliqueProperty_of_omegaBounded
#print axioms CliqueSize.boundedCliqueProperty_of_ultrafilterCompact

-- Section 3: the omega_1 example
#print axioms CliqueSize.OmegaOne.exists_boundedCliqueProperty_not_compactSpace
#print axioms CliqueSize.OmegaOne.exists_finiteOpenChromatic_not_compactSpace

-- Section 4: preservation, separable reflection, metacompactness, the witness profile
#print axioms CliqueSize.BoundedCliqueProperty.of_isClosed
#print axioms CliqueSize.BoundedCliqueProperty.image
#print axioms CliqueSize.separable_reflection
#print axioms CliqueSize.compactSpace_of_metacompact_of_countablyCompact
#print axioms CliqueSize.finiteCliqueProperty_iff_compactSpace_of_metacompact
#print axioms CliqueSize.witness_profile

-- Section 4: the beta-omega construction and the conditional witness
#print axioms CliqueSize.BetaOmega.mem_closure_betaR0_iff
#print axioms CliqueSize.BetaOmega.exists_free_ultrafilter_no_isPartialSection
#print axioms CliqueSize.BetaOmega.isOpen_goodSet
#print axioms CliqueSize.BetaOmega.mainQuestion_of_exists_countablyCompact_dense_subset_goodSet

-- Section 5: chromatic results and the sphere
#print axioms CliqueSize.encard_le_chiOp
#print axioms CliqueSize.finiteOpenChromatic_of_compact
#print axioms CliqueSize.boundedCliqueProperty_of_finiteOpenChromatic
#print axioms CliqueSize.mainQuestion_or_boundedCliqueProperty_iff_countablyCompact
#print axioms CliqueSize.sphere_clique_number
#print axioms CliqueSize.le_chiOp_sphereOrth
#print axioms CliqueSize.chiOp_sphereOrth_three_le
#print axioms CliqueSize.chiOp_sphereOrth_three_bounds
