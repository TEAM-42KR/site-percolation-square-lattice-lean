import SitePerc.Foundations
import SitePerc.Geometry
import SitePerc.Substitution

/-!
# Conditional assembly of the square-lattice site bound

This is the proved theory bridge, not the final unconditional finite calculation.
The two concrete boundary-law dominations are explicit unresolved computation
obligations. They are not among the four permitted classical inputs and must
be discharged before the final theorem can be claimed.
-/

namespace SitePerc

/-- The exact two finite comparisons required by the two-stage substitution. -/
structure TwoStageBoundaryDominations : Prop where
  stage1 : boundaryDominates 6 (0, 0) lineLattice intermediate q0 p1
  stage2 : boundaryDominates 6 (3, 3) intermediate square p1 p2

/-- General-theory closure with concrete D1/D2 still exposed. -/
theorem site_upper_of_boundary_domination (kesten : KestenAboveHalf)
    (finite : TwoStageBoundaryDominations) : pcSite ≤ (79 / 125 : ℝ) := by
  have hq : (1 / 2 : ℝ) < q0.val := by norm_num [q0]
  have hL : 0 < infiniteProbability lineLattice q0 := by
    rw [← line_graph_equivalence q0]
    exact kesten q0 hq
  have h1 : infiniteProbability lineLattice q0 ≤ infiniteProbability intermediate p1 :=
    substitution_exists 6 (by norm_num) (0, 0) lineLattice intermediate q0 p1
      stage1_geometry finite.stage1
  have h2 : infiniteProbability intermediate p1 ≤ infiniteProbability square p2 :=
    substitution_exists 6 (by norm_num) (3, 3) intermediate square p1 p2
      stage2_geometry finite.stage2
  have hp : 0 < infiniteProbability square p2 :=
    lt_of_lt_of_le (lt_of_lt_of_le hL h1) h2
  have htheta := square_exists_to_origin p2 hp
  simpa only [p2] using pc_le_of_theta p2 htheta

#print axioms site_upper_of_boundary_domination

end SitePerc
