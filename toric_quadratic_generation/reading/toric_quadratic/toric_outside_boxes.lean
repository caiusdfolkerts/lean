module

public import PaperVerification.ToricOutsideCorrections

@[expose] public section

/-!
# The original side-two boxes and the inner unit boxes

These are geometric containment statements in the original real polytope
and its actual topological interior. Every activated class and correction
used in their proofs is the exhaustive canonical construction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

theorem normal_basis_vertex_active («Σ» : SmoothCompleteFan n)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n))) (i : Fin n) :
    (dotProductEquiv ℝ (Fin n) (embed n (d i))) v = -(P.integralSupport (d i) : ℝ) := by
  have hnormal : embed n (d i) ∈ P.normalCone v := by
    rw [hcone]
    exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hh := (P.integralSupport_spec (d i) v hv).2.mpr hnormal
  linarith

/-- Proposition 5.2, with actual polytope containment and all activated
classes constructed in the proof. -/
theorem outside_side_two_box
    («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast n)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      Q.degree (fun w => (P.integralSupport w : ℝ)) < 2 * (Q.fiberDimension : ℝ) →
      ¬ Q.negative ⊆ Finset.univ.image d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 2) :
    v + ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ P.carrier := by
  apply P.corner_box_mem_of_vertices v _ 2 (by norm_num) ?_ t ht
  intro I
  let D := I.image d
  have hD : D ⊆ Finset.univ.image d := Finset.image_subset_image (Finset.subset_univ I)
  obtain ⟨Γ, F, hF, hrays, hΓd, hcoeff, hle⟩ :=
    «Σ».exists_outside_side_two_correction hpure P hP hfan hbound
      (Finset.univ.image d) D hd hD houtside
  have hmem := «Σ».box_corner_mem_of_refinement_nef Γ hrays
    (fun w => (P.integralSupport w : ℝ)) F hF d hΓd v
    (P.normal_basis_vertex_active «Σ» v hv d hcone) I 2
    (by
      intro i
      have hh := hcoeff (d i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hiD : d i ∈ D ↔ i ∈ I := by simp only [D, Finset.mem_image, d.injective.eq_iff]; simp
      simpa only [hiD] using hh)
    (by
      intro w hw
      have hh := hle w hw
      have hnonneg : 0 ≤ 2 * (if w ∈ D then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      linarith)
  rwa [P.fanPolytope_integralSupport_eq «Σ» hfan] at hmem

/-- Section 7.2's inner unit box lies in the actual topological interior,
not merely in a symbolic adjoint polytope. -/
theorem outside_inner_unit_box
    («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) (hbound : P.EdgesAtLeast (n + 1))
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (houtside : ∀ Q : «Σ».PrimitiveRelation, Q.IsCombinatoriallyContractible →
      0 < 2 * (Q.fiberDimension : ℝ) + 1 -
        Q.degree (fun w => (P.integralSupport w : ℝ)) - Q.negativeCoefficientSum →
      ¬ Q.negative ⊆ Finset.univ.image d)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    (v + ∑ i, integralBasisReal (integralDualBasis d) i) +
      ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ interior P.carrier := by
  let a : Lattice n → ℝ := fun w => (P.integralSupport w : ℝ)
  let a' : Lattice n → ℝ := fun w => a w - 1
  let v' := v + ∑ i, integralBasisReal (integralDualBasis d) i
  have hv' (i : Fin n) :
      (dotProductEquiv ℝ (Fin n) (embed n (d i))) v' = -a' (d i) := by
    rw [show v' = v + ∑ j, integralBasisReal (integralDualBasis d) j from rfl,
      map_add, map_sum, P.normal_basis_vertex_active «Σ» v hv d hcone i]
    simp only [normal_basis_dual_pairing, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp only [a', a]
    ring
  have hvertices (I : Finset (Fin n)) :
      v' + (1 : ℝ) • (∑ i ∈ I, integralBasisReal (integralDualBasis d) i) ∈
        «Σ».fanPolytope a' := by
    let D := I.image d
    have hD : D ⊆ Finset.univ.image d := Finset.image_subset_image (Finset.subset_univ I)
    obtain ⟨Γ, F, hF, hrays, hΓd, hcoeff, hle⟩ :=
      «Σ».exists_outside_inner_unit_correction hpure P hP hfan hbound
        (Finset.univ.image d) D hd hD houtside
    apply «Σ».box_corner_mem_of_refinement_nef Γ hrays a' F hF d hΓd v' hv' I 1
    · intro i
      have hh := hcoeff (d i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have hiD : d i ∈ D ↔ i ∈ I := by simp only [D, Finset.mem_image, d.injective.eq_iff]; simp
      simpa only [a', a, hiD, one_mul] using hh
    · intro w hw
      have hh := hle w hw
      have hnonneg : 0 ≤ (if w ∈ D then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      change F w ≤ (P.integralSupport w : ℝ) - 1
      linarith
  have hbox := «Σ».box_mem_fanPolytope_of_vertices a' v' _ 1 zero_le_one hvertices t ht
  have hinterior := «Σ».fanPolytope_sub_pos_subset_interior a 1 zero_lt_one hbox
  rwa [P.fanPolytope_integralSupport_eq «Σ» hfan] at hinterior

/-- All ordinary unit boxes are contained under the original edge bound,
with the exact basis from any full normal cone. -/
theorem unit_box_of_edge_bound
    («Σ» : SmoothCompleteFan n) (hpure : «Σ».IsPure) (hP : P.Smooth)
    (hfan : «Σ».realCones = P.normalFan) {bound : ℕ}
    (hbound : P.EdgesAtLeast bound) (hn : n ≤ bound)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hd : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    v + ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ P.carrier := by
  apply P.corner_box_of_contractible_degrees «Σ» hpure hfan v hv d hd hcone 1 zero_le_one ?_ t ht
  intro Q hQ
  have hdQ := P.contractible_degree_lower_bound hP «Σ» hpure hfan hbound Q hQ
  have hdim := Q.contractible_dimension_bound hQ
  have hr : Q.fiberDimension ≤ bound := by omega
  have hrR : (Q.fiberDimension : ℝ) ≤ bound := by exact_mod_cast hr
  simpa only [one_mul] using hrR.trans hdQ

end LatticePolytope

end PaperVerification.ToricGeometry
