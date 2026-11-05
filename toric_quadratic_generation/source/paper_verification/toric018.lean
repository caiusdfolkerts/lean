module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.Basic
public import paper_verification.toric002
public import paper_verification.toric017

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricStarDualBasis
section Source_ToricStarDualBasis

-- original header: module
-- original header: public import PaperVerification.ToricDualNormalCone
-- original header: public import PaperVerification.ToricStarBoxCoordinates
-- original header: @[expose] public section
/-!
# The dual ray basis of a smooth star subdivision

Replacing a pivot normal by the sum of the selected normals gives a genuine
integral basis. It is exactly dual to the primal shear in equation (10).
The inverse coordinate formulas are proved in the actual module.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section RayBasis

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [DecidableEq ι]

def starRayVector (b : Module.Basis ι R E) (I : Finset ι) (j : ι) : E :=
  ∑ i ∈ I.erase j, b i

theorem starRayVector_coord (b : Module.Basis ι R E)
    (I : Finset ι) (j i : ι) :
    b.coord i (starRayVector b I j) = if i ∈ I.erase j then 1 else 0 := by
  simp [starRayVector, map_sum, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    Finsupp.single_apply]

theorem starRayVector_coord_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) : b.coord j (starRayVector b I j) = 0 := by
  rw [starRayVector_coord]
  simp

/-- The basis replacing the pivot by the sum of the selected rays. -/
def starRayBasis (b : Module.Basis ι R E) (I : Finset ι) (j : ι) :
    Module.Basis ι R E :=
  b.map (LinearEquiv.transvection (starRayVector_coord_pivot b I j))

theorem starRayBasis_apply (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) :
    starRayBasis b I j k =
      if k = j then b j + starRayVector b I j else b k := by
  rw [starRayBasis, Module.Basis.map_apply, LinearEquiv.transvection.apply]
  by_cases hkj : k = j
  · subst k
    simp [Module.Basis.coord_apply]
  · simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hkj]

theorem starRayBasis_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (hj : j ∈ I) :
    starRayBasis b I j j = ∑ i ∈ I, b i := by
  rw [starRayBasis_apply, if_pos rfl]
  exact Finset.add_sum_erase I b hj

theorem starRayBasis_other (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) (hkj : k ≠ j) :
    starRayBasis b I j k = b k := by
  rw [starRayBasis_apply, if_neg hkj]

/-- Exact inverse coordinates: the pivot coefficient is unchanged; each
other selected coefficient loses the pivot coefficient. -/
theorem starRayBasis_coord (b : Module.Basis ι R E)
    (I : Finset ι) (j i : ι) (x : E) :
    (starRayBasis b I j).coord i x =
      if i ∈ I.erase j then b.coord i x - b.coord j x else b.coord i x := by
  change b.coord i
    ((LinearEquiv.transvection (starRayVector_coord_pivot b I j)).symm x) = _
  have hneg : b.coord j (-starRayVector b I j) = 0 := by
    rw [map_neg, starRayVector_coord_pivot, neg_zero]
  rw [LinearEquiv.transvection.symm_eq (starRayVector_coord_pivot b I j) hneg,
    LinearEquiv.transvection.apply,
    map_add, map_smul, map_neg, starRayVector_coord, smul_eq_mul]
  split_ifs <;> ring

theorem starRayBasis_coord_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (x : E) :
    (starRayBasis b I j).coord j x = b.coord j x := by
  rw [starRayBasis_coord]
  simp

/-- The sheared primal pivot coordinate is the sum of the old selected
coordinates. This is the dual version of the new exceptional ray. -/
theorem starShearBasis_coord_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (hj : j ∈ I) (x : E) :
    (starShearBasis b I j).coord j x = ∑ i ∈ I, b.coord i x := by
  let c := starShearBasis b I j
  let a : ι → R := fun k => c.repr x k
  have hsum : (∑ k, a k • starShearBasis b I j k) = x := c.sum_repr x
  have h := sum_normal_coords_shifted_star_box b I j hj (0 : R) a
  simpa only [zero_smul, zero_add, hsum, a, Module.Basis.coord_apply] using h.symm

theorem starShearBasis_coord_other (b : Module.Basis ι R E)
    (I : Finset ι) (j i : ι) (hij : i ≠ j) (x : E) :
    (starShearBasis b I j).coord i x = b.coord i x := by
  let c := starShearBasis b I j
  let a : ι → R := fun k => c.repr x k
  have hsum : (∑ k, a k • starShearBasis b I j k) = x := c.sum_repr x
  have h := coord_shifted_star_box b I j i (0 : R) a
  simpa only [zero_smul, zero_add, hsum, if_neg hij, add_zero,
    a, Module.Basis.coord_apply] using h.symm

end RayBasis

/-- Taking the genuine coordinate-pairing dual twice recovers the original
integral basis, not merely a basis with the same rays. -/
@[simp] theorem integralDualBasis_involutive {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    integralDualBasis (integralDualBasis b) = b := by
  apply DFunLike.ext
  intro i
  apply (dotProductEquiv ℤ (Fin n)).injective
  apply LinearMap.ext
  intro z
  change (∑ k, integralDualBasis (integralDualBasis b) i k * z k) =
    ∑ k, b i k * z k
  rw [integralDualBasis_pairing, integralDualBasis_repr]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- The normal-ray replacement is exactly dual to the primal star-chart
shear. The equality includes every tangent vector. -/
theorem integralDualBasis_starShearBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I) :
    integralDualBasis (starShearBasis b I j) =
      starRayBasis (integralDualBasis b) I j := by
  apply DFunLike.ext
  intro i
  apply (dotProductEquiv ℤ (Fin n)).injective
  apply LinearMap.ext
  intro z
  change (∑ k, integralDualBasis (starShearBasis b I j) i k * z k) =
    (∑ k, starRayBasis (integralDualBasis b) I j i k * z k)
  rw [integralDualBasis_pairing]
  change (starShearBasis b I j).coord i z = _
  by_cases hij : i = j
  · subst i
    rw [starShearBasis_coord_pivot b I j hj z,
      starRayBasis_pivot (integralDualBasis b) I j hj]
    have hpair : (∑ k, (∑ i ∈ I, integralDualBasis b i) k * z k) =
        ∑ i ∈ I, b.coord i z := by
      let f : Lattice n →ₗ[ℤ] ℤ := dotProductEquiv ℤ (Fin n) z
      have h := map_sum f (fun i => integralDualBasis b i) I
      have hi (i : Fin n) : f (integralDualBasis b i) = b.coord i z := by
        change (z ⬝ᵥ integralDualBasis b i) = _
        rw [dotProduct_comm]
        exact integralDualBasis_pairing b i z
      change z ⬝ᵥ (∑ i ∈ I, integralDualBasis b i) =
        ∑ i ∈ I, f (integralDualBasis b i) at h
      rw [dotProduct_comm] at h
      simpa only [dotProduct, hi] using h
    exact hpair.symm
  · rw [starShearBasis_coord_other b I j i hij z,
      starRayBasis_other (integralDualBasis b) I j i hij,
      integralDualBasis_pairing]
    rfl

/-- The real extension of the ray replacement uses the same actual vectors
as the integral replacement. -/
theorem integralBasisReal_starRayBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) :
    integralBasisReal (starRayBasis b I j) =
      starRayBasis (integralBasisReal b) I j := by
  apply DFunLike.ext
  intro k
  rw [integralBasisReal_apply, starRayBasis_apply, starRayBasis_apply]
  split_ifs
  · simp only [map_add, starRayVector, map_sum, integralBasisReal_apply]
  · exact (integralBasisReal_apply b k).symm

end PaperVerification.ToricGeometry

end
end Source_ToricStarDualBasis
-- END ORIGINAL PaperVerification.ToricStarDualBasis


-- BEGIN ORIGINAL PaperVerification.ToricCornerCriterion
section Source_ToricCornerCriterion

-- original header: module

-- original header: public import PaperVerification.ToricExtremalCriterion
-- original header: public import PaperVerification.ToricPolytopeSupport
-- original header: public import PaperVerification.ToricStarDualBasis

-- original header: @[expose] public section

/-!
# Genuine corner boxes from contractible degree bounds

The support coefficients are the actual minima of the given lattice
polytope. Nefness of each selected normal-ray subtraction produces the
corresponding geometric corner vertex. Linear minimization over a box then
gives the whole closed box, with its original real coordinates.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Actual primitive normal-ray inequalities characterize the original
polytope. No replacement halfspace polytope is introduced. -/
theorem mem_carrier_iff_normal_ray_inequalities («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan) (x : Ambient n) :
    x ∈ P.carrier ↔ ∀ u ∈ «Σ».rays,
      -(dotProductEquiv ℝ (Fin n) (embed n u)) x ≤ (P.integralSupport u : ℝ) := by
  constructor
  · intro hx u hu
    exact (P.integralSupport_spec u x hx).1
  · intro hx
    let J := P.carrier.extremePoints ℝ
    letI : Fintype J := P.finite_vertices.fintype
    have hvertices : Set.range (fun j : J => (j : Ambient n)) =
        P.carrier.extremePoints ℝ := by simp [J]
    rw [← P.hull_vertices, ← hvertices]
    apply mem_finite_convexHull_of_lower_support
    intro f
    obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
    have hvfan : P.normalCone v ∈ «Σ».realCones := by
      rw [hfan]
      exact ⟨v, hv.1, rfl⟩
    obtain ⟨s, hs, hscone⟩ := hvfan
    obtain ⟨b, I, hI⟩ := «Σ».smooth s hs
    have hfcone : dualVector f ∈ latticeRayCone (I.image b) := by
      rw [← hI]
      change dualVector f ∈ (latticeRayCone s : Set (Ambient n))
      rw [← hscone]
      exact (P.dualVector_mem_normalCone_iff f v).mpr hmin
    obtain ⟨hcpos, hczero⟩ :=
      (mem_latticeRayCone_basis_iff b I (dualVector f)).mp hfcone
    let g : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (x - v)
    have hg (i : Fin n) (hi : i ∈ I) : 0 ≤ g (integralBasisReal b i) := by
      have hbi : b i ∈ s := hI.symm ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
      have hbiray := «Σ».ray_mem_of_mem_cone hs hbi
      have hbinormal : embed n (b i) ∈ P.normalCone v := by
        rw [hscone]
        exact latticeRayCone_generator s hbi
      have he := (P.integralSupport_spec (b i) v hv.1).2.mpr hbinormal
      have hle := hx (b i) hbiray
      rw [← he] at hle
      have hsub : 0 ≤ (dotProductEquiv ℝ (Fin n) (embed n (b i))) (x - v) := by
        rw [map_sub]
        linarith
      change 0 ≤ (embed n (b i)) ⬝ᵥ (x - v) at hsub
      change 0 ≤ (x - v) ⬝ᵥ integralBasisReal b i
      rw [integralBasisReal_apply, dotProduct_comm]
      exact hsub
    have hnonneg : 0 ≤ g (dualVector f) := by
      rw [← (integralBasisReal b).sum_repr (dualVector f)]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_nonneg
      intro i hi
      by_cases hiI : i ∈ I
      · exact mul_nonneg (hcpos i) (hg i hiI)
      · rw [hczero i hiI, zero_mul]
    have he : g (dualVector f) = f (x - v) := by
      change ((x - v) ⬝ᵥ dualVector f) = _
      rw [dotProduct_comm]
      exact dualVector_pairing f v x
    rw [he, map_sub, sub_nonneg] at hnonneg
    exact ⟨⟨v, hv⟩, hnonneg⟩

/-- The dual of a full integral normal basis has the exact Kronecker
pairing with the original primitive normals. -/
theorem normal_basis_dual_pairing
    (d : Module.Basis (Fin n) ℤ (Lattice n)) (i j : Fin n) :
    (dotProductEquiv ℝ (Fin n) (embed n (d i)))
      (integralBasisReal (integralDualBasis d) j) = if j = i then 1 else 0 := by
  change (∑ k, embed n (d i) k * integralBasisReal (integralDualBasis d) j k) =
    if j = i then 1 else 0
  have h := integralDualBasis_real_pairing d j (integralBasisReal d i)
  rw [Module.Basis.repr_self_apply] at h
  simpa only [integralBasisReal_apply, mul_comm, eq_comm] using h

/-- Subtracting selected cone-ray coefficients moves the actual Cartier
vertex by the selected primitive tangent vectors. Genuine nefness puts
that shifted vertex back in the original polytope. -/
theorem corner_vertex_mem_of_nef («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hs : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (I : Finset (Fin n)) (side : ℝ) (hside : 0 ≤ side)
    (hnef : «Σ».IsNef ((fun u => (P.integralSupport u : ℝ)) -
      side • (fun u => if u ∈ I.image d then 1 else 0))) :
    v + side • (∑ i ∈ I, integralBasisReal (integralDualBasis d) i) ∈ P.carrier := by
  let c := v + side • (∑ i ∈ I, integralBasisReal (integralDualBasis d) i)
  obtain ⟨ℓ, he, hle⟩ := hnef (Finset.univ.image d) hs
  let q : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) c)
  have hpair (u : Lattice n) :
      q (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) c := by
    simp only [q, LinearMap.neg_apply]
    congr 1
    exact dotProduct_comm c (embed n u)
  have hℓq : ℓ = q := by
    apply (integralBasisReal d).ext
    intro i
    rw [integralBasisReal_apply, he (d i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩), hpair]
    have hnormal : embed n (d i) ∈ P.normalCone v := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hsupport := (P.integralSupport_spec (d i) v hv).2.mpr hnormal
    have hmem : d i ∈ I.image d ↔ i ∈ I := by
      simp only [Finset.mem_image, d.injective.eq_iff]
      simp
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hmem, c,
      map_add, map_smul, map_sum, normal_basis_dual_pairing,
      Finset.sum_ite_eq', neg_add_rev]
    rw [← hsupport]
    split_ifs <;> ring
  apply (P.mem_carrier_iff_normal_ray_inequalities «Σ» hfan c).mpr
  intro u hu
  have h := hle u hu
  rw [hℓq, hpair] at h
  change -(dotProductEquiv ℝ (Fin n) (embed n u)) c ≤
    (P.integralSupport u : ℝ) - side * (if u ∈ I.image d then 1 else 0) at h
  have hm : 0 ≤ side * (if u ∈ I.image d then (1 : ℝ) else 0) := by
    split_ifs <;> positivity
  linarith

/-- If every corner vertex belongs to a convex polytope, every point of
the full real box belongs to it. The proof minimizes each linear form
coordinate by coordinate, including coordinates where the form vanishes. -/
theorem corner_box_mem_of_vertices (v : Ambient n) (b : Fin n → Ambient n)
    (side : ℝ) (hside : 0 ≤ side)
    (hvertices : ∀ I : Finset (Fin n), v + side • (∑ i ∈ I, b i) ∈ P.carrier)
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    v + ∑ i, t i • b i ∈ P.carrier := by
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  have hrange : Set.range (fun j : J => (j : Ambient n)) =
      P.carrier.extremePoints ℝ := by simp [J]
  rw [← P.hull_vertices, ← hrange]
  apply mem_finite_convexHull_of_lower_support
  intro f
  let I := Finset.univ.filter (fun i => f (b i) < 0)
  obtain ⟨w, hw, hmin⟩ := P.exists_minimizing_vertex f
  refine ⟨⟨w, hw⟩, (hmin _ (hvertices I)).trans ?_⟩
  simp only [map_add, map_smul, map_sum, smul_eq_mul]
  refine add_le_add le_rfl ?_
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ I, side * f (b i)) =
        ∑ i, if i ∈ I then side * f (b i) else 0 := by simp
    _ ≤ ∑ i, t i * f (b i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiI : i ∈ I
      · rw [if_pos hiI]
        have hneg : f (b i) ≤ 0 := (Finset.mem_filter.mp hiI).2.le
        exact mul_le_mul_of_nonpos_right (ht i).2 hneg
      · rw [if_neg hiI]
        have hnonneg : 0 ≤ f (b i) := by
          simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and,
            not_lt] using hiI
        exact mul_nonneg (ht i).1 hnonneg

/-- The full numerical corner-box criterion, with genuine support degrees,
genuine contractible primitive relations, and the original real polytope. -/
theorem corner_box_of_contractible_degrees («Σ» : SmoothCompleteFan n)
    (hpure : «Σ».IsPure) (hfan : «Σ».realCones = P.normalFan)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hs : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      side * R.fiberDimension ≤ R.degree (fun u => (P.integralSupport u : ℝ)))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ side) :
    v + ∑ i, t i • integralBasisReal (integralDualBasis d) i ∈ P.carrier := by
  apply P.corner_box_mem_of_vertices v _ side hside ?_ t ht
  intro I
  apply P.corner_vertex_mem_of_nef «Σ» hfan v hv d hs hcone I side hside
  exact «Σ».nef_sub_cone_selection_of_contractible_degrees hpure P.integralSupport
    (P.integralSupport_isStrictSupport «Σ» hfan) _ side hside hdegree hs
    (Finset.image_subset_image (Finset.subset_univ I))

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricCornerCriterion
-- END ORIGINAL PaperVerification.ToricCornerCriterion


-- BEGIN ORIGINAL PaperVerification.ToricFiniteSupportPerturbation
section Source_ToricFiniteSupportPerturbation

-- original header: module
-- original header: public import PaperVerification.ToricNefCone
-- original header: public import Mathlib.Data.Finset.Max
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# Finite strict support perturbations

All choices of a sufficiently small positive real number are reduced here
to minima of finitely many positive explicit ratios. The later subdivision
argument therefore does not assume that strict inequalities survive a
perturbation without proving a common parameter works for every cone.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Finitely many strict affine inequalities hold simultaneously after a
sufficiently small positive perturbation. -/
theorem finite_strict_perturbation_all_small {ι : Type*} (I : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ I, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ i ∈ I, 0 < f i + ε * g i := by
  by_cases hI : I.Nonempty
  · obtain ⟨j, hj, hmin⟩ := I.exists_min_image (fun i => f i / (|g i| + 1)) hI
    let δ := f j / (|g j| + 1)
    have hδ : 0 < δ := div_pos (hf j hj) (by have h := abs_nonneg (g j); linarith)
    refine ⟨δ, hδ, ?_⟩
    intro ε hε hεδ i hi
    have hden : 0 < |g i| + 1 := by have h := abs_nonneg (g i); linarith
    have hδbound : δ * (|g i| + 1) ≤ f i :=
      (le_div_iff₀ hden).mp (hmin i hi)
    have hbound : ε * (|g i| + 1) ≤ f i :=
      (mul_le_mul_of_nonneg_right hεδ hden.le).trans hδbound
    have hg : 0 ≤ g i + |g i| := by have h := neg_abs_le (g i); linarith
    have hprod := mul_nonneg hε.le hg
    nlinarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε hεδ i hi
    exact (hI ⟨i, hi⟩).elim

theorem finite_strict_perturbation {ι : Type*} (I : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ I, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ I, 0 < f i + ε * g i := by
  obtain ⟨δ, hδ, hsmall⟩ := finite_strict_perturbation_all_small I f g hf
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

/-- A finite family of supporting linear forms with lexicographically
positive inactive slacks admits one common positive perturbation parameter. -/
theorem finite_lexicographic_support_perturbation_all_small {n : ℕ}
    (C : Finset (Finset (Lattice n))) (R : Finset (Lattice n))
    (a₀ a₁ : Lattice n → ℝ)
    (L₀ L₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ s ∈ C, ∀ v ∈ s,
      L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) = a₁ v)
    (hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      L₀ s (embed n v) < a₀ v ∨
      (L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) < a₁ v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ s ∈ C,
      (∀ v ∈ s, (L₀ s + ε • L₁ s) (embed n v) = a₀ v + ε * a₁ v) ∧
      (∀ v ∈ R, v ∉ s →
        (L₀ s + ε • L₁ s) (embed n v) < a₀ v + ε * a₁ v) := by
  let I := (C.product R).filter (fun p => p.2 ∉ p.1 ∧ L₀ p.1 (embed n p.2) < a₀ p.2)
  let f : Finset (Lattice n) × Lattice n → ℝ :=
    fun p => a₀ p.2 - L₀ p.1 (embed n p.2)
  let g : Finset (Lattice n) × Lattice n → ℝ :=
    fun p => a₁ p.2 - L₁ p.1 (embed n p.2)
  have hf : ∀ p ∈ I, 0 < f p := by
    intro p hp
    exact sub_pos.mpr (Finset.mem_filter.mp hp).2.2
  obtain ⟨δ, hδ, hpert⟩ := finite_strict_perturbation_all_small I f g hf
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ s hs
  constructor
  · intro v hv
    obtain ⟨h₀, h₁⟩ := heq s hs v hv
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₀, h₁]
  · intro v hv hvs
    rcases hlex s hs v hv hvs with h₀ | ⟨h₀, h₁⟩
    · have hmem : (s, v) ∈ I := Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs, hv⟩, hvs, h₀⟩
      have h := hpert ε hε hεδ (s, v) hmem
      change 0 < (a₀ v - L₀ s (embed n v)) + ε * (a₁ v - L₁ s (embed n v)) at h
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      nlinarith
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₀]
      exact add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left h₁ hε)

theorem finite_lexicographic_support_perturbation {n : ℕ}
    (C : Finset (Finset (Lattice n))) (R : Finset (Lattice n))
    (a₀ a₁ : Lattice n → ℝ)
    (L₀ L₁ : Finset (Lattice n) → Ambient n →ₗ[ℝ] ℝ)
    (heq : ∀ s ∈ C, ∀ v ∈ s,
      L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) = a₁ v)
    (hlex : ∀ s ∈ C, ∀ v ∈ R, v ∉ s →
      L₀ s (embed n v) < a₀ v ∨
      (L₀ s (embed n v) = a₀ v ∧ L₁ s (embed n v) < a₁ v)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ C,
      (∀ v ∈ s, (L₀ s + ε • L₁ s) (embed n v) = a₀ v + ε * a₁ v) ∧
      (∀ v ∈ R, v ∉ s →
        (L₀ s + ε • L₁ s) (embed n v) < a₀ v + ε * a₁ v) := by
  obtain ⟨δ, hδ, hsmall⟩ := finite_lexicographic_support_perturbation_all_small
    C R a₀ a₁ L₀ L₁ heq hlex
  exact ⟨δ, hδ, hsmall δ hδ le_rfl⟩

end PaperVerification.ToricGeometry
end
end Source_ToricFiniteSupportPerturbation
-- END ORIGINAL PaperVerification.ToricFiniteSupportPerturbation


-- BEGIN ORIGINAL PaperVerification.ToricFanPolytopes
section Source_ToricFanPolytopes

-- original header: module

-- original header: public import PaperVerification.ToricCornerCriterion
-- original header: public import PaperVerification.ToricFiniteSupportPerturbation
-- original header: public import Mathlib.Analysis.Convex.Intrinsic

-- original header: @[expose] public section

/-!
# Actual polytopes of nef support functions

The halfspaces are the literal primitive-ray inequalities. Their Cartier
points are explicit dual-basis sums. Completeness of the actual fan proves
the convex-hull description, including lower-dimensional nef polytopes.
Minkowski addition is then proved for the same actual subsets.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def fullCones : Finset (Finset (Lattice n)) :=
  «Σ».cones.filter (fun s => s.card = n)

theorem fullCones_mem (s : «Σ».fullCones) : (s : Finset (Lattice n)) ∈ «Σ».cones :=
  (Finset.mem_filter.mp s.property).1

theorem fullCones_card (s : «Σ».fullCones) : (s : Finset (Lattice n)).card = n :=
  (Finset.mem_filter.mp s.property).2

def fullConeBasis (s : «Σ».fullCones) : Module.Basis (Fin n) ℤ (Lattice n) :=
  Classical.choose («Σ».full_cone_basis («Σ».fullCones_mem s) («Σ».fullCones_card s))

theorem fullConeBasis_ray_set (s : «Σ».fullCones) :
    (s : Finset (Lattice n)) = Finset.univ.image («Σ».fullConeBasis s) :=
  Classical.choose_spec («Σ».full_cone_basis («Σ».fullCones_mem s) («Σ».fullCones_card s))

/-- The ordinary closed polytope cut out by all primitive-ray support
inequalities, with no nefness built into its definition. -/
def fanPolytope (a : Lattice n → ℝ) : Set (Ambient n) :=
  {x | ∀ u ∈ «Σ».rays, -a u ≤ (dotProductEquiv ℝ (Fin n) (embed n u)) x}

theorem fanPolytope_eq_normalHalfspaces (a : Lattice n → ℝ) :
    «Σ».fanPolytope a = normalHalfspaces
      (fun u : «Σ».rays => dotProductEquiv ℝ (Fin n) (embed n u))
      (fun u : «Σ».rays => -a u) := by
  ext x
  exact ⟨fun h u => h u u.property, fun h u hu => h ⟨u, hu⟩⟩

theorem convex_fanPolytope (a : Lattice n → ℝ) : Convex ℝ («Σ».fanPolytope a) := by
  rw [«Σ».fanPolytope_eq_normalHalfspaces]
  exact convex_normalHalfspaces _ _

/-- The Cartier point is the explicit dual-basis solution of all active
primitive support equalities. -/
def cartierPoint (a : Lattice n → ℝ) (s : «Σ».fullCones) : Ambient n :=
  -∑ i, a («Σ».fullConeBasis s i) •
    integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) i

def cartierBasis (s : «Σ».fullCones) : Module.Basis (Fin n) ℝ (Ambient n) :=
  integralBasisReal (integralDualBasis («Σ».fullConeBasis s))

def activeRay (s : «Σ».fullCones) (i : Fin n) : «Σ».rays :=
  ⟨«Σ».fullConeBasis s i, «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s)
    ((«Σ».fullConeBasis_ray_set s).symm ▸ Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩)⟩

theorem activeRay_dual (s : «Σ».fullCones) (i : Fin n) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i))) x =
      («Σ».cartierBasis s).repr x i := by
  have h := integralDualBasis_real_pairing (integralDualBasis («Σ».fullConeBasis s)) i x
  change (∑ j, embed n («Σ».fullConeBasis s i) j * x j) =
    («Σ».cartierBasis s).repr x i
  simpa only [integralDualBasis_involutive, cartierBasis] using h

theorem cartierPoint_active (a : Lattice n → ℝ) (s : «Σ».fullCones) (i : Fin n) :
    (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i))) («Σ».cartierPoint a s) =
      -a («Σ».activeRay s i) := by
  rw [«Σ».activeRay_dual]
  simp [cartierPoint, cartierBasis, activeRay, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.repr_self_apply,
    Finsupp.single_apply, smul_eq_mul]

/-- Completeness gives a vertex basis on which any real linear form is
nonnegative. This is a property of the original fan, not an extra support
function hypothesis. -/
theorem exists_cartierBasis_nonnegative (hpure : «Σ».IsPure)
    (f : Ambient n →ₗ[ℝ] ℝ) : ∃ s : «Σ».fullCones, ∀ i, 0 ≤ f («Σ».cartierBasis s i) := by
  obtain ⟨t, ht, hft⟩ := «Σ».complete (dualVector f)
  obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
  let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
  have hfs : dualVector f ∈ latticeRayCone s := latticeRayCone_mono hts hft
  rw [show s = Finset.univ.image («Σ».fullConeBasis s') from
    «Σ».fullConeBasis_ray_set s'] at hfs
  have hcoords := ((mem_latticeRayCone_basis_iff («Σ».fullConeBasis s')
    Finset.univ (dualVector f)).mp hfs).1
  refine ⟨s', ?_⟩
  intro i
  have hp := integralDualBasis_real_repr (integralDualBasis («Σ».fullConeBasis s'))
    (dualVector f) i
  rw [integralDualBasis_involutive] at hp
  have hf : (∑ j, dualVector f j * «Σ».cartierBasis s' i j) = f («Σ».cartierBasis s' i) := by
    simpa only [Pi.zero_apply, sub_zero, sub_zero] using
      dualVector_pairing f (0 : Ambient n) («Σ».cartierBasis s' i)
  have hi := hcoords i
  rw [hp, show integralBasisReal (integralDualBasis («Σ».fullConeBasis s')) i =
      «Σ».cartierBasis s' i from rfl, hf] at hi
  exact hi

/-- Genuine nefness places each actual Cartier point in every ray
halfspace. -/
theorem cartierPoint_mem_of_nef {a : Lattice n → ℝ} (ha : «Σ».IsNef a)
    (s : «Σ».fullCones) : «Σ».cartierPoint a s ∈ «Σ».fanPolytope a := by
  obtain ⟨ℓ, he, hle⟩ := ha s («Σ».fullCones_mem s)
  let q : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) («Σ».cartierPoint a s))
  have hq (u : Lattice n) :
      q (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
    change -(«Σ».cartierPoint a s ⬝ᵥ embed n u) =
      -(embed n u ⬝ᵥ «Σ».cartierPoint a s)
    rw [dotProduct_comm]
  have hℓq : ℓ = q := by
    apply (integralBasisReal («Σ».fullConeBasis s)).ext
    intro i
    rw [integralBasisReal_apply, he _
      ((«Σ».fullConeBasis_ray_set s).symm ▸ Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩), hq]
    have h := «Σ».cartierPoint_active a s i
    change (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s i)))
      («Σ».cartierPoint a s) = -a («Σ».fullConeBasis s i) at h
    rw [h, neg_neg]
  intro u hu
  have h := hle u hu
  rw [hℓq, hq] at h
  linarith

/-- The exact nef polytope/Cartier-point dictionary, with no dimension
assumption on the resulting polytope. -/
theorem fanPolytope_eq_convexHull_cartier (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    «Σ».fanPolytope a = convexHull ℝ (Set.range («Σ».cartierPoint a)) := by
  rw [«Σ».fanPolytope_eq_normalHalfspaces]
  apply shifted_halfspaces_eq_convexHull _ _ («Σ».cartierBasis) («Σ».activeRay)
    («Σ».cartierPoint a)
  · exact «Σ».activeRay_dual
  · exact «Σ».exists_cartierBasis_nonnegative hpure
  · exact «Σ».cartierPoint_active a
  · intro s
    rw [← «Σ».fanPolytope_eq_normalHalfspaces]
    exact «Σ».cartierPoint_mem_of_nef ha s

theorem cartierPoint_add (a b : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (a + b) s = «Σ».cartierPoint a s + «Σ».cartierPoint b s := by
  simp only [cartierPoint, Pi.add_apply, add_smul, Finset.sum_add_distrib, neg_add]

/-- The Minkowski identity for all genuine nef support functions,
including those whose polytopes have smaller affine dimension. -/
theorem fanPolytope_add (hpure : «Σ».IsPure)
    (a b : Lattice n → ℝ) (ha : «Σ».IsNef a) (hb : «Σ».IsNef b) :
    «Σ».fanPolytope (a + b) = «Σ».fanPolytope a + «Σ».fanPolytope b := by
  apply Set.Subset.antisymm
  · rw [«Σ».fanPolytope_eq_convexHull_cartier hpure (a + b) (IsNef.add «Σ» ha hb)]
    apply convexHull_min
    · rintro _ ⟨s, rfl⟩
      rw [«Σ».cartierPoint_add]
      exact Set.add_mem_add («Σ».cartierPoint_mem_of_nef ha s) («Σ».cartierPoint_mem_of_nef hb s)
    · exact («Σ».convex_fanPolytope a).add («Σ».convex_fanPolytope b)
  · rintro x ⟨y, hy, z, hz, rfl⟩ u hu
    have hyu := hy u hu
    have hzu := hz u hu
    change -(a u + b u) ≤ _
    rw [map_add]
    linarith

/-- Nef support plus a positive strictly convex support has strict support
on every actual cone. -/
theorem isStrictSupport_add_of_nef {a b : Lattice n → ℝ}
    (ha : «Σ».IsNef a) (hb : «Σ».IsStrictSupport b) : «Σ».IsStrictSupport (a + b) := by
  intro s hs
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  obtain ⟨k, ke, klt⟩ := hb s hs
  refine ⟨ℓ + k, ?_, ?_⟩
  · intro u hu
    simp only [LinearMap.add_apply, Pi.add_apply, he u hu, ke u hu]
  · intro u hu hus
    exact add_lt_add_of_le_of_lt (hle u hu) (klt u hu hus)

/-- Strict positivity on actual extremal primitive rays gives strict
support. A finite positive perturbation reduces it to the proved nef
criterion; strict support is not defined by those ray inequalities. -/
theorem isStrictSupport_of_extremal_primitive_pos (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ)
    (ha : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → 0 < R.degree a) :
    «Σ».IsStrictSupport a := by
  let I := Finset.univ.filter (fun Q : «Σ».primitiveCollections =>
    («Σ».canonicalPrimitive Q).IsExtremal)
  let f := fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).degree a
  let g := fun Q : «Σ».primitiveCollections =>
    -(«Σ».canonicalPrimitive Q).degree (fun u => (H u : ℝ))
  obtain ⟨ε, hε, hsmall⟩ := finite_strict_perturbation I f g
    (fun Q hQ => ha _ (Finset.mem_filter.mp hQ).2)
  have hnef : «Σ».IsNef (a - ε • (fun u => (H u : ℝ))) := by
    apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
    intro R hR
    obtain ⟨Q, hQ'⟩ := «Σ».exists_canonicalPrimitive_vector R
    have hQ := hQ'.symm
    have hcanon : («Σ».canonicalPrimitive Q).IsExtremal := by
      change (PointedCone.hull ℝ {(«Σ».canonicalPrimitive Q).vector}).IsFaceOf «Σ».effectiveCone
      rw [hQ]
      exact hR
    have hmem : Q ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hcanon⟩
    have h := (hsmall Q hmem).le
    have hdeg (c : Lattice n → ℝ) : («Σ».canonicalPrimitive Q).degree c = R.degree c := by
      rw [← («Σ».canonicalPrimitive Q).vector_pairing, hQ, R.vector_pairing]
    rw [PrimitiveRelation.degree_sub, PrimitiveRelation.degree_smul]
    dsimp only [f, g] at h
    rw [hdeg, hdeg] at h
    linarith
  have hs := «Σ».isStrictSupport_add_of_nef hnef (IsStrictSupport.smul «Σ» hH hε)
  convert hs using 1
  ext u
  simp

end SmoothCompleteFan

namespace LatticePolytope

theorem fanPolytope_integralSupport_eq {n : ℕ} (P : LatticePolytope n)
    («Σ» : SmoothCompleteFan n) (hfan : «Σ».realCones = P.normalFan) :
    «Σ».fanPolytope (fun u => (P.integralSupport u : ℝ)) = P.carrier := by
  ext x
  rw [P.mem_carrier_iff_normal_ray_inequalities «Σ» hfan]
  change (∀ u ∈ «Σ».rays, -(P.integralSupport u : ℝ) ≤
    (dotProductEquiv ℝ (Fin n) (embed n u)) x) ↔ _
  constructor <;> intro h u hu <;> have hh := h u hu <;> linarith

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricFanPolytopes
-- END ORIGINAL PaperVerification.ToricFanPolytopes


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanWeights
section Source_ToricBundleFanWeights

-- original header: module

-- original header: public import PaperVerification.ToricBundleFan
-- original header: public import PaperVerification.ToricFanPolytopes


-- original header: @[expose] public section
/-!
# Actual homogeneous fiber weights and base inequalities

For a zero-focus relation the homogeneous coordinates are the actual slacks
`a(v) + ⟨v,x⟩` on its positive rays.  Their sum is the fiber degree.  The
remaining inequalities are those of the genuine base fan with coefficients
`C_α = C_base + Σ α_i E_i`.  The formulas below hold for arbitrary real
support coefficients and weights; no positivity or convexity is hidden in
the definitions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem dotProductEquiv_dualVector {n : ℕ}
    (f : Ambient n →ₗ[ℝ] ℝ) (z : Ambient n) :
    (dotProductEquiv ℝ (Fin n) z) (dualVector f) = f z := by
  change (∑ i, z i * dualVector f i) = f z
  have h := dualVector_pairing f (0 : Ambient n) z
  simpa only [Pi.zero_apply, sub_zero, mul_comm] using h

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

/-- The fiber part of the dual functional at homogeneous weight `α`. -/
def fiberFunctional (a α : Lattice n → ℝ) : Ambient n →ₗ[ℝ] ℝ :=
  ∑ i ∈ c.fiberIndices,
    (α (c.basis i) - a (c.basis i)) • (integralBasisReal c.basis).coord i

def pointFunctional (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) : Ambient n →ₗ[ℝ] ℝ :=
  c.fiberFunctional a α +
    (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card)) y).comp c.quotientReal

/-- The actual ambient real point determined by fiber and base coordinates. -/
def point (a α : Lattice n → ℝ) (y : Ambient (n - c.fiberIndices.card)) : Ambient n :=
  dualVector (c.pointFunctional a α y)

theorem point_pairing (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) (z : Ambient n) :
    (dotProductEquiv ℝ (Fin n) z) (c.point a α y) =
      (∑ i ∈ c.fiberIndices,
        (α (c.basis i) - a (c.basis i)) * (integralBasisReal c.basis).repr z i) +
        (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card)) (c.quotientReal z)) y := by
  rw [point, dotProductEquiv_dualVector]
  simp only [pointFunctional, fiberFunctional, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    smul_eq_mul, LinearMap.comp_apply]
  congr 1
  change (∑ j, y j * c.quotientReal z j) = ∑ j, c.quotientReal z j * y j
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem point_pairing_lattice (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) (v : Lattice n) :
    (dotProductEquiv ℝ (Fin n) (embed n v)) (c.point a α y) =
      (∑ i ∈ c.fiberIndices,
        (c.basis.repr v i : ℝ) * (α (c.basis i) - a (c.basis i))) +
        (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card))
          (embed (n - c.fiberIndices.card) (c.quotientLattice v))) y := by
  rw [c.point_pairing, coneQuotient_compatible]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integralBasisReal_repr, mul_comm]

/-- Total homogeneous weight expressed in the independent fiber coordinates. -/
theorem weight_total_iff (a α : Lattice n → ℝ) :
    (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v ↔
      α c.omitted - a c.omitted =
        -(∑ i ∈ c.fiberIndices, (α (c.basis i) - a (c.basis i))) := by
  have hs (f : Lattice n → ℝ) : (∑ v ∈ R.positive, f v) =
      (∑ i ∈ c.fiberIndices, f (c.basis i)) + f c.omitted := by
    rw [← Finset.sum_erase_add R.positive f c.omitted_mem, ← c.fiber_ray_set,
      Finset.sum_image]
    exact fun i _ j _ hij => c.basis.injective hij
  rw [hs α, hs a, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

theorem point_pairing_positive (hN : R.negative = ∅)
    (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Ambient (n - c.fiberIndices.card)) {v : Lattice n} (hv : v ∈ R.positive) :
    (dotProductEquiv ℝ (Fin n) (embed n v)) (c.point a α y) = α v - a v := by
  rw [c.point_pairing_lattice, c.quotient_positive hN hv, map_zero,
    map_zero, LinearMap.zero_apply, add_zero]
  by_cases hvu : v = c.omitted
  · subst v
    rw [(c.weight_total_iff a α).mp hα]
    simp only [c.omitted_coordinate hN]
    simp [Finset.sum_neg_distrib]
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp
      (c.fiber_ray_set.symm ▸ Finset.mem_erase.mpr ⟨hvu, hv⟩)
    simp [Module.Basis.repr_self_apply, Finsupp.single_apply, hi]

/-- The literal base coefficient at homogeneous fiber weight `α`. -/
def baseWeight (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℝ) (q : Lattice (n - c.fiberIndices.card)) : ℝ :=
  a (c.baseRayLift hR hN q) + ∑ i ∈ c.fiberIndices,
    (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) *
      (α (c.basis i) - a (c.basis i))

/-- The integer piecewise-linear twisting coefficient attached to a fiber
ray. The omitted ray has coefficient zero in the chosen splitting. -/
def twistCoefficient (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (v : Lattice n) (q : Lattice (n - c.fiberIndices.card)) : ℤ :=
  ∑ i ∈ c.fiberIndices, if c.basis i = v then
    c.basis.repr (c.baseRayLift hR hN q) i else 0

theorem twistCoefficient_omitted (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (q : Lattice (n - c.fiberIndices.card)) :
    c.twistCoefficient hR hN c.omitted q = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hne : c.basis i ≠ c.omitted := by
    intro he
    have hm := c.fiber_ray_set ▸ Finset.mem_image.mpr ⟨i, hi, rfl⟩
    exact (Finset.mem_erase.mp hm).1 he
  simp only [if_neg hne]

theorem baseWeight_affine (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℝ) (q : Lattice (n - c.fiberIndices.card)) :
    c.baseWeight hR hN a α q = c.baseWeight hR hN a 0 q +
      ∑ i ∈ c.fiberIndices, (c.basis.repr (c.baseRayLift hR hN q) i : ℝ) * α (c.basis i) := by
  unfold baseWeight
  simp only [Pi.zero_apply, zero_sub, mul_sub, mul_neg, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  ring

theorem nonfiber_slack_identity (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) {v : Lattice n}
    (hv : v ∈ «Σ».rays \ R.positive) :
    a v + (dotProductEquiv ℝ (Fin n) (embed n v)) (c.point a α y) =
      c.baseWeight hR hN a α (c.quotientLattice v) +
        (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card))
          (embed (n - c.fiberIndices.card) (c.quotientLattice v))) y := by
  rw [c.point_pairing_lattice]
  unfold baseWeight
  rw [c.baseRayLift_quotient hR hN hv]
  ring

/-- The homogeneous-coordinate description is exactly equivalent to the
original ambient polytope inequalities. -/
theorem point_mem_fanPolytope_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.point a α y ∈ «Σ».fanPolytope a ↔
      (∀ v ∈ R.positive, 0 ≤ α v) ∧
        y ∈ c.baseFan.fanPolytope (c.baseWeight hR hN a α) := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro v hv
      have h := hx v (R.primitive.1 hv)
      rw [c.point_pairing_positive hN a α hα y hv] at h
      linarith
    · intro q hq
      have hv := c.baseRayLift_mem hR hN hq
      have h := hx (c.baseRayLift hR hN q) (Finset.mem_sdiff.mp hv).1
      have he := c.nonfiber_slack_identity hR hN a α y hv
      rw [c.quotient_baseRayLift hR hN hq] at he
      linarith
  · rintro ⟨hα0, hy⟩ v hv
    by_cases hvP : v ∈ R.positive
    · rw [c.point_pairing_positive hN a α hα y hvP]
      linarith [hα0 v hvP]
    · have hv' := Finset.mem_sdiff.mpr ⟨hv, hvP⟩
      have hq := (c.base_ray_iff hR hN _).mpr ⟨v, hv', rfl⟩
      have h := hy (c.quotientLattice v) hq
      have he := c.nonfiber_slack_identity hR hN a α y hv'
      linarith

/-- Actual homogeneous weights of an ambient point. -/
def homogeneousWeight (c : R.BundleCoordinates) (a : Lattice n → ℝ) (x : Ambient n) (v : Lattice n) : ℝ :=
  a v + (dotProductEquiv ℝ (Fin n) (embed n v)) x

theorem homogeneousWeight_total (hN : R.negative = ∅)
    (a : Lattice n → ℝ) (x : Ambient n) :
    (∑ v ∈ R.positive, c.homogeneousWeight a x v) = ∑ v ∈ R.positive, a v := by
  have hsum : (∑ v ∈ R.positive, embed n v) = 0 := by
    rw [← map_sum, R.equation, hN, Finset.sum_empty, map_zero]
  simp only [homogeneousWeight, Finset.sum_add_distrib]
  have hz : (∑ v ∈ R.positive, (dotProductEquiv ℝ (Fin n) (embed n v)) x) = 0 := by
    have h := congrArg (fun z : Ambient n => (dotProductEquiv ℝ (Fin n) z) x) hsum
    simpa only [map_sum, LinearMap.sum_apply, map_zero, LinearMap.zero_apply] using h
  rw [hz, add_zero]

/-- The actual base coordinates are obtained by pairing with the integral
section of the quotient. -/
def basePoint (x : Ambient n) : Ambient (n - c.fiberIndices.card) :=
  dualVector ((dotProductEquiv ℝ (Fin n) x).comp
    (coneQuotientSectionReal c.basis c.fiberIndices))

theorem point_homogeneousWeight_basePoint (a : Lattice n → ℝ) (x : Ambient n) :
    c.point a (c.homogeneousWeight a x) (c.basePoint x) = x := by
  apply (dotProductEquiv ℝ (Fin n)).injective
  apply LinearMap.ext
  intro z
  have hp := c.point_pairing a (c.homogeneousWeight a x) (c.basePoint x) z
  have hb := dotProductEquiv_dualVector
    ((dotProductEquiv ℝ (Fin n) x).comp
      (coneQuotientSectionReal c.basis c.fiberIndices)) (c.quotientReal z)
  have hd := basisSection_projection_decomposition (integralBasisReal c.basis)
    c.fiberIndices z
  have he := congrArg ((dotProductEquiv ℝ (Fin n) x) : Ambient n → ℝ) hd
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at he
  change (dotProductEquiv ℝ (Fin n) (c.point a (c.homogeneousWeight a x) (c.basePoint x))) z =
    (dotProductEquiv ℝ (Fin n) x) z
  rw [show (dotProductEquiv ℝ (Fin n) (c.point a (c.homogeneousWeight a x) (c.basePoint x))) z =
      (dotProductEquiv ℝ (Fin n) z) (c.point a (c.homogeneousWeight a x) (c.basePoint x)) by
        exact dotProduct_comm
          (c.point a (c.homogeneousWeight a x) (c.basePoint x)) z, hp]
  change _ + (dotProductEquiv ℝ (Fin (n - c.fiberIndices.card)) (c.quotientReal z))
    (dualVector _) = _
  rw [hb]
  have hsec : coneQuotientSectionReal c.basis c.fiberIndices (c.quotientReal z) =
      basisSection (integralBasisReal c.basis) c.fiberIndices
        (basisProjection (integralBasisReal c.basis) c.fiberIndices z) := by
    simp [coneQuotientSectionReal, quotientReal, coneQuotientReal]
  rw [LinearMap.comp_apply, hsec]
  simp only [homogeneousWeight, add_sub_cancel_left]
  have hpair (i : Fin n) :
      (dotProductEquiv ℝ (Fin n) (embed n (c.basis i))) x =
        (dotProductEquiv ℝ (Fin n) x) (integralBasisReal c.basis i) := by
    rw [integralBasisReal_apply]
    exact dotProduct_comm (embed n (c.basis i)) x
  simp only [hpair]
  calc
    _ = (dotProductEquiv ℝ (Fin n) x)
        (basisSection (integralBasisReal c.basis) c.fiberIndices
          (basisProjection (integralBasisReal c.basis) c.fiberIndices z)) +
        ∑ i ∈ c.fiberIndices, (integralBasisReal c.basis).repr z i *
          (dotProductEquiv ℝ (Fin n) x) (integralBasisReal c.basis i) := by
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ = _ := he

/-- The coefficient identity used in canonical adjunction.  It is a literal
identity of the actual ray coefficients, including the `-1` on each base ray. -/
theorem baseWeight_canonical (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a β : Lattice n → ℝ)
    (q : Lattice (n - c.fiberIndices.card)) :
    c.baseWeight hR hN (fun v => a v - 1) β q =
      c.baseWeight hR hN a (fun v => β v + 1) q - 1 := by
  unfold baseWeight
  have he (i : Fin n) : β (c.basis i) - (a (c.basis i) - 1) =
      (β (c.basis i) + 1) - a (c.basis i) := by ring
  simp only [he]
  ring

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanWeights
-- END ORIGINAL PaperVerification.ToricBundleFanWeights


-- BEGIN ORIGINAL PaperVerification.ToricIntegralAffine
section Source_ToricIntegralAffine

-- original header: module
-- original header: public import PaperVerification.ToricIntegralBasis
-- original header: @[expose] public section
/-!
# Saturated integral affine coordinate embeddings

These data encode an ordinary injective integral affine map whose linear image
is saturated in the ambient lattice. The saturation clause is about all actual
lattice vectors in that real subspace; no decomposition property is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricExchange

/-- An integral affine coordinate embedding with exactly the induced lattice
on its real image. -/
structure IntegralAffineEmbedding (d n : ℕ) where
  origin : Lattice n
  linear : Lattice d →+ Lattice n
  realLinear : Ambient d →ₗ[ℝ] Ambient n
  injective : Function.Injective realLinear
  compatible : ∀ z, embed n (linear z) = realLinear (embed d z)
  saturated : ∀ z : Lattice n, embed n z ∈ Set.range realLinear → ∃ w, linear w = z

/-- Coordinate content of an integer vector, equal to its lattice segment length. -/
def latticeContent {n : ℕ} (z : Lattice n) : ℕ :=
  Finset.univ.gcd (fun i => (z i).natAbs)

/-- Coordinate gcd divisibility is exactly divisibility of the whole lattice vector. -/
theorem dvd_latticeContent_iff {n : ℕ} (k : ℕ) (z : Lattice n) :
    k ∣ latticeContent z ↔ ∃ w : Lattice n, z = (k : ℤ) • w := by
  classical
  constructor
  · intro hk
    have hd (i : Fin n) : (k : ℤ) ∣ z i :=
      Int.natCast_dvd.mpr (hk.trans (Finset.gcd_dvd (Finset.mem_univ i)))
    choose w hw using hd
    exact ⟨w, by funext i; exact hw i⟩
  · rintro ⟨w, rfl⟩
    apply Finset.dvd_gcd
    intro i hi
    apply Int.natCast_dvd.mp
    exact ⟨w i, rfl⟩

/-- Injective affine maps preserve ordinary extreme subsets. -/
theorem affine_isExtreme_image {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P F : Set V} (hF : IsExtreme ℝ P F) :
    IsExtreme ℝ (f '' P) (f '' F) := by
  refine ⟨Set.image_mono hF.subset, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
  rw [← image_openSegment ℝ f x y] at hseg
  obtain ⟨w, hw, he⟩ := hseg
  have hwz := hf he
  subst w
  exact ⟨x, hF.left_mem_of_mem_openSegment hx hy hz hw, rfl⟩

/-- Extremeness of an affine image is equivalent to extremeness in the source. -/
theorem affine_isExtreme_image_iff {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P F : Set V) :
    IsExtreme ℝ (f '' P) (f '' F) ↔ IsExtreme ℝ P F := by
  constructor
  · intro hF
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, he⟩ := hF.subset ⟨x, hx, rfl⟩
      have hyx := hf he
      simpa only [hyx] using hy
    · intro x hx y hy z hz hseg
      have hseg' : f z ∈ openSegment ℝ (f x) (f y) := by
        rw [← image_openSegment ℝ f x y]
        exact ⟨z, hseg, rfl⟩
      obtain ⟨w, hw, he⟩ := hF.left_mem_of_mem_openSegment
        ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hseg'
      have hwx := hf he
      simpa only [hwx] using hw
  · exact affine_isExtreme_image f hf

namespace IntegralAffineEmbedding

variable {d n : ℕ} (e : IntegralAffineEmbedding d n)

theorem linear_injective : Function.Injective e.linear := by
  intro x y h
  apply embed_injective d
  apply e.injective
  simpa only [e.compatible] using congrArg (embed n) h

/-- Saturation preserves divisibility of lattice vectors by every natural
number, including zero. -/
theorem linear_exists_smul_iff (k : ℕ) (z : Lattice d) :
    (∃ w : Lattice n, e.linear z = (k : ℤ) • w) ↔
      ∃ w : Lattice d, z = (k : ℤ) • w := by
  constructor
  · rintro ⟨w, hw⟩
    by_cases hk : k = 0
    · subst k
      refine ⟨0, ?_⟩
      apply e.linear_injective
      simpa using hw
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have he : e.realLinear (embed d z) = (k : ℝ) • embed n w := by
        rw [← e.compatible, hw, embed_int_smul, Int.cast_natCast]
      have hwrange : embed n w ∈ Set.range e.realLinear := by
        refine ⟨(k : ℝ)⁻¹ • embed d z, ?_⟩
        rw [map_smul, he, smul_smul, inv_mul_cancel₀ hkR, one_smul]
      obtain ⟨v, hv⟩ := e.saturated w hwrange
      refine ⟨v, ?_⟩
      apply e.linear_injective
      rw [map_zsmul, hv]
      exact hw
  · rintro ⟨w, rfl⟩
    exact ⟨e.linear w, map_zsmul e.linear _ _⟩

/-- Saturated integral embeddings preserve the exact coordinate gcd. -/
theorem latticeContent_linear (z : Lattice d) :
    latticeContent (e.linear z) = latticeContent z := by
  apply Nat.dvd_antisymm
  · apply (dvd_latticeContent_iff _ z).mpr
    apply (e.linear_exists_smul_iff _ z).mp
    exact (dvd_latticeContent_iff _ (e.linear z)).mp dvd_rfl
  · apply (dvd_latticeContent_iff _ (e.linear z)).mpr
    apply (e.linear_exists_smul_iff _ z).mpr
    exact (dvd_latticeContent_iff _ z).mp dvd_rfl

/-- The actual real affine map, including its integral translation. -/
def realMap : Ambient d →ᵃ[ℝ] Ambient n :=
  AffineMap.const ℝ (Ambient d) (embed n e.origin) + e.realLinear.toAffineMap

/-- The corresponding map on actual integer coordinates. -/
def latticeMap (z : Lattice d) : Lattice n := e.origin + e.linear z

@[simp] theorem realMap_apply (x : Ambient d) :
    e.realMap x = embed n e.origin + e.realLinear x := rfl

@[simp] theorem embed_latticeMap (z : Lattice d) :
    embed n (e.latticeMap z) = e.realMap (embed d z) := by
  simp [latticeMap, realMap_apply, e.compatible]

theorem realMap_injective : Function.Injective e.realMap := by
  intro x y h
  apply e.injective
  exact add_left_cancel h

theorem latticeMap_injective : Function.Injective e.latticeMap := by
  intro x y h
  apply embed_injective d
  apply e.realMap_injective
  simpa only [embed_latticeMap] using congrArg (embed n) h

/-- The usual lattice length is unchanged by a saturated integral affine chart. -/
theorem latticeLength_latticeMap (x y : Lattice d) :
    LatticePolytope.latticeLength (e.latticeMap x) (e.latticeMap y) =
      LatticePolytope.latticeLength x y := by
  change latticeContent (e.latticeMap y - e.latticeMap x) = latticeContent (y - x)
  have he : e.latticeMap y - e.latticeMap x = e.linear (y - x) := by
    simp only [latticeMap, map_sub]
    abel
  rw [he, e.latticeContent_linear]

/-- Every ambient lattice point in the affine image has unique integral
coordinates. Thus the coordinate lattice is the saturated face lattice. -/
theorem exists_latticeMap_of_mem_range (z : Lattice n)
    (hz : embed n z ∈ Set.range e.realMap) :
    ∃ w : Lattice d, e.latticeMap w = z := by
  obtain ⟨x, hx⟩ := hz
  have hrange : embed n (z - e.origin) ∈ Set.range e.realLinear := by
    refine ⟨x, ?_⟩
    rw [map_sub, ← hx, realMap_apply, add_sub_cancel_left]
  obtain ⟨w, hw⟩ := e.saturated (z - e.origin) hrange
  refine ⟨w, ?_⟩
  simp only [latticeMap, hw]
  abel

/-- Lattice-point membership in an affine image is exactly membership of the
unique integral preimage. -/
theorem lattice_image_membership (P : Set (Ambient d)) (z : Lattice n) :
    embed n z ∈ e.realMap '' P ↔
      ∃ w : Lattice d, embed d w ∈ P ∧ e.latticeMap w = z := by
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨w, hw⟩ := e.exists_latticeMap_of_mem_range z ⟨x, he⟩
    refine ⟨w, ?_, hw⟩
    have hcoord : embed d w = x := by
      apply e.realMap_injective
      rw [← e.embed_latticeMap, hw, he]
    simpa only [hcoord] using hx
  · rintro ⟨w, hw, rfl⟩
    exact ⟨embed d w, hw, (e.embed_latticeMap w).symm⟩

/-- The induced map on points of a convex set uses the actual affine image. -/
def mapLatticePoint (P : Set (Ambient d)) :
    latticePoints (embed d) P → latticePoints (embed n) (e.realMap '' P) :=
  fun z => ⟨e.latticeMap z, (e.lattice_image_membership P _).mpr ⟨z, z.property, rfl⟩⟩

/-- Summing affine images adds one copy of the origin per summand. -/
theorem total_mapLatticePoint (P : Set (Ambient d))
    (s : Multiset (latticePoints (embed d) P)) :
    total (latticePoints (embed n) (e.realMap '' P)) (s.map (e.mapLatticePoint P)) =
      s.card • e.origin + e.linear (total (latticePoints (embed d) P) s) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, total_cons, ih, Multiset.card_cons, map_add,
      add_nsmul, one_nsmul]
    change e.origin + e.linear (a : Lattice d) +
      (s.card • e.origin + e.linear (total (latticePoints (embed d) P) s)) = _
    abel

/-- Full integer decomposition transfers through a saturated integral affine
embedding in every degree, with the translation multiplicity handled exactly. -/
theorem integerDecompositionProperty_image (P : Set (Ambient d))
    (hP : IntegerDecompositionProperty (embed d) P) :
    IntegerDecompositionProperty (embed n) (e.realMap '' P) := by
  intro k hk z hz
  obtain ⟨_, ⟨x, hx, rfl⟩, hz⟩ := hz
  have hdiff : embed n (z - (k : ℤ) • e.origin) = e.realLinear ((k : ℝ) • x) := by
    rw [map_sub, embed_int_smul, hz, realMap_apply, smul_add, map_smul]
    simp only [Int.cast_natCast]
    abel
  obtain ⟨u, hu⟩ := e.saturated (z - (k : ℤ) • e.origin) ⟨(k : ℝ) • x, hdiff.symm⟩
  have huR : embed d u = (k : ℝ) • x := by
    apply e.injective
    rw [← e.compatible, hu, hdiff]
  obtain ⟨s, hcard, htotal⟩ := hP k hk u ⟨x, hx, huR⟩
  refine ⟨s.map (e.mapLatticePoint P), ?_, ?_⟩
  · simpa only [Multiset.card_map] using hcard
  · rw [e.total_mapLatticePoint, hcard, htotal, hu, natCast_zsmul]
    abel

/-- The affine range of a full-dimensional coordinate polytope equals the
actual affine span of its image. -/
theorem realMap_range_eq_affineSpan (P : LatticePolytope d) :
    Set.range e.realMap = (affineSpan ℝ (e.realMap '' P.carrier) : Set (Ambient n)) := by
  rw [← AffineSubspace.map_span]
  change Set.range e.realMap = e.realMap '' (affineSpan ℝ P.carrier : Set (Ambient d))
  rw [show affineSpan ℝ P.carrier = ⊤ from P.fullDimensional]
  simp

/-- Two full-dimensional charts of the same actual set have equal affine ranges. -/
theorem realMap_range_eq_of_image_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n) (P : LatticePolytope d) (Q : LatticePolytope k)
    (h : e.realMap '' P.carrier = f.realMap '' Q.carrier) :
    Set.range e.realMap = Set.range f.realMap := by
  rw [e.realMap_range_eq_affineSpan P, f.realMap_range_eq_affineSpan Q, h]

/-- Edges in a chart are exactly the actual nondegenerate segment faces of
its affine image. -/
theorem edge_iff_ambient (P : LatticePolytope d) (x y : Ambient d) :
    P.IsEdge x y ↔ e.realMap x ≠ e.realMap y ∧
      IsExtreme ℝ (e.realMap '' P.carrier) (segment ℝ (e.realMap x) (e.realMap y)) := by
  rw [LatticePolytope.IsEdge, ← image_segment ℝ e.realMap,
    affine_isExtreme_image_iff e.realMap e.realMap_injective]
  constructor
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (e.realMap_injective he), hface⟩
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (congrArg e.realMap he), hface⟩

/-- Actual edges transfer between any two injective affine charts of the same set. -/
theorem edge_transfer_iff {k : ℕ} (f : IntegralAffineEmbedding k n)
    (P : LatticePolytope d) (Q : LatticePolytope k)
    (h : e.realMap '' P.carrier = f.realMap '' Q.carrier)
    (x y : Ambient d) (u v : Ambient k)
    (hx : e.realMap x = f.realMap u) (hy : e.realMap y = f.realMap v) :
    P.IsEdge x y ↔ Q.IsEdge u v := by
  rw [e.edge_iff_ambient P, f.edge_iff_ambient Q, h, hx, hy]

/-- Equal affine coordinate ranges have equal linear direction ranges, even
when the two integral origins differ. -/
theorem linear_range_eq_of_affine_range_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realMap = Set.range f.realMap) :
    Set.range e.realLinear = Set.range f.realLinear := by
  have hincl {d k : ℕ} (e : IntegralAffineEmbedding d n) (f : IntegralAffineEmbedding k n)
      (h : Set.range e.realMap = Set.range f.realMap) :
      Set.range e.realLinear ⊆ Set.range f.realLinear := by
    rintro z ⟨x, rfl⟩
    have hx : e.realMap x ∈ Set.range f.realMap := by rw [← h]; exact Set.mem_range_self x
    have hzero : e.realMap 0 ∈ Set.range f.realMap := by rw [← h]; exact Set.mem_range_self 0
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y0, hy0⟩ := hzero
    refine ⟨y - y0, ?_⟩
    rw [map_sub]
    have he := congrArg₂ (fun a b : Ambient n => a - b) hy hy0
    simpa only [realMap_apply, map_zero, add_zero, add_sub_add_left_eq_sub,
      add_sub_cancel_left] using he
  exact Set.Subset.antisymm (hincl e f h) (hincl f e h.symm)

/-- Saturation supplies an integral coordinate preimage for every vector
expressed in another chart of the same real direction subspace. -/
theorem exists_linear_preimage_of_range_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    ∃ w : Lattice d, e.linear w = f.linear z := by
  apply e.saturated
  rw [h, f.compatible]
  exact Set.mem_range_self (embed k z)

/-- The integral linear map changing between two saturated coordinate charts. -/
def changeLinearMap {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) : Lattice k →ₗ[ℤ] Lattice d where
  toFun z := Classical.choose (e.exists_linear_preimage_of_range_eq f h z)
  map_add' x y := by
    apply e.linear_injective
    change e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h (x + y))) =
      e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h x) +
        Classical.choose (e.exists_linear_preimage_of_range_eq f h y))
    rw [Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h (x + y))]
    simp only [map_add,
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h x),
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h y)]
  map_smul' r x := by
    apply e.linear_injective
    change e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h (r • x))) =
      e.linear (r • Classical.choose (e.exists_linear_preimage_of_range_eq f h x))
    rw [Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h (r • x))]
    simp only [map_zsmul,
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h x)]

@[simp] theorem changeLinearMap_apply {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    e.linear (e.changeLinearMap f h z) = f.linear z :=
  Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h z)

/-- The change of saturated lattice coordinates is an actual integral linear
equivalence, in arbitrary source dimensions. -/
def changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) : Lattice k ≃ₗ[ℤ] Lattice d :=
  LinearEquiv.ofBijective (e.changeLinearMap f h) ⟨by
    intro x y hxy
    apply f.linear_injective
    simpa only [e.changeLinearMap_apply] using congrArg e.linear hxy, by
    intro y
    obtain ⟨x, hx⟩ := f.exists_linear_preimage_of_range_eq e h.symm y
    refine ⟨x, e.linear_injective ?_⟩
    rw [e.changeLinearMap_apply]
    exact hx⟩

@[simp] theorem changeLinear_apply {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    e.linear (e.changeLinear f h z) = f.linear z :=
  e.changeLinearMap_apply f h z

/-- Changing a saturated coordinate chart translates the origin once and
then uses the exact integral linear change of coordinates. -/
theorem latticeMap_changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear)
    (z0 : Lattice d) (hz0 : e.latticeMap z0 = f.origin) (z : Lattice k) :
    e.latticeMap (z0 + e.changeLinear f h z) = f.latticeMap z := by
  change e.origin + e.linear (z0 + e.changeLinear f h z) = f.origin + f.linear z
  rw [map_add, e.changeLinear_apply, ← add_assoc]
  exact congrArg (fun x => x + f.linear z) hz0

/-- The real images of integer-coordinate changes agree exactly. -/
theorem realMap_changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear)
    (z0 : Lattice d) (hz0 : e.latticeMap z0 = f.origin) (z : Lattice k) :
    e.realMap (embed d (z0 + e.changeLinear f h z)) = f.realMap (embed k z) := by
  rw [← e.embed_latticeMap, e.latticeMap_changeLinear f h z0 hz0 z, f.embed_latticeMap]

/-- Applying an affine lattice chart preserves the prescribed parity class
of a difference. This is the forward direction used for face parity. -/
theorem sameParity_latticeMap {x y : Lattice d} (h : SameParity x y) :
    SameParity (e.latticeMap x) (e.latticeMap y) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨e.linear w, ?_⟩
  change (e.origin + e.linear x) - (e.origin + e.linear y) = _
  rw [add_sub_add_left_eq_sub, ← map_sub, hw, map_add]

end IntegralAffineEmbedding

end PaperVerification.ToricGeometry
end
end Source_ToricIntegralAffine
-- END ORIGINAL PaperVerification.ToricIntegralAffine


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanIntegral
section Source_ToricBundleFanIntegral

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanWeights
-- original header: public import PaperVerification.ToricIntegralAffine


-- original header: @[expose] public section
/-!
# The saturated integral lattice of every homogeneous fiber slice

The chart at a fixed integral homogeneous weight is an explicit integral
affine embedding.  Its image lattice is saturated, because its base-coordinate
inverse pairs with the integral section of the quotient.  This is the exact
lattice statement needed for parity classes and inherited edge lengths.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

def integerDualVector {n : ℕ} (f : Lattice n →ₗ[ℤ] ℤ) : Lattice n :=
  fun i => f (Pi.basisFun ℤ (Fin n) i)

theorem embed_standard_basis (n : ℕ) (i : Fin n) :
    embed n (Pi.basisFun ℤ (Fin n) i) = Pi.basisFun ℝ (Fin n) i := by
  funext j
  simp [Pi.basisFun_apply, Pi.single_apply, embed]

theorem embed_integerDualVector {n : ℕ}
    (f : Lattice n →ₗ[ℤ] ℤ) (g : Ambient n →ₗ[ℝ] ℝ)
    (hfg : ∀ z : Lattice n, g (embed n z) = (f z : ℝ)) :
    embed n (integerDualVector f) = dualVector g := by
  funext i
  have h := hfg (Pi.basisFun ℤ (Fin n) i)
  rw [embed_standard_basis] at h
  exact h.symm

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

def integerBaseWeight (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℤ) (q : Lattice (n - c.fiberIndices.card)) : ℤ :=
  a (c.baseRayLift hR hN q) + ∑ i ∈ c.fiberIndices,
    c.basis.repr (c.baseRayLift hR hN q) i * (α (c.basis i) - a (c.basis i))

theorem integerBaseWeight_cast (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (a α : Lattice n → ℤ) (q : Lattice (n - c.fiberIndices.card)) :
    (c.integerBaseWeight hR hN a α q : ℝ) =
      c.baseWeight hR hN (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) q := by
  simp only [integerBaseWeight, baseWeight]
  push_cast
  rfl

def integerPointFunctional (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) : Lattice n →ₗ[ℤ] ℤ :=
  (∑ i ∈ c.fiberIndices, (α (c.basis i) - a (c.basis i)) • c.basis.coord i) +
    (dotProductEquiv ℤ (Fin (n - c.fiberIndices.card)) y).comp c.quotientLattice

def integerPoint (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) : Lattice n :=
  integerDualVector (c.integerPointFunctional a α y)

theorem pointFunctional_compatible (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) (z : Lattice n) :
    c.pointFunctional (fun v => (a v : ℝ)) (fun v => (α v : ℝ))
      (embed (n - c.fiberIndices.card) y) (embed n z) =
        (c.integerPointFunctional a α y z : ℝ) := by
  simp only [pointFunctional, fiberFunctional, integerPointFunctional,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Module.Basis.coord_apply, smul_eq_mul,
    integralBasisReal_repr, coneQuotient_compatible]
  change (∑ i ∈ c.fiberIndices,
      ((α (c.basis i) : ℝ) - (a (c.basis i) : ℝ)) * (c.basis.repr z i : ℝ)) +
    (∑ j, (y j : ℝ) * (c.quotientLattice z j : ℝ)) =
      (((∑ i ∈ c.fiberIndices,
          (α (c.basis i) - a (c.basis i)) * c.basis.repr z i) +
        ∑ j, y j * c.quotientLattice z j : ℤ) : ℝ)
  push_cast
  rfl

theorem integerPoint_compatible (a α : Lattice n → ℤ)
    (y : Lattice (n - c.fiberIndices.card)) :
    embed n (c.integerPoint a α y) =
      c.point (fun v => (a v : ℝ)) (fun v => (α v : ℝ))
        (embed (n - c.fiberIndices.card) y) :=
  embed_integerDualVector _ _ (c.pointFunctional_compatible a α y)

theorem fiberFunctional_section (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.fiberFunctional a α (coneQuotientSectionReal c.basis c.fiberIndices y) = 0 := by
  simp only [fiberFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, smul_eq_mul, coneQuotientSectionReal,
    LinearMap.comp_apply, basisSection_repr]
  apply Finset.sum_eq_zero
  intro i hi
  rw [dif_pos hi, mul_zero]

theorem basePoint_point (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) : c.basePoint (c.point a α y) = y := by
  funext j
  change (dotProductEquiv ℝ (Fin n) (c.point a α y))
      (coneQuotientSectionReal c.basis c.fiberIndices
        (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j)) = y j
  rw [show (dotProductEquiv ℝ (Fin n) (c.point a α y))
      (coneQuotientSectionReal c.basis c.fiberIndices
        (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j)) =
      (dotProductEquiv ℝ (Fin n)
        (coneQuotientSectionReal c.basis c.fiberIndices
          (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j))) (c.point a α y) by
      exact dotProduct_comm (c.point a α y)
        (coneQuotientSectionReal c.basis c.fiberIndices
          (Pi.basisFun ℝ (Fin (n - c.fiberIndices.card)) j))]
  rw [point, dotProductEquiv_dualVector]
  simp only [pointFunctional, LinearMap.add_apply, LinearMap.comp_apply,
    c.fiberFunctional_section, coneQuotient_section_real, zero_add]
  simp [dotProductEquiv, dotProduct, Pi.basisFun_apply, Pi.single_apply]

def integerBasePoint (z : Lattice n) : Lattice (n - c.fiberIndices.card) :=
  integerDualVector ((dotProductEquiv ℤ (Fin n) z).comp
    (coneQuotientSectionLattice c.basis c.fiberIndices))

theorem integerBasePoint_compatible (z : Lattice n) :
    embed (n - c.fiberIndices.card) (c.integerBasePoint z) = c.basePoint (embed n z) := by
  apply embed_integerDualVector
  intro y
  simp only [LinearMap.comp_apply, coneQuotientSection_compatible]
  change (∑ i, (z i : ℝ) * (coneQuotientSectionLattice c.basis c.fiberIndices y i : ℝ)) =
    ((∑ i, z i * coneQuotientSectionLattice c.basis c.fiberIndices y i : ℤ) : ℝ)
  push_cast
  rfl

def baseLinearLattice : Lattice (n - c.fiberIndices.card) →+ Lattice n where
  toFun y := c.integerPoint 0 0 y
  map_zero' := by
    funext i
    simp [integerPoint, integerDualVector, integerPointFunctional]
  map_add' y z := by
    funext i
    simp [integerPoint, integerDualVector, integerPointFunctional, map_add]

def baseLinearReal : Ambient (n - c.fiberIndices.card) →ₗ[ℝ] Ambient n where
  toFun y := c.point 0 0 y
  map_add' y z := by
    funext i
    simp [point, dualVector, pointFunctional, fiberFunctional, map_add]
  map_smul' a y := by
    funext i
    simp [point, dualVector, pointFunctional, fiberFunctional, map_smul]

theorem baseLinear_compatible (z : Lattice (n - c.fiberIndices.card)) :
    embed n (c.baseLinearLattice z) = c.baseLinearReal (embed (n - c.fiberIndices.card) z) := by
  change embed n (c.integerPoint 0 0 z) =
    c.point 0 0 (embed (n - c.fiberIndices.card) z)
  have hzero : (fun v : Lattice n => (((0 : Lattice n → ℤ) v : ℤ) : ℝ)) =
      (0 : Lattice n → ℝ) := by
    funext v
    simp only [Pi.zero_apply, Int.cast_zero]
  have h := c.integerPoint_compatible (0 : Lattice n → ℤ) (0 : Lattice n → ℤ) z
  rw [hzero] at h
  exact h

theorem baseLinear_injective : Function.Injective c.baseLinearReal := by
  intro x y h
  have he := congrArg c.basePoint h
  change c.basePoint (c.point 0 0 x) = c.basePoint (c.point 0 0 y) at he
  rw [c.basePoint_point, c.basePoint_point] at he
  exact he

theorem baseLinear_saturated (z : Lattice n)
    (hz : embed n z ∈ Set.range c.baseLinearReal) :
    ∃ w : Lattice (n - c.fiberIndices.card), c.baseLinearLattice w = z := by
  obtain ⟨y, hy⟩ := hz
  have hycoord : y = embed (n - c.fiberIndices.card) (c.integerBasePoint z) := by
    have he := congrArg c.basePoint hy
    rw [show c.baseLinearReal y = c.point 0 0 y from rfl, c.basePoint_point,
      ← c.integerBasePoint_compatible z] at he
    exact he
  refine ⟨c.integerBasePoint z, ?_⟩
  apply embed_injective n
  rw [c.baseLinear_compatible, ← hycoord, hy]

/-- Fixed integral homogeneous weight gives a saturated integral affine chart. -/
def fiberChart (a α : Lattice n → ℤ) : IntegralAffineEmbedding (n - c.fiberIndices.card) n where
  origin := c.integerPoint a α 0
  linear := c.baseLinearLattice
  realLinear := c.baseLinearReal
  injective := c.baseLinear_injective
  compatible := c.baseLinear_compatible
  saturated := c.baseLinear_saturated

theorem point_add_base (a α : Lattice n → ℝ)
    (y : Ambient (n - c.fiberIndices.card)) :
    c.point a α y = c.point a α 0 + c.baseLinearReal y := by
  funext i
  simp [point, dualVector, pointFunctional, fiberFunctional, baseLinearReal]

theorem fiberChart_realMap (a α : Lattice n → ℤ)
    (y : Ambient (n - c.fiberIndices.card)) :
    (c.fiberChart a α).realMap y =
      c.point (fun v => (a v : ℝ)) (fun v => (α v : ℝ)) y := by
  rw [IntegralAffineEmbedding.realMap_apply]
  change embed n (c.integerPoint a α 0) + c.baseLinearReal y = _
  rw [c.integerPoint_compatible]
  simpa only [map_zero] using (c.point_add_base (fun v => (a v : ℝ))
    (fun v => (α v : ℝ)) y).symm

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanIntegral
-- END ORIGINAL PaperVerification.ToricBundleFanIntegral


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanEndpoints
section Source_ToricBundleFanEndpoints

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanIntegral


-- original header: @[expose] public section
/-!
# Endpoint divisors on the genuine base fan

At each vertex of the projective fiber simplex the base coefficients inherit
strict support from the original fan.  The supporting functions and their
slacks are computed explicitly using the integral quotient section.  Thus
ampleness of the endpoint base divisors is proved, not assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

def endpointWeight (c : R.BundleCoordinates) (a : Lattice n → ℝ) (u : Lattice n) (v : Lattice n) : ℝ :=
  if v = u then ∑ w ∈ R.positive, a w else 0

theorem endpointWeight_total (a : Lattice n → ℝ) {u : Lattice n}
    (hu : u ∈ R.positive) :
    (∑ v ∈ R.positive, c.endpointWeight a u v) = ∑ v ∈ R.positive, a v := by
  simp [endpointWeight, hu]

theorem endpointWeight_nonneg (a : Lattice n → ℝ)
    (hk : 0 ≤ ∑ w ∈ R.positive, a w) (u v : Lattice n) :
    0 ≤ c.endpointWeight a u v := by
  unfold endpointWeight
  split_ifs
  · exact hk
  · exact le_rfl

theorem weights_eq_endpoint (c : R.BundleCoordinates) {α : Lattice n → ℝ} {k : ℝ} {u : Lattice n}
    (hu : u ∈ R.positive) (hsum : (∑ v ∈ R.positive, α v) = k)
    (hzero : ∀ v ∈ R.positive.erase u, α v = 0) :
    ∀ v ∈ R.positive, α v = if v = u then k else 0 := by
  have hau : α u = k := by
    rw [← Finset.sum_erase_add R.positive α hu] at hsum
    have hz : (∑ v ∈ R.positive.erase u, α v) = 0 := Finset.sum_eq_zero hzero
    simpa only [hz, zero_add] using hsum
  intro v hv
  by_cases hvu : v = u
  · simp only [hvu, if_pos rfl, ite_true, hau]
  · rw [if_neg hvu]
    exact hzero v (Finset.mem_erase.mpr ⟨hvu, hv⟩)

theorem endpoint_support_coordinates (hN : R.negative = ∅)
    (a : Lattice n → ℝ) {u : Lattice n} (hu : u ∈ R.positive)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hℓ : ∀ v ∈ R.positive.erase u, ℓ (embed n v) = a v) :
    ∀ v ∈ R.positive, c.endpointWeight a u v - a v = -ℓ (embed n v) := by
  have hsum : (∑ v ∈ R.positive, ℓ (embed n v)) = 0 := by
    rw [← map_sum, ← map_sum, R.equation, hN, Finset.sum_empty, map_zero, map_zero]
  have hslack : (∑ v ∈ R.positive, (a v - ℓ (embed n v))) = ∑ v ∈ R.positive, a v := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
  have he := c.weights_eq_endpoint hu hslack (fun v hv => by rw [hℓ v hv, sub_self])
  intro v hv
  have h := he v hv
  change a v - ℓ (embed n v) = c.endpointWeight a u v at h
  linarith

def liftBaseCone (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (D : Finset (Lattice (n - c.fiberIndices.card))) : Finset (Lattice n) :=
  D.image (c.baseRayLift hR hN)

theorem liftBaseCone_subset_nonfiber (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice (n - c.fiberIndices.card))}
    (hD : D ⊆ c.baseFan.rays) :
    c.liftBaseCone hR hN D ⊆ «Σ».rays \ R.positive := by
  intro v hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
  exact c.baseRayLift_mem hR hN (hD hq)

theorem quotient_liftBaseCone (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice (n - c.fiberIndices.card))}
    (hD : D ⊆ c.baseFan.rays) :
    (c.liftBaseCone hR hN D).image c.quotientLattice = D := by
  unfold liftBaseCone
  rw [Finset.image_image]
  have he : D.image (fun q => c.quotientLattice (c.baseRayLift hR hN q)) = D.image id := by
    apply Finset.image_congr
    intro q hq
    exact c.quotient_baseRayLift hR hN (hD hq)
  change D.image (fun q => c.quotientLattice (c.baseRayLift hR hN q)) = D
  rw [he, Finset.image_id]

theorem liftBaseCone_mem (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice (n - c.fiberIndices.card))}
    (hD : D ∈ c.baseFan.cones) : c.liftBaseCone hR hN D ∈ «Σ».cones := by
  have hDrays : D ⊆ c.baseFan.rays :=
    fun q hq => (c.baseFan.mem_rays_iff q).mpr ⟨D, hD, hq⟩
  have hnon := c.liftBaseCone_subset_nonfiber hR hN hDrays
  apply (c.nonfiber_cone_iff_projected_cone hR hN
    (fun v hv => (Finset.mem_sdiff.mp (hnon hv)).1) ?_).mpr
  · rw [c.quotient_liftBaseCone hR hN hDrays]
    exact hD
  · exact Finset.disjoint_left.mpr
      (fun v hv hvP => (Finset.mem_sdiff.mp (hnon hv)).2 hvP)

theorem baseWeight_support_residual (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ) (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (hα : ∀ i ∈ c.fiberIndices,
      α (c.basis i) - a (c.basis i) = -ℓ (embed n (c.basis i)))
    {q : Lattice (n - c.fiberIndices.card)} (hq : q ∈ c.baseFan.rays) :
    c.baseWeight hR hN a α q -
      ℓ (coneQuotientSectionReal c.basis c.fiberIndices (embed (n - c.fiberIndices.card) q)) =
        a (c.baseRayLift hR hN q) - ℓ (embed n (c.baseRayLift hR hN q)) := by
  let v := c.baseRayLift hR hN q
  have hd := coneQuotient_decomposition c.basis c.fiberIndices (embed n v)
  rw [coneQuotient_compatible, c.quotient_baseRayLift hR hN hq] at hd
  have he := congrArg ℓ hd
  simp only [map_add, map_sum, map_smul, smul_eq_mul,
    integralBasisReal_repr, integralBasisReal_apply] at he
  have hsum : (∑ i ∈ c.fiberIndices, (c.basis.repr v i : ℝ) *
      (α (c.basis i) - a (c.basis i))) =
      -(∑ i ∈ c.fiberIndices, (c.basis.repr v i : ℝ) * ℓ (embed n (c.basis i))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hα i hi, mul_neg]
  change a v + _ - _ = a v - _
  rw [hsum]
  linarith only [he]

/-- Every endpoint divisor is strictly supported on the actual base fan. -/
theorem endpoint_isStrictSupport (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℝ) (ha : «Σ».IsStrictSupport a)
    {u : Lattice n} (hu : u ∈ R.positive) :
    c.baseFan.IsStrictSupport (c.baseWeight hR hN a (c.endpointWeight a u)) := by
  intro D hD
  have hDrays : D ⊆ c.baseFan.rays :=
    fun q hq => (c.baseFan.mem_rays_iff q).mpr ⟨D, hD, hq⟩
  let C := c.liftBaseCone hR hN D
  have hC : C ∈ «Σ».cones := c.liftBaseCone_mem hR hN hD
  have hnon : C ⊆ «Σ».rays \ R.positive := c.liftBaseCone_subset_nonfiber hR hN hDrays
  have huC : u ∉ C := fun hu' => (Finset.mem_sdiff.mp (hnon hu')).2 hu
  have hfill : R.positive.erase u ∪ C ∈ «Σ».cones :=
    R.fill_cone_with_positive_except hR hC (by rw [hN]; exact Finset.empty_subset _) hu huC
  obtain ⟨ℓ, hℓ, hstrict⟩ := ha _ hfill
  have hcoord := c.endpoint_support_coordinates hN a hu ℓ
    (fun v hv => hℓ v (Finset.mem_union_left _ hv))
  have hα (i : Fin n) (hi : i ∈ c.fiberIndices) :
      c.endpointWeight a u (c.basis i) - a (c.basis i) = -ℓ (embed n (c.basis i)) :=
    hcoord _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  refine ⟨ℓ.comp (coneQuotientSectionReal c.basis c.fiberIndices), ?_, ?_⟩
  · intro q hqD
    have hq := hDrays hqD
    have hvC : c.baseRayLift hR hN q ∈ C := Finset.mem_image.mpr ⟨q, hqD, rfl⟩
    have he := c.baseWeight_support_residual hR hN a (c.endpointWeight a u) ℓ hα hq
    have hv := hℓ _ (Finset.mem_union_right _ hvC)
    simp only [LinearMap.comp_apply]
    linarith only [he, hv]
  · intro q hq hqD
    have hv := c.baseRayLift_mem hR hN hq
    have hvnot : c.baseRayLift hR hN q ∉ R.positive.erase u ∪ C := by
      intro hm
      rcases Finset.mem_union.mp hm with hmP | hmC
      · exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_of_mem_erase hmP)
      · obtain ⟨q', hq'D, he⟩ := Finset.mem_image.mp hmC
        have heq := congrArg c.quotientLattice he
        rw [c.quotient_baseRayLift hR hN (hDrays hq'D),
          c.quotient_baseRayLift hR hN hq] at heq
        exact hqD (heq ▸ hq'D)
    have hlt := hstrict _ (Finset.mem_sdiff.mp hv).1 hvnot
    have he := c.baseWeight_support_residual hR hN a (c.endpointWeight a u) ℓ hα hq
    simp only [LinearMap.comp_apply]
    linarith only [he, hlt]

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanEndpoints
-- END ORIGINAL PaperVerification.ToricBundleFanEndpoints


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanFaces
section Source_ToricBundleFanFaces

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanEndpoints


-- original header: @[expose] public section
/-!
# Endpoint base polytopes are actual saturated faces

Every homogeneous slice is identified with its actual ambient fiber-slack
slice. At an endpoint, it is the face cut out by all other positive rays.
Together with the integral affine chart this proves the exact, saturated
lattice interpretation needed when passing edge lengths to the base.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} {R : «Σ».PrimitiveRelation}
  (c : R.BundleCoordinates)

theorem point_congr_on_positive (a α β : Lattice n → ℝ)
    (hαβ : ∀ v ∈ R.positive, α v = β v)
    (y : Ambient (n - c.fiberIndices.card)) : c.point a α y = c.point a β y := by
  have hf : c.fiberFunctional a α = c.fiberFunctional a β := by
    unfold fiberFunctional
    apply Finset.sum_congr rfl
    intro i hi
    rw [hαβ _ (c.fiber_subset_positive (Finset.mem_image.mpr ⟨i, hi, rfl⟩))]
  simp only [point, pointFunctional, hf]

def homogeneousSlice (a α : Lattice n → ℝ) : Set (Ambient n) :=
  {x ∈ «Σ».fanPolytope a | ∀ v ∈ R.positive, c.homogeneousWeight a x v = α v}

theorem point_image_basePolytope (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a α : Lattice n → ℝ)
    (hα : (∑ v ∈ R.positive, α v) = ∑ v ∈ R.positive, a v)
    (hα0 : ∀ v ∈ R.positive, 0 ≤ α v) :
    (c.point a α) '' c.baseFan.fanPolytope (c.baseWeight hR hN a α) =
      c.homogeneousSlice a α := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(c.point_mem_fanPolytope_iff hR hN a α hα y).mpr ⟨hα0, hy⟩, ?_⟩
    intro v hv
    rw [homogeneousWeight, c.point_pairing_positive hN a α hα y hv]
    ring
  · rintro ⟨hx, hweights⟩
    have he : c.point a α (c.basePoint x) = x := by
      rw [c.point_congr_on_positive a α (c.homogeneousWeight a x)
        (fun v hv => (hweights v hv).symm), c.point_homogeneousWeight_basePoint]
    refine ⟨c.basePoint x, ?_, he⟩
    apply ((c.point_mem_fanPolytope_iff hR hN a α hα (c.basePoint x)).mp ?_).2
    rw [he]
    exact hx

/-- The endpoint face is given by the literal supporting equalities on all
positive rays other than its vertex label. -/
def endpointFace (c : R.BundleCoordinates) (a : Lattice n → ℝ) (u : Lattice n) : Set (Ambient n) :=
  {x ∈ «Σ».fanPolytope a | ∀ v ∈ R.positive.erase u,
    (dotProductEquiv ℝ (Fin n) (embed n v)) x = -a v}

theorem endpointSlice_eq_face (hN : R.negative = ∅)
    (a : Lattice n → ℝ) {u : Lattice n} (hu : u ∈ R.positive) :
    c.homogeneousSlice a (c.endpointWeight a u) = c.endpointFace a u := by
  ext x
  constructor
  · rintro ⟨hx, hw⟩
    refine ⟨hx, ?_⟩
    intro v hv
    have he := hw v (Finset.mem_of_mem_erase hv)
    simp only [homogeneousWeight, endpointWeight, if_neg (Finset.mem_erase.mp hv).1] at he
    linarith
  · rintro ⟨hx, hface⟩
    refine ⟨hx, ?_⟩
    apply c.weights_eq_endpoint hu (c.homogeneousWeight_total hN a x)
    intro v hv
    rw [homogeneousWeight, hface v hv, add_neg_cancel]

theorem endpointFace_isExtreme (a : Lattice n → ℝ) (u : Lattice n) :
    IsExtreme ℝ («Σ».fanPolytope a) (c.endpointFace a u) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  refine ⟨hx, ?_⟩
  intro v hv
  have hvrays := R.primitive.1 (Finset.mem_of_mem_erase hv)
  have hxv := hx v hvrays
  have hyv := hy v hvrays
  have hzv := hz.2 v hv
  have hlin := congrArg (dotProductEquiv ℝ (Fin n) (embed n v) : Ambient n → ℝ) he
  simp only [map_add, map_smul, smul_eq_mul] at hlin
  have hy_slack : 0 ≤ (dotProductEquiv ℝ (Fin n) (embed n v)) y + a v := by
    linarith only [hyv]
  have hx_slack : 0 ≤ (dotProductEquiv ℝ (Fin n) (embed n v)) x + a v := by
    linarith only [hxv]
  have hnon := mul_nonneg hs.le hy_slack
  have hxnon := mul_nonneg hr.le hx_slack
  have hbalance :
      r * ((dotProductEquiv ℝ (Fin n) (embed n v)) x + a v) +
        s * ((dotProductEquiv ℝ (Fin n) (embed n v)) y + a v) = 0 := by
    calc
      r * ((dotProductEquiv ℝ (Fin n) (embed n v)) x + a v) +
          s * ((dotProductEquiv ℝ (Fin n) (embed n v)) y + a v) =
          (r * (dotProductEquiv ℝ (Fin n) (embed n v)) x +
            s * (dotProductEquiv ℝ (Fin n) (embed n v)) y) + (r + s) * a v := by ring
      _ = (dotProductEquiv ℝ (Fin n) (embed n v)) z + a v := by
        rw [hlin, hrs, one_mul]
      _ = 0 := by rw [hzv, neg_add_cancel]
  have hzero : r * ((dotProductEquiv ℝ (Fin n) (embed n v)) x + a v) = 0 := by
    linarith only [hxnon, hnon, hbalance]
  have hvzero := (mul_eq_zero.mp hzero).resolve_left hr.ne'
  linarith

theorem endpoint_image_is_face (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℝ)
    (hk : 0 ≤ ∑ v ∈ R.positive, a v) {u : Lattice n} (hu : u ∈ R.positive) :
    (c.point a (c.endpointWeight a u)) ''
      c.baseFan.fanPolytope (c.baseWeight hR hN a (c.endpointWeight a u)) =
        c.endpointFace a u := by
  rw [c.point_image_basePolytope hR hN a (c.endpointWeight a u)
    (c.endpointWeight_total a hu) (fun v hv => c.endpointWeight_nonneg a hk u v),
    c.endpointSlice_eq_face hN a hu]

def endpointIntegerWeight (c : R.BundleCoordinates) (a : Lattice n → ℤ) (u v : Lattice n) : ℤ :=
  if v = u then ∑ w ∈ R.positive, a w else 0

theorem endpointIntegerWeight_cast (a : Lattice n → ℤ) (u v : Lattice n) :
    (c.endpointIntegerWeight a u v : ℝ) = c.endpointWeight (fun w => (a w : ℝ)) u v := by
  simp only [endpointIntegerWeight, endpointWeight]
  split_ifs <;> push_cast <;> rfl

/-- The endpoint base polytope has exactly the saturated affine lattice
of the corresponding original face. -/
theorem endpointChart_image (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℤ)
    (hk : 0 ≤ ∑ v ∈ R.positive, a v) {u : Lattice n} (hu : u ∈ R.positive) :
    (c.fiberChart a (c.endpointIntegerWeight a u)).realMap ''
      c.baseFan.fanPolytope (c.baseWeight hR hN (fun v => (a v : ℝ))
        (c.endpointWeight (fun v => (a v : ℝ)) u)) =
      c.endpointFace (fun v => (a v : ℝ)) u := by
  have hmap : (c.fiberChart a (c.endpointIntegerWeight a u)).realMap =
      c.point (fun v => (a v : ℝ)) (c.endpointWeight (fun v => (a v : ℝ)) u) := by
    funext y
    rw [c.fiberChart_realMap]
    congr 1
    funext v
    exact c.endpointIntegerWeight_cast a u v
  rw [hmap]
  apply c.endpoint_image_is_face hR hN _ _ hu
  exact_mod_cast hk

theorem endpointChart_isExtreme (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (a : Lattice n → ℤ)
    (hk : 0 ≤ ∑ v ∈ R.positive, a v) {u : Lattice n} (hu : u ∈ R.positive) :
    IsExtreme ℝ («Σ».fanPolytope (fun v => (a v : ℝ)))
      ((c.fiberChart a (c.endpointIntegerWeight a u)).realMap ''
        c.baseFan.fanPolytope (c.baseWeight hR hN (fun v => (a v : ℝ))
          (c.endpointWeight (fun v => (a v : ℝ)) u))) := by
  rw [c.endpointChart_image hR hN a hk hu]
  exact c.endpointFace_isExtreme _ _

end SmoothCompleteFan.PrimitiveRelation.BundleCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanFaces
-- END ORIGINAL PaperVerification.ToricBundleFanFaces


-- BEGIN ORIGINAL PaperVerification.ToricOrthantEdges
section Source_ToricOrthantEdges

-- original header: module

-- original header: public import PaperVerification.ToricNormalFan
-- original header: public import Mathlib.Data.Finset.Max

-- original header: @[expose] public section

/-!
# Genuine edges at a supporting lattice orthant

Each coordinate ray is cut out as an actual face. A positive point on that
ray and compact finite generation give its other endpoint. Integrality of
that endpoint proves that its distance in a primitive basis direction is
a positive integer. Smoothness is not an input to these statements.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange PaperVerification.ToricVertexCone

variable {n : ℕ} (P : LatticePolytope n)

def coordinateRayFace (v : Ambient n) (b : Module.Basis (Fin n) ℝ (Ambient n))
    (i : Fin n) : Set (Ambient n) :=
  {x ∈ P.carrier | ∀ j, j ≠ i → b.repr (x - v) j = 0}

theorem coordinateRayFace_convex (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (i : Fin n) :
    Convex ℝ (P.coordinateRayFace v b i) := by
  intro x hx y hy r s hr hs hrs
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 hr hs hrs, ?_⟩
  intro j hji
  have hxj := hx.2 j hji
  have hyj := hy.2 j hji
  simp only [map_sub, Finsupp.sub_apply] at hxj hyj
  simp only [map_sub, map_add, map_smul, Finsupp.sub_apply,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [sub_eq_zero.mp hxj, sub_eq_zero.mp hyj, ← add_mul, hrs, one_mul, sub_self]

theorem coordinateRayFace_isExtreme (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (horthant : ∀ x ∈ P.carrier, ∀ j, 0 ≤ b.repr (x - v) j) (i : Fin n) :
    IsExtreme ℝ P.carrier (P.coordinateRayFace v b i) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  refine ⟨hx, ?_⟩
  intro j hji
  have hxj := horthant x hx j
  have hyj := horthant y hy j
  have hzj := hz.2 j hji
  have he' := congrArg (fun t => b.repr t j) he
  simp only [map_sub, Finsupp.sub_apply] at hxj hyj hzj ⊢
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at he'
  have hbalance : r * (b.repr x j - b.repr v j) +
      s * (b.repr y j - b.repr v j) = 0 := by
    calc
      r * (b.repr x j - b.repr v j) + s * (b.repr y j - b.repr v j) =
          (r * b.repr x j + s * b.repr y j) - (r + s) * b.repr v j := by ring
      _ = b.repr z j - b.repr v j := by rw [he', hrs, one_mul]
      _ = 0 := hzj
  have hrx := mul_nonneg hr.le hxj
  have hsy := mul_nonneg hs.le hyj
  have hzero : r * (b.repr x j - b.repr v j) = 0 := by
    linarith only [hbalance, hrx, hsy]
  exact (mul_eq_zero.mp hzero).resolve_left hr.ne'

theorem coordinateRayFace_point_eq (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (i : Fin n)
    {x : Ambient n} (hx : x ∈ P.coordinateRayFace v b i) :
    x = v + (b.repr (x - v) i) • b i := by
  apply b.ext_elem
  intro j
  by_cases hji : j = i
  · subst j
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, if_pos rfl, ite_true, smul_eq_mul, mul_one,
      map_sub, Finsupp.sub_apply]
    ring
  · have hz := hx.2 j hji
    simp only [map_sub, Finsupp.sub_apply] at hz
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, if_neg (Ne.symm hji), smul_eq_mul,
      mul_zero, add_zero]
    exact sub_eq_zero.mp hz

/-- Every primitive coordinate ray with a positive feasible point is an
actual edge of the given lattice polytope, with positive integral length. -/
theorem coordinateRayFace_eq_integral_edge
    (vZ : Lattice n) (hvZ : vZ ∈ P.generators)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (horthant : ∀ x ∈ P.carrier, ∀ j,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) j)
    (i : Fin n)
    (hpositive : ∃ ε : ℝ, 0 < ε ∧
      embed n vZ + ε • integralBasisReal b i ∈ P.carrier) :
    ∃ k : ℕ, 0 < k ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (k : ℤ) • b i)) ∧
      P.coordinateRayFace (embed n vZ) (integralBasisReal b) i =
        segment ℝ (embed n vZ) (embed n (vZ + (k : ℤ) • b i)) := by
  let v := embed n vZ
  let bR := integralBasisReal b
  let F := P.coordinateRayFace v bR i
  let S := P.generators.image (embed n)
  let T := faceGenerators S F
  let f : Ambient n →ₗ[ℝ] ℝ := bR.coord i
  have hcarrier : P.carrier = convexHull ℝ (S : Set (Ambient n)) := by
    simp only [carrier, S, Finset.coe_image]
  have hFconv : Convex ℝ F := P.coordinateRayFace_convex v bR i
  have hFext : IsExtreme ℝ P.carrier F :=
    P.coordinateRayFace_isExtreme v bR horthant i
  have hFhull : F = convexHull ℝ (T : Set (Ambient n)) := by
    apply convex_face_eq_convexHull_filter S F hFconv
    simpa only [← hcarrier] using hFext
  have hvP : v ∈ P.carrier := subset_convexHull ℝ _ ⟨vZ, hvZ, rfl⟩
  have hvF : v ∈ F := ⟨hvP, by intro j hji; simp⟩
  have hvT : v ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨vZ, hvZ, rfl⟩, hvF⟩
  obtain ⟨w, hwT, hmax⟩ := T.exists_max_image f ⟨v, hvT⟩
  have hwS : w ∈ S := (Finset.mem_filter.mp hwT).1
  have hwF : w ∈ F := (Finset.mem_filter.mp hwT).2
  have hbound (x : Ambient n) (hx : x ∈ F) : f x ≤ f w := by
    have hlow := linear_lower_bound_hull T (-f) (-f w)
      (fun z hz => neg_le_neg (hmax z hz)) x (hFhull ▸ hx)
    simpa only [LinearMap.neg_apply, neg_le_neg_iff] using hlow
  let «λ» := f (w - v)
  obtain ⟨ε, hε, hεP⟩ := hpositive
  have hεF : v + ε • bR i ∈ F := by
    refine ⟨hεP, ?_⟩
    intro j hji
    simp [bR, Module.Basis.repr_self_apply, hji, Ne.symm hji]
  have «hλ» : 0 < «λ» := by
    have hle := hbound _ hεF
    have he : f (v + ε • bR i) = f v + ε := by
      simp [f, Module.Basis.coord_apply]
    rw [he] at hle
    dsimp [«λ»]
    rw [map_sub]
    linarith
  have hwline : w = v + «λ» • bR i :=
    P.coordinateRayFace_point_eq v bR i hwF
  have hvw : v ≠ w := by
    intro he
    have hz : «λ» = 0 := by simp [«λ», ← he]
    linarith
  have hFsegment : F = segment ℝ v w := by
    apply Set.Subset.antisymm
    · intro x hx
      let μ := bR.repr (x - v) i
      have hμ0 : 0 ≤ μ := horthant x hx.1 i
      have «hμλ» : μ ≤ «λ» := by
        have hb := hbound x hx
        change f (x - v) ≤ f (w - v)
        simpa only [map_sub, sub_le_sub_iff_right] using hb
      have ht : μ / «λ» ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hμ0 «hλ».le, (div_le_one «hλ»).mpr «hμλ»⟩
      have hline : AffineMap.lineMap v w (μ / «λ») = x := by
        rw [AffineMap.lineMap_apply_module', hwline, add_sub_cancel_left,
          smul_smul, div_mul_cancel₀ _ «hλ».ne']
        simpa only [add_comm] using (P.coordinateRayFace_point_eq v bR i hx).symm
      simpa only [hline] using lineMap_mem_segment ℝ v w ht
    · exact hFconv.segment_subset hvF hwF
  obtain ⟨wZ, hwZ, hew⟩ := Finset.mem_image.mp hwS
  let z : ℤ := b.repr (wZ - vZ) i
  have «hλz» : «λ» = (z : ℝ) := by
    change (integralBasisReal b).repr (w - embed n vZ) i = _
    rw [← hew, ← map_sub, integralBasisReal_repr]
  have hz : 0 < z := by exact_mod_cast («hλz» ▸ «hλ»)
  let k : ℕ := z.toNat
  have hkZ : (k : ℤ) = z := Int.toNat_of_nonneg hz.le
  have hk : 0 < k := by exact_mod_cast (hkZ.symm ▸ hz)
  have hwendpoint : w = embed n (vZ + (k : ℤ) • b i) := by
    rw [hwline, «hλz», ← hkZ, map_add, embed_int_smul, integralBasisReal_apply]
  refine ⟨k, hk, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [← hwendpoint] using hvw
    · simpa only [hFsegment, hwendpoint] using hFext
  · simpa only [hwendpoint] using hFsegment

end PaperVerification.ToricGeometry.LatticePolytope
end
end Source_ToricOrthantEdges
-- END ORIGINAL PaperVerification.ToricOrthantEdges


-- BEGIN ORIGINAL PaperVerification.ToricFanPolytopeConstruction
section Source_ToricFanPolytopeConstruction

-- original header: module

-- original header: public import PaperVerification.ToricFanPolytopes
-- original header: public import PaperVerification.ToricOrthantEdges
-- original header: public import PaperVerification.ToricNormalConeRealization
-- original header: public import PaperVerification.ToricNormalConeAverages

-- original header: @[expose] public section

/-!
# An integral strictly convex support function gives its genuine polytope

The generators are literal integral Cartier points. Positive feasible points
on each dual basis ray prove full dimension and identify the actual edges;
none of these conclusions is stored as an assumption in the construction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem fullCones_nonempty (hpure : «Σ».IsPure) : «Σ».fullCones.Nonempty := by
  obtain ⟨t, ht, hzero⟩ := «Σ».complete 0
  obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
  exact ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩

/-- The actual integral solution of the primitive active equations. -/
def cartierLatticePoint (a : Lattice n → ℤ) (s : «Σ».fullCones) : Lattice n :=
  -∑ i, a («Σ».fullConeBasis s i) • integralDualBasis («Σ».fullConeBasis s) i

theorem embed_cartierLatticePoint (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    embed n («Σ».cartierLatticePoint a s) = «Σ».cartierPoint (fun u => (a u : ℝ)) s := by
  simp only [cartierLatticePoint, cartierPoint, map_neg, map_sum,
    embed_int_smul, integralBasisReal_apply]

theorem cartierPoint_support_eq_of_mem (a : Lattice n → ℝ) (s : «Σ».fullCones)
    {u : Lattice n} (hu : u ∈ (s : Finset (Lattice n))) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) = -a u := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hu)
  exact «Σ».cartierPoint_active a s i

/-- Strict support means literal strict inequality at every inactive ray
of the actual Cartier point. -/
theorem cartierPoint_support_lt_of_not_mem {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) (s : «Σ».fullCones)
    {u : Lattice n} (hu : u ∈ «Σ».rays) (hus : u ∉ (s : Finset (Lattice n))) :
    -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
  obtain ⟨ℓ, he, hlt⟩ := ha s («Σ».fullCones_mem s)
  let q : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) («Σ».cartierPoint a s))
  have hq (z : Lattice n) :
      q (embed n z) = -(dotProductEquiv ℝ (Fin n) (embed n z)) («Σ».cartierPoint a s) := by
    change -(«Σ».cartierPoint a s ⬝ᵥ embed n z) =
      -(embed n z ⬝ᵥ «Σ».cartierPoint a s)
    rw [dotProduct_comm]
  have hℓq : ℓ = q := by
    apply (integralBasisReal («Σ».fullConeBasis s)).ext
    intro i
    have hi : «Σ».fullConeBasis s i ∈ (s : Finset (Lattice n)) := by
      rw [«Σ».fullConeBasis_ray_set]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [integralBasisReal_apply, he _ hi, hq,
      «Σ».cartierPoint_support_eq_of_mem a s hi, neg_neg]
  have h := hlt u hu hus
  rw [hℓq, hq] at h
  linarith

theorem cartierPoint_orthant {a : Lattice n → ℝ} (s : «Σ».fullCones)
    {x : Ambient n} (hx : x ∈ «Σ».fanPolytope a) (i : Fin n) :
    0 ≤ («Σ».cartierBasis s).repr (x - «Σ».cartierPoint a s) i := by
  rw [← «Σ».activeRay_dual s i, map_sub, «Σ».cartierPoint_active]
  exact sub_nonneg.mpr (hx («Σ».activeRay s i) («Σ».activeRay s i).property)

/-- Every dual coordinate ray has a strictly positive feasible initial
segment. A finite common perturbation handles all inactive facets. -/
theorem exists_positive_axis_point {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) (s : «Σ».fullCones) (i : Fin n) :
    ∃ ε : ℝ, 0 < ε ∧
      «Σ».cartierPoint a s + ε • «Σ».cartierBasis s i ∈ «Σ».fanPolytope a := by
  let v := «Σ».cartierPoint a s
  let e := «Σ».cartierBasis s i
  let I := «Σ».rays \ (s : Finset (Lattice n))
  let f : Lattice n → ℝ := fun u => a u + (dotProductEquiv ℝ (Fin n) (embed n u)) v
  let g : Lattice n → ℝ := fun u => (dotProductEquiv ℝ (Fin n) (embed n u)) e
  have hf (u : Lattice n) (hu : u ∈ I) : 0 < f u := by
    obtain ⟨hur, hus⟩ := Finset.mem_sdiff.mp hu
    have h := «Σ».cartierPoint_support_lt_of_not_mem ha s hur hus
    dsimp [f, v]
    linarith
  obtain ⟨ε, hε, hsmall⟩ := finite_strict_perturbation I f g hf
  refine ⟨ε, hε, ?_⟩
  intro u hu
  by_cases hus : u ∈ (s : Finset (Lattice n))
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hus)
    have heq := «Σ».cartierPoint_active a s j
    have hpair : (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s j))) e =
        if i = j then 1 else 0 := by
      rw [show «Σ».fullConeBasis s j = («Σ».activeRay s j : Lattice n) from rfl,
        «Σ».activeRay_dual]
      exact Module.Basis.repr_self_apply _ _ _
    change -a («Σ».fullConeBasis s j) ≤ _
    rw [map_add, map_smul, hpair]
    change -a («Σ».fullConeBasis s j) ≤
      (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s j))) v +
        ε * (if i = j then 1 else 0)
    change (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s j))) v =
      -a («Σ».fullConeBasis s j) at heq
    rw [heq]
    split_ifs <;> nlinarith
  · have h := hsmall u (Finset.mem_sdiff.mpr ⟨hu, hus⟩)
    dsimp [f, g] at h
    rw [map_add, map_smul]
    change -a u ≤ (dotProductEquiv ℝ (Fin n) (embed n u)) v + ε * g u
    dsimp [g]
    linarith

/-- The actual halfspace polytope has full affine span. This includes
dimension zero and does not presume a previously constructed polytope. -/
theorem affineSpan_fanPolytope_eq_top (hpure : «Σ».IsPure)
    {a : Lattice n → ℝ} (ha : «Σ».IsStrictSupport a) :
    affineSpan ℝ («Σ».fanPolytope a) = ⊤ := by
  obtain ⟨s, hs⟩ := «Σ».fullCones_nonempty hpure
  let s' : «Σ».fullCones := ⟨s, hs⟩
  let v := «Σ».cartierPoint a s'
  let b := «Σ».cartierBasis s'
  let A := affineSpan ℝ («Σ».fanPolytope a)
  have hv : v ∈ A := subset_affineSpan ℝ _
    («Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) s')
  have hb (i : Fin n) : b i ∈ A.direction := by
    obtain ⟨ε, hε, hpoint⟩ := «Σ».exists_positive_axis_point ha s' i
    have hd := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ _ hpoint) hv
    have hd' : ε • b i ∈ A.direction := by
      simpa only [v, b, A, vsub_eq_sub, add_sub_cancel_left] using hd
    have hh := A.direction.smul_mem ε⁻¹ hd'
    simpa only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] using hh
  have hdir (x : Ambient n) : x ∈ A.direction := by
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ (fun i _ => A.direction.smul_mem _ (hb i))
  apply top_unique
  intro x hx
  have hh := AffineSubspace.vadd_mem_of_mem_direction (hdir (x - v)) hv
  simpa only [vadd_eq_add, sub_add_cancel] using hh

def supportGenerators (a : Lattice n → ℤ) : Finset (Lattice n) :=
  Finset.univ.image («Σ».cartierLatticePoint a)

theorem supportGenerators_nonempty (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    («Σ».supportGenerators a).Nonempty := by
  obtain ⟨s, hs⟩ := «Σ».fullCones_nonempty hpure
  exact ⟨«Σ».cartierLatticePoint a ⟨s, hs⟩,
    Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_univ _, rfl⟩⟩

theorem embed_supportGenerators (a : Lattice n → ℤ) :
    (embed n) '' («Σ».supportGenerators a : Set (Lattice n)) =
      Set.range («Σ».cartierPoint (fun u => (a u : ℝ))) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨s, («Σ».embed_cartierLatticePoint a s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨«Σ».cartierLatticePoint a s,
      Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩,
      «Σ».embed_cartierLatticePoint a s⟩

/-- A literal full-dimensional lattice polytope, generated by its
integral Cartier points. Smoothness is proved separately below. -/
def supportLatticePolytope (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) : LatticePolytope n where
  generators := «Σ».supportGenerators a
  nonempty := «Σ».supportGenerators_nonempty hpure a
  fullDimensional := by
    rw [«Σ».embed_supportGenerators,
      ← «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]
    exact «Σ».affineSpan_fanPolytope_eq_top hpure ha

theorem supportLatticePolytope_carrier (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).carrier =
      «Σ».fanPolytope (fun u => (a u : ℝ)) := by
  change convexHull ℝ ((embed n) '' («Σ».supportGenerators a : Set (Lattice n))) = _
  rw [«Σ».embed_supportGenerators,
    ← «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricFanPolytopeConstruction
-- END ORIGINAL PaperVerification.ToricFanPolytopeConstruction


-- BEGIN ORIGINAL PaperVerification.ToricFanPolytopeSmoothness
section Source_ToricFanPolytopeSmoothness

-- original header: module

-- original header: public import PaperVerification.ToricFanPolytopeConstruction
-- original header: public import PaperVerification.ToricFanConstruction

-- original header: @[expose] public section

/-!
# Smoothness and the exact normal fan of the support polytope

An arbitrary actual incident edge is forced onto one dual coordinate ray
by the minimal face of its endpoints. This rules out omitted incident
edges. All normal cones, including the zero cone and proper face cones,
are then identified with the original finite fan.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def supportInequalities (a : Lattice n → ℝ) :
    AffineInequalities «Σ».rays (Ambient n) :=
  AffineInequalities.ofSlack (fun u =>
    (dotProductEquiv ℝ (Fin n) (embed n u)).toAffineMap +
      AffineMap.const ℝ (Ambient n) (a u))

theorem supportInequalities_slack (a : Lattice n → ℝ) (u : «Σ».rays)
    (x : Ambient n) :
    («Σ».supportInequalities a).slack u x =
      (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u := rfl

theorem supportInequalities_region (a : Lattice n → ℝ) :
    («Σ».supportInequalities a).region = «Σ».fanPolytope a := by
  ext x
  change (∀ u : «Σ».rays, 0 ≤
    (dotProductEquiv ℝ (Fin n) (embed n u)) x + a u) ↔ _
  constructor
  · intro h u hu
    have hh := h ⟨u, hu⟩
    change -a u ≤ _
    linarith
  · intro h u
    have hh := h u u.property
    change -a u ≤ _ at hh
    linarith

/-- Any actual edge incident to a Cartier vertex lies on exactly one of
the primitive dual coordinate rays. This conclusion is derived from the
actual finite halfspace face, not assumed as fan combinatorics. -/
theorem support_polytope_edge_has_coordinate_direction
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones)
    (w : Ambient n)
    (hedge : («Σ».supportLatticePolytope hpure a ha).IsEdge
      («Σ».cartierPoint (fun u => (a u : ℝ)) s) w) :
    ∃ i : Fin n, w ∈ («Σ».supportLatticePolytope hpure a ha).coordinateRayFace
      («Σ».cartierPoint (fun u => (a u : ℝ)) s) («Σ».cartierBasis s) i := by
  let P := «Σ».supportLatticePolytope hpure a ha
  let aR : Lattice n → ℝ := fun u => (a u : ℝ)
  let v := «Σ».cartierPoint aR s
  let b := «Σ».cartierBasis s
  let H := «Σ».supportInequalities aR
  have hPH : P.carrier = H.region := by
    rw [«Σ».supportInequalities_region, «Σ».supportLatticePolytope_carrier]
  obtain ⟨hvP, hwP⟩ := P.edge_endpoints_extreme hedge
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ b.repr (x - v) j := by
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have hpositive : ∃ i : Fin n, 0 < b.repr (w - v) i := by
    by_contra hn
    push_neg at hn
    have heq : w = v := by
      apply b.ext_elem
      intro i
      have hz := le_antisymm (hn i) (horthant w hwP.1 i)
      simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using hz
    exact hedge.1 heq.symm
  obtain ⟨i, hi⟩ := hpositive
  obtain ⟨ε, hε, hpoint⟩ := «Σ».exists_positive_axis_point ha s i
  let z := v + ε • b i
  have hzH : z ∈ H.region := by
    rw [«Σ».supportInequalities_region]
    exact hpoint
  have hzface : z ∈ H.face (H.jointZeros v w) := by
    refine ⟨hzH, ?_⟩
    intro u hu
    have huv := hu.1
    have huw := hu.2
    have hucone : (u : Lattice n) ∈ (s : Finset (Lattice n)) := by
      by_contra hus
      have hh := «Σ».cartierPoint_support_lt_of_not_mem ha s u.property hus
      rw [«Σ».supportInequalities_slack] at huv
      change (dotProductEquiv ℝ (Fin n) (embed n u)) v + aR u = 0 at huv
      linarith
    obtain ⟨j, hj, hju⟩ := Finset.mem_image.mp ((«Σ».fullConeBasis_ray_set s) ▸ hucone)
    have hjne : j ≠ i := by
      intro hji
      subst j
      have he : b.repr (w - v) i = 0 := by
        rw [← «Σ».activeRay_dual s i, map_sub, «Σ».cartierPoint_active]
        change (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s i))) w -
          -aR («Σ».fullConeBasis s i) = 0
        rw [hju]
        simpa only [H, «Σ».supportInequalities_slack, sub_neg_eq_add] using huw
      linarith
    rw [«Σ».supportInequalities_slack]
    have hp : (dotProductEquiv ℝ (Fin n) (embed n u)) (b i) = 0 := by
      rw [← hju]
      change (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s j))) (b i) = 0
      rw [«Σ».activeRay_dual]
      simp [b, Module.Basis.repr_self_apply, hjne, Ne.symm hjne]
    change (dotProductEquiv ℝ (Fin n) (embed n u)) (v + ε • b i) + aR u = 0
    rw [map_add, map_smul, hp, smul_zero, add_zero]
    exact huv
  have hmin := H.jointFace_minimal (hPH ▸ hvP.1) (hPH ▸ hwP.1)
    (convex_segment v w) (by simpa only [← hPH] using hedge.2)
    (left_mem_segment ℝ v w) (right_mem_segment ℝ v w)
  have hzseg : z ∈ segment ℝ v w := hmin hzface
  obtain ⟨r, t, hr, ht, hrt, hline⟩ := hzseg
  have hcoords (j : Fin n) :
      ε * (if i = j then 1 else 0) = t * b.repr (w - v) j := by
    have he := congrArg (fun x => b.repr x j) hline
    change b.repr (r • v + t • w) j = b.repr (v + ε • b i) j at he
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, smul_eq_mul] at he
    simp only [map_sub, Finsupp.sub_apply]
    have hbase : (r + t) * b.repr v j = b.repr v j := by rw [hrt, one_mul]
    nlinarith only [he, hbase]
  have htne : t ≠ 0 := by
    intro he
    have hh := hcoords i
    simp [he] at hh
    linarith
  refine ⟨i, hwP.1, ?_⟩
  intro j hji
  have he := hcoords j
  rw [if_neg (Ne.symm hji), mul_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left htne

/-- All coordinate-ray faces have actual positive integral endpoints. -/
theorem support_polytope_coordinate_edges
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones) :
    ∃ lengths : Fin n → ℕ, ∀ i,
      0 < lengths i ∧
      («Σ».supportLatticePolytope hpure a ha).IsEdge
        («Σ».cartierPoint (fun u => (a u : ℝ)) s)
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) ∧
      («Σ».supportLatticePolytope hpure a ha).coordinateRayFace
        («Σ».cartierPoint (fun u => (a u : ℝ)) s) («Σ».cartierBasis s) i =
        segment ℝ («Σ».cartierPoint (fun u => (a u : ℝ)) s)
          (embed n («Σ».cartierLatticePoint a s +
            (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  have hvgen : «Σ».cartierLatticePoint a s ∈ P.generators :=
    Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ («Σ».cartierBasis s).repr (x - embed n («Σ».cartierLatticePoint a s)) j := by
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have hex (i : Fin n) := P.coordinateRayFace_eq_integral_edge
    («Σ».cartierLatticePoint a s) hvgen (integralDualBasis («Σ».fullConeBasis s)) horthant i
    (by simpa only [P, cartierBasis, «Σ».embed_cartierLatticePoint,
      «Σ».supportLatticePolytope_carrier] using «Σ».exists_positive_axis_point ha s i)
  choose lengths hlengths using hex
  refine ⟨lengths, ?_⟩
  intro i
  simpa only [P, cartierBasis, «Σ».embed_cartierLatticePoint] using hlengths i

/-- The resulting lattice polytope is smooth in the literal all-edges
definition. Both existence and completeness of the incident basis edges
have been proved independently. -/
theorem supportLatticePolytope_smooth
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).Smooth := by
  let P := «Σ».supportLatticePolytope hpure a ha
  let aR : Lattice n → ℝ := fun u => (a u : ℝ)
  intro v hv
  have hP : P.carrier = convexHull ℝ (Set.range («Σ».cartierPoint aR)) := by
    rw [«Σ».supportLatticePolytope_carrier,
      «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha)]
  have hv' : v ∈ (convexHull ℝ (Set.range («Σ».cartierPoint aR))).extremePoints ℝ :=
    hP ▸ hv
  obtain ⟨s, rfl⟩ := extremePoints_convexHull_subset hv'
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  refine ⟨«Σ».cartierLatticePoint a s, integralDualBasis («Σ».fullConeBasis s), lengths,
    «Σ».embed_cartierLatticePoint a s, ?_, ?_⟩
  · intro i
    exact ⟨(hlengths i).1, (hlengths i).2.1⟩
  · intro w hw
    obtain ⟨i, hi⟩ := «Σ».support_polytope_edge_has_coordinate_direction hpure a ha s w hw
    have hwseg := (hlengths i).2.2 ▸ hi
    have hverts := P.edge_endpoints_extreme hw
    have hend := (P.edge_endpoints_extreme (hlengths i).2.1).2.1
    rcases (mem_extremePoints_iff_forall_segment.mp hverts.2).2
      _ hverts.1.1 _ hend hwseg with hvw | hew
    · exact (hw.1 hvw).elim
    · exact ⟨i, hew.symm⟩

/-- The actual normal cone at each integral Cartier vertex is its full
original fan cone, with no rescaling or missing primitive ray. -/
theorem supportLatticePolytope_cartier_normalCone
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) (s : «Σ».fullCones) :
    («Σ».supportLatticePolytope hpure a ha).normalCone
      («Σ».cartierPoint (fun u => (a u : ℝ)) s) =
      (latticeRayCone (s : Finset (Lattice n)) : Set (Ambient n)) := by
  let P := «Σ».supportLatticePolytope hpure a ha
  obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s
  have hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n («Σ».cartierLatticePoint a s))
        (embed n («Σ».cartierLatticePoint a s +
          (lengths i : ℤ) • integralDualBasis («Σ».fullConeBasis s) i)) := by
    intro i
    simpa only [«Σ».embed_cartierLatticePoint] using
      ⟨(hlengths i).1, (hlengths i).2.1⟩
  have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
      0 ≤ («Σ».cartierBasis s).repr (x - embed n («Σ».cartierLatticePoint a s)) j := by
    rw [«Σ».embed_cartierLatticePoint]
    exact «Σ».cartierPoint_orthant s ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
  have heq := P.normalCone_eq_latticeRayCone («Σ».cartierLatticePoint a s)
    (integralDualBasis («Σ».fullConeBasis s)) lengths hedges horthant
  simpa only [«Σ».embed_cartierLatticePoint, integralDualBasis_involutive,
    ← «Σ».fullConeBasis_ray_set] using heq

/-- Equality of the entire actual normal fan, including all proper cones. -/
theorem supportLatticePolytope_normalFan
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    («Σ».supportLatticePolytope hpure a ha).normalFan = «Σ».realCones := by
  let P := «Σ».supportLatticePolytope hpure a ha
  let aR : Lattice n → ℝ := fun u => (a u : ℝ)
  have hnormal := «Σ».supportLatticePolytope_cartier_normalCone hpure a ha
  have hv (s : «Σ».fullCones) : «Σ».cartierPoint aR s ∈ P.carrier := by
    rw [«Σ».supportLatticePolytope_carrier]
    exact «Σ».cartierPoint_mem_of_nef (IsStrictSupport.isNef «Σ» ha) s
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hhull : x ∈ convexHull ℝ (Set.range («Σ».cartierPoint aR)) := by
      rw [← «Σ».fanPolytope_eq_convexHull_cartier hpure _ (IsStrictSupport.isNef «Σ» ha),
        ← «Σ».supportLatticePolytope_carrier hpure a ha]
      exact hx
    obtain ⟨p, hp, hpsum, hpm⟩ :=
      PaperVerification.Toric.exists_probability_of_mem_convexHull_range
        («Σ».cartierPoint aR) hhull
    let K := Finset.univ.filter (fun s : «Σ».fullCones => 0 < p s)
    have hK : K.Nonempty := by
      have hpos : 0 < ∑ s, p s := by rw [hpsum]; norm_num
      obtain ⟨s, hs, hps⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ => hp s)).mp hpos
      exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hps⟩⟩
    obtain ⟨t, ht, hspec⟩ := «Σ».exists_cone_finite_intersection K
      (fun s : «Σ».fullCones => (s : Finset (Lattice n))) hK
      (fun s _ => «Σ».fullCones_mem s)
    refine ⟨t, ht, ?_⟩
    ext u
    rw [← hpm, P.mem_normalCone_convex_average («Σ».cartierPoint aR) p hv hp hpsum u]
    change (∀ s : «Σ».fullCones, 0 < p s → u ∈ P.normalCone («Σ».cartierPoint aR s)) ↔
      u ∈ latticeRayCone t
    rw [hspec u]
    simp only [P, aR, hnormal, K, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    let d := «Σ».fullConeBasis s'
    let I := basisRayIndices d t
    have htfull : t ⊆ Finset.univ.image d := by
      rw [← «Σ».fullConeBasis_ray_set s']
      exact hts
    have hI : I.image d = t := image_basisRayIndices d t htfull
    obtain ⟨lengths, hlengths⟩ := «Σ».support_polytope_coordinate_edges hpure a ha s'
    have hedges : ∀ i, 0 < lengths i ∧
        P.IsEdge (embed n («Σ».cartierLatticePoint a s'))
          (embed n («Σ».cartierLatticePoint a s' + (lengths i : ℤ) • integralDualBasis d i)) := by
      intro i
      simpa only [«Σ».embed_cartierLatticePoint] using
        ⟨(hlengths i).1, (hlengths i).2.1⟩
    have horthant (x : Ambient n) (hx : x ∈ P.carrier) (j : Fin n) :
        0 ≤ (integralBasisReal (integralDualBasis d)).repr
          (x - embed n («Σ».cartierLatticePoint a s')) j := by
      rw [«Σ».embed_cartierLatticePoint]
      exact «Σ».cartierPoint_orthant s' ((«Σ».supportLatticePolytope_carrier hpure a ha) ▸ hx) j
    have hsub := P.subbasis_mem_normalFan («Σ».cartierLatticePoint a s')
      (by simpa only [«Σ».embed_cartierLatticePoint] using hv s')
      (integralDualBasis d) lengths hedges horthant I
    simpa only [integralDualBasis_involutive, hI] using hsub

/-- The complete reverse dictionary required by dimension induction. -/
theorem exists_smooth_latticePolytope_of_integral_strictSupport
    (hpure : «Σ».IsPure) (a : Lattice n → ℤ)
    (ha : «Σ».IsStrictSupport (fun u => (a u : ℝ))) :
    ∃ P : LatticePolytope n,
      P.carrier = «Σ».fanPolytope (fun u => (a u : ℝ)) ∧
      P.Smooth ∧ P.normalFan = «Σ».realCones := by
  exact ⟨«Σ».supportLatticePolytope hpure a ha,
    «Σ».supportLatticePolytope_carrier hpure a ha,
    «Σ».supportLatticePolytope_smooth hpure a ha,
    «Σ».supportLatticePolytope_normalFan hpure a ha⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
end Source_ToricFanPolytopeSmoothness
-- END ORIGINAL PaperVerification.ToricFanPolytopeSmoothness


-- BEGIN ORIGINAL PaperVerification.ToricChartSmoothness
section Source_ToricChartSmoothness

-- original header: module
-- original header: public import PaperVerification.ToricIntegralAffine
-- original header: @[expose] public section
/-!
# Smoothness transferred from saturated local face coordinates

At each face vertex, one may choose a different saturated coordinate chart.
The integral transition map converts its standard primitive edge basis into a
basis in any fixed chart, proving the literal global smoothness definition.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricExchange

/-- Standard primitive edge charts at every actual vertex prove that any
fixed saturated lattice-polytope chart of the same set is smooth. -/
theorem smooth_of_local_saturated_charts {d n : ℕ} (F : Set (Ambient n))
    (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n)
    (heF : e.realMap '' Q.carrier = F)
    (hlocal : ∀ v ∈ F.extremePoints ℝ,
      ∃ (k : ℕ) (R : LatticePolytope k) (f : IntegralAffineEmbedding k n)
        (lengths : Fin k → ℕ),
        f.realMap 0 = v ∧ f.realMap '' R.carrier = F ∧
        (∀ i, 0 < lengths i ∧
          R.IsEdge 0 (embed k ((lengths i : ℤ) • Pi.basisFun ℤ (Fin k) i))) ∧
        (∀ w, R.IsEdge 0 w →
          ∃ i, w = embed k ((lengths i : ℤ) • Pi.basisFun ℤ (Fin k) i))) :
    Q.Smooth := by
  classical
  intro v hv
  have hvF : e.realMap v ∈ F.extremePoints ℝ := by
    rw [← heF]
    exact affine_mem_extremePoints_image e.realMap e.realMap_injective hv
  obtain ⟨k, R, f, lengths, hf0, hfF, hedge, hall⟩ := hlocal (e.realMap v) hvF
  obtain ⟨z0, hz0Q, hz0⟩ := Q.extreme_integral hv
  have hlinearRange : Set.range e.realLinear = Set.range f.realLinear :=
    e.linear_range_eq_of_affine_range_eq f
      (e.realMap_range_eq_of_image_eq f Q R (heF.trans hfF.symm))
  let T : Lattice k ≃ₗ[ℤ] Lattice d := e.changeLinear f hlinearRange
  let b0 : Module.Basis (Fin k) ℤ (Lattice d) := (Pi.basisFun ℤ (Fin k)).map T
  let index : Fin k ≃ Fin d := b0.indexEquiv (Pi.basisFun ℤ (Fin d))
  let b : Module.Basis (Fin d) ℤ (Lattice d) := b0.reindex index
  have hb (i : Fin d) : b i = T (Pi.basisFun ℤ (Fin k) (index.symm i)) := by
    simp [b, b0]
  have horigin : e.latticeMap z0 = f.origin := by
    apply embed_injective n
    rw [e.embed_latticeMap, hz0, ← hf0]
    simp [IntegralAffineEmbedding.realMap_apply]
  have hpoint (z : Lattice k) :
      e.realMap (embed d (z0 + T z)) = f.realMap (embed k z) :=
    e.realMap_changeLinear f hlinearRange z0 horigin z
  refine ⟨z0, b, fun i => lengths (index.symm i), hz0, ?_, ?_⟩
  · intro i
    let j : Fin k := index.symm i
    refine ⟨(hedge j).1, ?_⟩
    have hmap : e.realMap (embed d (z0 + (lengths j : ℤ) • b i)) =
        f.realMap (embed k ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)) := by
      rw [hb]
      rw [← T.map_smul]
      exact hpoint ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)
    exact (e.edge_transfer_iff f Q R (heF.trans hfF.symm)
      v (embed d (z0 + (lengths j : ℤ) • b i))
      0 (embed k ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)) hf0.symm hmap).mpr
      (hedge j).2
  · intro w hw
    have hwF : e.realMap w ∈ F := by
      rw [← heF]
      exact ⟨w, (Q.edge_endpoints_extreme hw).2.1, rfl⟩
    rw [← hfF] at hwF
    obtain ⟨u, huR, hu⟩ := hwF
    have huEdge : R.IsEdge 0 u :=
      (e.edge_transfer_iff f Q R (heF.trans hfF.symm) v w 0 u hf0.symm hu.symm).mp hw
    obtain ⟨j, hj⟩ := hall u huEdge
    refine ⟨index j, ?_⟩
    apply e.realMap_injective
    rw [← hu, hj]
    have he := hpoint ((lengths j : ℤ) • Pi.basisFun ℤ (Fin k) j)
    simpa only [hb, Equiv.symm_apply_apply, LinearEquiv.map_smul] using he.symm

end PaperVerification.ToricGeometry
end
end Source_ToricChartSmoothness
-- END ORIGINAL PaperVerification.ToricChartSmoothness


-- BEGIN ORIGINAL PaperVerification.ToricFaceCoordinates
section Source_ToricFaceCoordinates

-- original header: module
-- original header: public import PaperVerification.ToricNormalFan
-- original header: public import PaperVerification.ToricIntegralAffine
-- original header: public import Mathlib.LinearAlgebra.LinearIndependent.Defs
-- original header: public import Mathlib.Data.Finset.Sort
-- original header: @[expose] public section
/-!
# Saturated coordinates on a subset of an integral basis

Selecting any subset of a genuine integral basis gives an injective integral
affine coordinate map whose real image has exactly the induced lattice.
These maps will be used as actual coordinates on faces of smooth polytopes.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators

section BasisSelection

variable {R E ι κ : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [Fintype κ]

def selectedBasisMap (b : Module.Basis ι R E) (a : κ ↪ ι) : (κ → R) →ₗ[R] E :=
  Fintype.linearCombination R (fun i => b (a i))

@[simp] theorem selectedBasisMap_apply (b : Module.Basis ι R E) (a : κ ↪ ι) (x : κ → R) :
    selectedBasisMap b a x = ∑ i, x i • b (a i) := rfl

@[simp] theorem selectedBasisMap_coordinate (b : Module.Basis ι R E)
    (a : κ ↪ ι) (x : κ → R) (i : κ) :
    b.repr (selectedBasisMap b a x) (a i) = x i := by
  classical
  simp [selectedBasisMap_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, Finsupp.single_apply,
    a.injective.eq_iff, smul_eq_mul]

theorem selectedBasisMap_coordinate_eq_zero (b : Module.Basis ι R E)
    (a : κ ↪ ι) (x : κ → R) (j : ι) (hj : j ∉ Set.range a) :
    b.repr (selectedBasisMap b a x) j = 0 := by
  classical
  have hne (i : κ) : a i ≠ j := fun hi => hj ⟨i, hi⟩
  simp [selectedBasisMap_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, hne, smul_eq_mul]

theorem selectedBasisMap_injective (b : Module.Basis ι R E) (a : κ ↪ ι) :
    Function.Injective (selectedBasisMap b a) := by
  intro x y hxy
  funext i
  have h := congrArg (fun z => b.repr z (a i)) hxy
  simpa only [selectedBasisMap_coordinate] using h

/-- A selected-basis subspace is exactly the locus where all omitted basis
coordinates vanish. -/
theorem mem_range_selectedBasisMap_iff (b : Module.Basis ι R E) (a : κ ↪ ι) (x : E) :
    x ∈ Set.range (selectedBasisMap b a) ↔
      ∀ j ∉ Set.range a, b.repr x j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ j hj
    exact selectedBasisMap_coordinate_eq_zero b a t j hj
  · intro hx
    refine ⟨fun i => b.repr x (a i), ?_⟩
    apply b.ext_elem
    intro j
    by_cases hj : j ∈ Set.range a
    · obtain ⟨i, rfl⟩ := hj
      exact selectedBasisMap_coordinate b a (fun i => b.repr x (a i)) i
    · rw [selectedBasisMap_coordinate_eq_zero b a _ j hj, hx j hj]

theorem selectedBasisMap_repr_restrict (b : Module.Basis ι R E) (a : κ ↪ ι) (x : E)
    (hx : ∀ j ∉ Set.range a, b.repr x j = 0) :
    selectedBasisMap b a (fun i => b.repr x (a i)) = x := by
  obtain ⟨w, hw⟩ := (mem_range_selectedBasisMap_iff b a x).mpr hx
  have hcoord : w = fun i => b.repr x (a i) := by
    funext i
    rw [← hw, selectedBasisMap_coordinate]
  rw [← hcoord]
  exact hw

@[simp] theorem selectedBasisMap_single (b : Module.Basis ι R E) (a : κ ↪ ι)
    [DecidableEq κ] (i : κ) (r : R) :
    selectedBasisMap b a (Pi.single i r) = r • b (a i) :=
  Fintype.linearCombination_apply_single R (fun k => b (a k)) i r

end BasisSelection

/-- An integral selected-basis combination embeds as the identical real combination. -/
theorem embed_selectedBasisMap {d n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (z : Lattice d) :
    embed n (selectedBasisMap b a z) =
      selectedBasisMap (integralBasisReal b) a (embed d z) := by
  ext j
  simp [selectedBasisMap_apply, map_sum, integralBasisReal_apply, embed,
    Finset.sum_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]

/-- Selecting an integral basis subset and an integral origin defines an actual
saturated integral affine coordinate embedding. -/
def selectedBasisChart {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) :
    IntegralAffineEmbedding d n where
  origin := v
  linear := (selectedBasisMap b a).toAddMonoidHom
  realLinear := selectedBasisMap (integralBasisReal b) a
  injective := selectedBasisMap_injective _ _
  compatible := embed_selectedBasisMap b a
  saturated := by
    intro z hz
    have hzero := (mem_range_selectedBasisMap_iff (integralBasisReal b) a (embed n z)).mp hz
    have hzeroZ (j : Fin n) (hj : j ∉ Set.range a) : b.repr z j = 0 := by
      have h := hzero j hj
      rw [integralBasisReal_repr] at h
      exact Int.cast_eq_zero.mp h
    obtain ⟨w, hw⟩ := (mem_range_selectedBasisMap_iff b a z).mpr hzeroZ
    exact ⟨w, hw⟩

@[simp] theorem selectedBasisChart_realMap {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (x : Ambient d) :
    (selectedBasisChart v b a).realMap x =
      embed n v + ∑ i, x i • integralBasisReal b (a i) := rfl

@[simp] theorem selectedBasisChart_latticeMap {d n : ℕ} (v : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (a : Fin d ↪ Fin n) (x : Lattice d) :
    (selectedBasisChart v b a).latticeMap x = v + ∑ i, x i • b (a i) := rfl

end PaperVerification.ToricGeometry
end
end Source_ToricFaceCoordinates
-- END ORIGINAL PaperVerification.ToricFaceCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricFaceInheritance
section Source_ToricFaceInheritance

-- original header: module
-- original header: public import PaperVerification.ToricFaceCoordinates
-- original header: public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
-- original header: @[expose] public section
/-!
# Face coordinates for smooth lattice polytopes

The coordinate support of a face is determined by the incident edge rays that
remain in that face. This gives a coordinate sublattice of an actual integral
basis, hence a saturated lattice, without assuming a face-inheritance theorem.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical
open Set
open PaperVerification.ToricExchange

section AffineCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem affine_apply_add_smul (f : E →ᵃ[ℝ] ℝ) (v w : E) (a : ℝ) :
    f (v + a • w) = f v + a * f.linear w := by
  rw [add_comm]
  change f ((a • w) +ᵥ v) = _
  rw [AffineMap.map_vadd]
  simp [map_smul, vadd_eq_add, smul_eq_mul, add_comm]

theorem affine_apply_basis_coordinates (f : E →ᵃ[ℝ] ℝ)
    (b : Module.Basis ι ℝ E) (v x : E) :
    f x = f v + ∑ i, b.repr (x - v) i * f.linear (b i) := by
  have hx : x = (∑ i, b.repr (x - v) i • b i) +ᵥ v := by
    rw [b.sum_repr]
    simp
  calc
    f x = f ((∑ i, b.repr (x - v) i • b i) +ᵥ v) := congrArg f hx
    _ = _ := by
      rw [AffineMap.map_vadd]
      simp [map_sum, map_smul, vadd_eq_add, smul_eq_mul, add_comm]

/-- A positive basis coordinate of a point on a face forces that edge ray
to remain in the same face. The proof uses actual affine slacks and their
nonnegative weighted sum, rather than a combinatorial face assumption. -/
theorem positive_coordinate_endpoint_mem_face {κ : Type*}
    (H : AffineInequalities κ E) (J : Set κ)
    (b : Module.Basis ι ℝ E) (v : E) (hv : v ∈ H.face J)
    (lengths : ι → ℝ) (hlength : ∀ i, 0 < lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ H.region)
    (hcone : ∀ x ∈ H.region, ∀ i, 0 ≤ b.repr (x - v) i)
    (x : E) (hx : x ∈ H.face J) (i : ι) (hi : 0 < b.repr (x - v) i) :
    v + lengths i • b i ∈ H.face J := by
  refine ⟨hedges i, ?_⟩
  intro k hk
  have hv0 : H.slack k v = 0 := hv.2 k hk
  have hx0 : H.slack k x = 0 := hx.2 k hk
  have hcoef (j : ι) : 0 ≤ (H.slack k).linear (b j) := by
    have hj := hedges j k
    rw [affine_apply_add_smul, hv0, zero_add] at hj
    exact nonneg_of_mul_nonneg_right hj (hlength j)
  have hterms (j : ι) :
      0 ≤ b.repr (x - v) j * (H.slack k).linear (b j) :=
    mul_nonneg (hcone x hx.1 j) (hcoef j)
  have hsum : (∑ j, b.repr (x - v) j * (H.slack k).linear (b j)) = 0 := by
    have h := affine_apply_basis_coordinates (H.slack k) b v x
    rw [hv0, hx0, zero_add] at h
    exact h.symm
  have hle : b.repr (x - v) i * (H.slack k).linear (b i) ≤ 0 := by
    have h := Finset.single_le_sum (f := fun j =>
      b.repr (x - v) j * (H.slack k).linear (b j)) (fun j _ => hterms j)
      (Finset.mem_univ i)
    rwa [hsum] at h
  have hzero := le_antisymm hle (hterms i)
  have hlin : (H.slack k).linear (b i) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hi.ne'
  rw [affine_apply_add_smul, hv0, hlin, mul_zero, add_zero]

end AffineCoordinates

/-- The origin together with one nonzero point on every coordinate axis
affinely spans the full coordinate space, including dimension zero. -/
theorem affineSpan_eq_top_of_scaled_axes {d : ℕ} (S : Set (Ambient d))
    (hzero : (0 : Ambient d) ∈ S) (lengths : Fin d → ℝ)
    (hlength : ∀ i, lengths i ≠ 0)
    (haxes : ∀ i, lengths i • Pi.basisFun ℝ (Fin d) i ∈ S) :
    affineSpan ℝ S = ⊤ := by
  have hspan : Submodule.span ℝ S = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℝ (Fin d)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi := (Submodule.span ℝ S).smul_mem (lengths i)⁻¹
      (Submodule.subset_span (haxes i))
    simpa [smul_smul, hlength i] using hi
  rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ S hzero)]
  rw [hspan] <;> rfl

/-- Indices of the incident basis directions whose endpoints lie on a specified face. -/
def faceEdgeIndices {n : ℕ} (F : Set (Ambient n)) (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (lengths : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => v + lengths i • b i ∈ F)

@[simp] theorem mem_faceEdgeIndices {n : ℕ} (F : Set (Ambient n)) (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (lengths : Fin n → ℝ) (i : Fin n) :
    i ∈ faceEdgeIndices F v b lengths ↔ v + lengths i • b i ∈ F := by
  classical
  simp [faceEdgeIndices]

/-- An actual nonempty face in a supporting basis orthant is exactly the
coordinate section obtained by setting its omitted edge coordinates to zero. -/
theorem face_eq_coordinate_section {n : ℕ} {κ : Type*} [Finite κ]
    (H : AffineInequalities κ (Ambient n)) (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ H.region F)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (v : Ambient n) (hv : v ∈ F)
    (lengths : Fin n → ℝ) (hlength : ∀ i, 0 < lengths i)
    (hedges : ∀ i, v + lengths i • b i ∈ H.region)
    (hcone : ∀ x ∈ H.region, ∀ i, 0 ≤ b.repr (x - v) i) :
    F = {x ∈ H.region | ∀ i ∉ faceEdgeIndices F v b lengths,
      b.repr (x - v) i = 0} := by
  classical
  obtain ⟨z, hz, hFeq⟩ := H.exists_activeFace_eq hFconv hF ⟨v, hv⟩
  let J := H.jointZeros z z
  have hvJ : v ∈ H.face J := by simpa only [hFeq] using hv
  ext x
  constructor
  · intro hx
    refine ⟨hF.subset hx, ?_⟩
    intro i hi
    have hnonneg := hcone x (hF.subset hx) i
    by_contra hne
    have hpos : 0 < b.repr (x - v) i := lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hxJ : x ∈ H.face J := by simpa only [hFeq] using hx
    have hiJ := positive_coordinate_endpoint_mem_face H J b v hvJ lengths hlength
      hedges hcone x hxJ i hpos
    apply hi
    apply (mem_faceEdgeIndices F v b lengths i).mpr
    simpa only [hFeq] using hiJ
  · rintro ⟨hxP, hxzero⟩
    rw [hFeq]
    refine ⟨hxP, ?_⟩
    intro k hk
    have hv0 : H.slack k v = 0 := hvJ.2 k hk
    have hterm (i : Fin n) :
        b.repr (x - v) i * (H.slack k).linear (b i) = 0 := by
      by_cases hi : i ∈ faceEdgeIndices F v b lengths
      · have hwi : v + lengths i • b i ∈ H.face J := by
          have hiF := (mem_faceEdgeIndices F v b lengths i).mp hi
          simpa only [hFeq] using hiF
        have hzero := hwi.2 k hk
        rw [affine_apply_add_smul, hv0, zero_add] at hzero
        have hlin := (mul_eq_zero.mp hzero).resolve_left (hlength i).ne'
        rw [hlin, mul_zero]
      · rw [hxzero i hi, zero_mul]
    rw [affine_apply_basis_coordinates (H.slack k) b v x, hv0]
    simp only [hterm, Finset.sum_const_zero, add_zero]

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- A convex face is generated by the original integral generators it contains. -/
theorem face_eq_hull_lattice_filter (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) :
    F = convexHull ℝ ((embed n) ''
      ((P.generators.filter fun z => embed n z ∈ F) : Set (Lattice n))) := by
  classical
  let s := P.generators.image (embed n)
  have hs : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have h := convex_face_eq_convexHull_filter s F hFconv (by simpa only [hs] using hF)
  calc
    F = convexHull ℝ (faceGenerators s F : Set (Ambient n)) := h
    _ = _ := by
      congr 1
      ext x
      simp only [faceGenerators, Finset.mem_coe, Finset.mem_filter, Finset.mem_image,
        Set.mem_image, s]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hx⟩
        exact ⟨z, ⟨hz, hx⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hx⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, hx⟩

/-- Every nonempty actual convex face has an actual vertex. -/
theorem face_vertices_nonempty (F : Set (Ambient n))
    (hFconv : Convex ℝ F) (hF : IsExtreme ℝ P.carrier F) (hFne : F.Nonempty) :
    (F.extremePoints ℝ).Nonempty := by
  have hcompact : IsCompact F := by
    rw [P.face_eq_hull_lattice_filter F hFconv hF]
    exact ((P.generators.filter fun z => embed n z ∈ F).finite_toSet.image
      (embed n)).isCompact_convexHull ℝ
  exact hcompact.extremePoints_nonempty hFne

/-- Supporting basis coordinates follow from the complete list of actual
incident edges. This form retains a specified primitive basis. -/
theorem basis_cone_of_incident_edges (v : Ambient n)
    (hv : v ∈ P.carrier.extremePoints ℝ) (vZ : Lattice n)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hvZ : embed n vZ = v)
    (hall : ∀ w, P.IsEdge v w →
      ∃ i, w = embed n (vZ + (lengths i : ℤ) • b i)) :
    ∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i := by
  classical
  let s := P.generators.image (embed n)
  have hs : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hs] using hv
  have hedgeRay : ∀ w : Ambient n, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Ambient n))) (segment ℝ v w) →
      ∃ i : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • integralBasisReal b i := by
    intro w hvw hface
    obtain ⟨i, rfl⟩ := hall w ⟨hvw, by simpa only [hs] using hface⟩
    refine ⟨i, (lengths i : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [map_add, hvZ, integralBasisReal_apply, add_sub_cancel_left]
    ext j
    simp [embed, Int.cast_mul]
  have h := PaperVerification.ToricVertexCone.nonnegative_basis_coordinates_of_incident_edges
    s v hv' (integralBasisReal b) hedgeRay
  simpa only [hs] using h

/-- Every face, at every one of its vertices, has saturated integral coordinates
in which its complete incident edge family consists of the standard coordinate
axes. Its coordinate polytope is full dimensional; a proper face has strictly
smaller dimension. No face-smoothness theorem is assumed. -/
theorem exists_face_chart_at_vertex (hP : P.Smooth)
    (F : Set (Ambient n)) (hFconv : Convex ℝ F)
    (hF : IsExtreme ℝ P.carrier F) (v : Ambient n)
    (hv : v ∈ F.extremePoints ℝ) :
    ∃ (d : ℕ) (Q : LatticePolytope d) (e : IntegralAffineEmbedding d n)
      (lengths : Fin d → ℕ),
      d ≤ n ∧ (F ≠ P.carrier → d < n) ∧
      e.realMap 0 = v ∧ e.realMap '' Q.carrier = F ∧
      (∀ i, 0 < lengths i ∧ Q.IsEdge 0
        (embed d ((lengths i : ℤ) • Pi.basisFun ℤ (Fin d) i))) ∧
      (∀ w, Q.IsEdge 0 w → ∃ i,
        w = embed d ((lengths i : ℤ) • Pi.basisFun ℤ (Fin d) i)) := by
  classical
  have hvP := hF.extremePoints_subset_extremePoints hv
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hvP
  let bR := integralBasisReal b
  let lR : Fin n → ℝ := fun i => lengths i
  have hlR (i : Fin n) : 0 < lR i := by
    change (0 : ℝ) < (lengths i : ℝ)
    exact_mod_cast (hedges i).1
  have hendpoint (i : Fin n) :
      embed n (vZ + (lengths i : ℤ) • b i) = v + lR i • bR i := by
    rw [map_add, hvZ]
    ext j
    simp [lR, bR, integralBasisReal_apply, embed, Int.cast_mul]
  have hcone := P.basis_cone_of_incident_edges v hvP vZ b lengths hvZ hall
  obtain ⟨κ, hκ, H, hHP⟩ := P.hasFiniteHalfspaces
  letI := hκ
  let I := faceEdgeIndices F v bR lR
  have hsection : F = {x ∈ P.carrier | ∀ i ∉ I, bR.repr (x - v) i = 0} := by
    have h := face_eq_coordinate_section H F hFconv
      (by simpa only [← hHP] using hF) bR v hv.1 lR hlR
      (fun i => by
        rw [← hHP, ← hendpoint]
        exact (P.edge_endpoints_extreme (hedges i).2).2.1)
      (by simpa only [← hHP] using hcone)
    simpa only [← hHP, I] using h
  let d := I.card
  let a : Fin d ↪ Fin n := (I.orderEmbOfFin rfl).toEmbedding
  have harange : Set.range a = (I : Set (Fin n)) := by
    exact Finset.range_orderEmbOfFin I rfl
  have haI (i : Fin d) : a i ∈ I := by
    change a i ∈ (I : Set (Fin n))
    rw [← harange]
    exact Set.mem_range_self i
  let e := selectedBasisChart vZ b a
  let proj : Lattice n → Lattice d := fun z i => b.repr (z - vZ) (a i)
  let S := P.generators.filter (fun z => embed n z ∈ F)
  let qgens := S.image proj
  let Qset := convexHull ℝ ((embed d) '' (qgens : Set (Lattice d)))
  have hcoord (x : Ambient n) (hx : x ∈ F) :
      ∀ j ∉ Set.range a, bR.repr (x - v) j = 0 := by
    have hx' : x ∈ {x ∈ P.carrier | ∀ i ∉ I, bR.repr (x - v) i = 0} := by
      rwa [← hsection]
    intro j hj
    exact hx'.2 j (by simpa only [harange, Finset.mem_coe] using hj)
  have hreconstruct (z : Lattice n) (hz : embed n z ∈ F) : e.latticeMap (proj z) = z := by
    have hz0 (j : Fin n) (hj : j ∉ Set.range a) : b.repr (z - vZ) j = 0 := by
      have h := hcoord (embed n z) hz j hj
      rw [← hvZ, ← map_sub, integralBasisReal_repr] at h
      exact Int.cast_eq_zero.mp h
    change vZ + selectedBasisMap b a (fun i => b.repr (z - vZ) (a i)) = z
    rw [selectedBasisMap_repr_restrict b a (z - vZ) hz0]
    abel
  have hgenimage : e.realMap '' ((embed d) '' (qgens : Set (Lattice d))) =
      (embed n) '' (S : Set (Lattice n)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
      rw [← e.embed_latticeMap, hreconstruct z (Finset.mem_filter.mp hz).2]
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨embed d (proj z), ⟨proj z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [← e.embed_latticeMap, hreconstruct z (Finset.mem_filter.mp hz).2]
  have himage : e.realMap '' Qset = F := by
    rw [e.realMap.image_convexHull, hgenimage]
    exact (P.face_eq_hull_lattice_filter F hFconv hF).symm
  have hezero : e.realMap 0 = v := by
    simp only [e, selectedBasisChart_realMap, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero, hvZ]
  have hmem (x : Ambient d) : x ∈ Qset ↔ e.realMap x ∈ F := by
    rw [← himage]
    exact e.realMap_injective.mem_set_image.symm
  have hzero : (0 : Ambient d) ∈ Qset := (hmem 0).mpr (hezero.symm ▸ hv.1)
  have heaxis (i : Fin d) : e.realMap
      ((lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i) =
        embed n (vZ + (lengths (a i) : ℤ) • b (a i)) := by
    change embed n vZ + selectedBasisMap bR a
      ((lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i) = _
    rw [map_smul]
    have hsingle : selectedBasisMap bR a (Pi.basisFun ℝ (Fin d) i) = bR (a i) := by
      simpa only [Pi.basisFun_apply, selectedBasisMap_single, one_smul]
        using selectedBasisMap_single bR a i (1 : ℝ)
    rw [hsingle, hvZ, hendpoint]
  have haxes (i : Fin d) :
      (lengths (a i) : ℝ) • Pi.basisFun ℝ (Fin d) i ∈ Qset := by
    apply (hmem _).mpr
    rw [heaxis, hendpoint]
    exact (mem_faceEdgeIndices F v bR lR (a i)).mp (haI i)
  have hfull : affineSpan ℝ Qset = ⊤ :=
    affineSpan_eq_top_of_scaled_axes Qset hzero (fun i => lengths (a i))
      (fun i => (hlR (a i)).ne') haxes
  have hqne : qgens.Nonempty := by
    obtain ⟨x, hx⟩ := convexHull_nonempty_iff.mp ⟨0, hzero⟩
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, hq⟩
  let Q : LatticePolytope d := ⟨qgens, hqne, hfull⟩
  have hQset : Q.carrier = Qset := rfl
  have hd : d ≤ n := by
    calc
      d = I.card := rfl
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ I)
      _ = n := Finset.card_fin n
  have hdstrict (hproper : F ≠ P.carrier) : d < n := by
    apply lt_of_le_of_ne hd
    intro hdn
    have hI : I = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ I)
      (by simpa only [Finset.card_fin, ← hdn] using (le_rfl : I.card ≤ I.card))
    apply hproper
    rw [hsection, hI]
    simp
  have heembedaxis (i : Fin d) :
      e.realMap (embed d ((lengths (a i) : ℤ) • Pi.basisFun ℤ (Fin d) i)) =
      embed n (vZ + (lengths (a i) : ℤ) • b (a i)) := by
    rw [← e.embed_latticeMap]
    congr 1
    change vZ + selectedBasisMap b a
      ((lengths (a i) : ℤ) • Pi.basisFun ℤ (Fin d) i) = _
    rw [map_smul]
    have hs : selectedBasisMap b a (Pi.basisFun ℤ (Fin d) i) = b (a i) := by
      simpa only [Pi.basisFun_apply, selectedBasisMap_single, one_smul]
        using selectedBasisMap_single b a i (1 : ℤ)
    rw [hs]
  refine ⟨d, Q, e, fun i => lengths (a i), hd, hdstrict, hezero, himage, ?_, ?_⟩
  · intro i
    refine ⟨(hedges (a i)).1, ?_, ?_⟩
    · intro heq
      have h := congrArg e.realMap heq
      rw [hezero, heembedaxis] at h
      exact (hedges (a i)).2.1 h
    · apply (affine_isExtreme_image_iff e.realMap e.realMap_injective _ _).mp
      rw [hQset, himage, image_segment, hezero, heembedaxis]
      apply (hedges (a i)).2.2.mono hF.subset
      apply hFconv.segment_subset hv.1
      rw [hendpoint]
      exact (mem_faceEdgeIndices F v bR lR (a i)).mp (haI i)
  · intro w hw
    have hwF : e.realMap w ∈ F := by
      rw [← himage]
      exact ⟨w, (Q.edge_endpoints_extreme hw).2.1, rfl⟩
    have hedgeP : P.IsEdge v (e.realMap w) := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw.1
        apply e.realMap_injective
        simpa only [hezero] using h
      · have h := affine_isExtreme_image e.realMap e.realMap_injective hw.2
        rw [hQset, himage, image_segment, hezero] at h
        exact hF.trans h
    obtain ⟨j, hj⟩ := hall (e.realMap w) hedgeP
    have hjI : j ∈ I := by
      apply (mem_faceEdgeIndices F v bR lR j).mpr
      rw [← hendpoint, ← hj]
      exact hwF
    have hjrange : j ∈ Set.range a := by rwa [harange]
    obtain ⟨i, rfl⟩ := hjrange
    refine ⟨i, e.realMap_injective ?_⟩
    rw [heembedaxis]
    exact hj

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricFaceInheritance
-- END ORIGINAL PaperVerification.ToricFaceInheritance


-- BEGIN ORIGINAL PaperVerification.ToricBoundary
section Source_ToricBoundary

-- original header: module
-- original header: public import PaperVerification.ToricIntegralAffine
-- original header: public import Mathlib.Topology.Order.Basic
-- original header: @[expose] public section
/-!
# Boundary points lie on proper actual faces

A finite halfspace presentation is constructed earlier from finite convex hulls.
Here globally redundant equality constraints are removed using full dimension,
so an ordinary boundary point yields a genuinely proper convex face.
-/

noncomputable section

namespace PaperVerification.ToricExchange

open Set

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]

/-- An affine functional vanishing on a set vanishes throughout its affine span. -/
theorem affine_zero_on_span (S : Set V) (f : V →ᵃ[ℝ] ℝ)
    (h : ∀ x ∈ S, f x = 0) : ∀ x ∈ affineSpan ℝ S, f x = 0 := by
  intro x hx
  refine affineSpan_induction (p := fun y => f y = 0) hx h ?_
  intro c u v w hu hv hw
  rw [AffineMap.map_vadd, map_smul, AffineMap.linear_apply_vsub]
  simp [hu, hv, hw]

namespace AffineInequalities

variable (H : AffineInequalities I V) [Finite I]

/-- A noninterior point of a full-dimensional finite halfspace polytope
has an active supporting constraint that is not globally redundant. -/
theorem exists_informative_active_of_not_interior
    (hspan : affineSpan ℝ H.region = ⊤) (x : V) (hx : x ∈ H.region)
    (hint : x ∉ interior H.region) :
    ∃ i : I, H.informative i ∧ H.slack i x = 0 := by
  classical
  by_contra h
  have hstrict (i : I) (hi : H.informative i) : 0 < H.slack i x := by
    have hne : H.slack i x ≠ 0 := fun hz => h ⟨i, hi, hz⟩
    exact lt_of_le_of_ne (hx i) hne.symm
  have hzero (i : I) (hi : ¬ H.informative i) : ∀ y : V, H.slack i y = 0 := by
    intro y
    have hz : ∀ z ∈ H.region, H.slack i z = 0 := by
      intro z hz
      by_contra hne
      exact hi ⟨z, hz, hne⟩
    exact affine_zero_on_span H.region (H.slack i) hz y (by rw [hspan]; trivial)
  let U : Set V := ⋂ i : {i : I // H.informative i}, {y | 0 < H.slack i.1 y}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (H.continuous_slack i.1)
  have hxU : x ∈ U := mem_iInter.mpr (fun i => hstrict i.1 i.2)
  have hUH : U ⊆ H.region := by
    intro y hy i
    by_cases hi : H.informative i
    · exact (mem_iInter.mp hy ⟨i, hi⟩).le
    · exact le_of_eq (hzero i hi y).symm
  exact hint (interior_maximal hUH hU hxU)

/-- A boundary point lies on a proper ordinary convex face. -/
theorem exists_proper_face_of_not_interior
    (hspan : affineSpan ℝ H.region = ⊤) (x : V) (hx : x ∈ H.region)
    (hint : x ∉ interior H.region) :
    ∃ F : Set V, x ∈ F ∧ Convex ℝ F ∧ IsExtreme ℝ H.region F ∧ F ≠ H.region := by
  obtain ⟨i, hi, hix⟩ := H.exists_informative_active_of_not_interior hspan x hx hint
  refine ⟨H.face {i}, ⟨hx, ?_⟩, H.convex_face {i}, H.isExtreme_face {i}, ?_⟩
  · intro j hj
    simpa only [Set.mem_singleton_iff.mp hj] using hix
  · obtain ⟨y, hy, hiy⟩ := hi
    intro hface
    have hyface : y ∈ H.face {i} := by rw [hface]; exact hy
    exact hiy (hyface.2 i (Set.mem_singleton i))

end AffineInequalities

end PaperVerification.ToricExchange

namespace PaperVerification.ToricGeometry.LatticePolytope

open PaperVerification.ToricExchange

/-- The boundary-face reduction for the literal full-dimensional lattice
polytope type, with no exposed-face assumption. -/
theorem boundary_proper_face {n : ℕ} (P : LatticePolytope n)
    (x : Ambient n) (hx : x ∈ P.carrier) (hint : x ∉ interior P.carrier) :
    ∃ F : Set (Ambient n), x ∈ F ∧ Convex ℝ F ∧
      IsExtreme ℝ P.carrier F ∧ F ≠ P.carrier := by
  obtain ⟨I, hI, H, hP⟩ := P.hasFiniteHalfspaces
  letI := hI
  have hspan : affineSpan ℝ H.region = ⊤ := by
    rw [← hP]
    exact P.fullDimensional
  rw [hP] at hx hint ⊢
  exact H.exists_proper_face_of_not_interior hspan x hx hint

end PaperVerification.ToricGeometry.LatticePolytope
end
end Source_ToricBoundary
-- END ORIGINAL PaperVerification.ToricBoundary


