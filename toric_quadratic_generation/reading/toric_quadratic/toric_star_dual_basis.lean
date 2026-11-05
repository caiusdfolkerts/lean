module
public import PaperVerification.ToricDualNormalCone
public import PaperVerification.ToricStarBoxCoordinates
@[expose] public section
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

