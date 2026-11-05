module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part07
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricStarDualBasis
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
-- END PaperVerification.ToricStarDualBasis
end

section
-- BEGIN PaperVerification.ToricCornerCriterion



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
-- END PaperVerification.ToricCornerCriterion
end

section
-- BEGIN PaperVerification.ToricFiniteSupportPerturbation
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
-- END PaperVerification.ToricFiniteSupportPerturbation
end

section
-- BEGIN PaperVerification.ToricFanPolytopes



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
-- END PaperVerification.ToricFanPolytopes
end

section
-- BEGIN PaperVerification.ToricOrthantEdges



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
-- END PaperVerification.ToricOrthantEdges
end

section
-- BEGIN PaperVerification.ToricNormalConeFaces
/-!
# Intersections of actual normal cones

An intersection with another point's normal cone is the zero-coordinate face
cut out by the displacement to that point. The proof expands a normal in an
actual dual integral basis and uses nonnegativity of every summand.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- A normal supports two carrier points precisely when its support value
agrees at those points. -/
theorem mem_normalCone_inter_iff (v w : Ambient n)
    (hv : v ∈ P.carrier) (hw : w ∈ P.carrier) (u : Ambient n) :
    u ∈ P.normalCone v ∩ P.normalCone w ↔
      u ∈ P.normalCone v ∧ (∑ j, u j * (w j - v j)) = 0 := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (x : Ambient n) :
      u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hp : (∑ j, u j * (w j - v j)) = f w - f v := by
    change f (w - v) = _
    exact f.map_sub w v
  change (u ∈ P.normalCone v ∧ u ∈ P.normalCone w) ↔ _
  simp only [hmem v, hmem w, hp]
  constructor
  · rintro ⟨huv, huw⟩
    exact ⟨huv, sub_eq_zero.mpr (le_antisymm (huw v hv) (huv w hw))⟩
  · rintro ⟨huv, heq⟩
    refine ⟨huv, ?_⟩
    intro y hy
    rw [sub_eq_zero.mp heq]
    exact huv y hy

/-- In any genuine integral basis generating the normal cone at v, its
intersection with the cone at w is the coordinate face consisting of those
primitive normals that vanish on w-v. -/
theorem normalCone_inter_eq_latticeRayCone
    (v w : Ambient n) (hv : v ∈ P.carrier) (hw : w ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n))) :
    P.normalCone v ∩ P.normalCone w =
      (latticeRayCone ((Finset.univ.filter (fun i =>
        (∑ j, embed n (d i) j * (w j - v j)) = 0)).image d) : Set (Ambient n)) := by
  classical
  let b := integralBasisReal d
  let height : Fin n → ℝ := fun i => ∑ j, embed n (d i) j * (w j - v j)
  have hheight (i : Fin n) : 0 ≤ height i := by
    have hi : embed n (d i) ∈ P.normalCone v := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)
    exact hi w hw
  have hmem (u : Ambient n) :
      u ∈ P.normalCone v ↔ ∀ i, 0 ≤ b.repr u i := by
    rw [hcone]
    change u ∈ latticeRayCone (Finset.univ.image d) ↔ _
    rw [mem_latticeRayCone_basis_iff]
    simp only [Finset.mem_univ, not_true_eq_false, false_implies, implies_true, and_true, b]
  have hpair (u : Ambient n) :
      (∑ j, u j * (w j - v j)) = ∑ i, b.repr u i * height i := by
    let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (w - v)
    have hf (i : Fin n) : f (b i) = height i := by
      change ((w - v) ⬝ᵥ (b i)) = _
      rw [dotProduct_comm]
      rw [show b i = embed n (d i) from integralBasisReal_apply d i]
      rfl
    have hs := congrArg f (b.sum_repr u)
    have hsum : f u = ∑ i, b.repr u i * f (b i) := by
      simpa only [map_sum, map_smul, smul_eq_mul] using hs.symm
    calc
      (∑ j, u j * (w j - v j)) = f u := dotProduct_comm u (w - v)
      _ = ∑ i, b.repr u i * height i := by simpa only [hf] using hsum
  ext u
  rw [P.mem_normalCone_inter_iff v w hv hw u, hmem u, hpair u]
  change ((∀ i, 0 ≤ b.repr u i) ∧ (∑ i, b.repr u i * height i) = 0) ↔
    u ∈ latticeRayCone ((Finset.univ.filter (fun i => height i = 0)).image d)
  rw [mem_latticeRayCone_basis_iff]
  change ((∀ i, 0 ≤ b.repr u i) ∧ (∑ i, b.repr u i * height i) = 0) ↔
    (∀ i, 0 ≤ b.repr u i) ∧
      ∀ i ∉ Finset.univ.filter (fun i => height i = 0), b.repr u i = 0
  constructor
  · rintro ⟨hu, hsum⟩
    refine ⟨hu, ?_⟩
    intro i hi
    have hne : height i ≠ 0 := by simpa only [Finset.mem_filter, Finset.mem_univ,
      true_and] using hi
    have hp : b.repr u i * height i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hu j) (hheight j))).mp hsum i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hp).resolve_right hne
  · rintro ⟨hu, hz⟩
    refine ⟨hu, Finset.sum_eq_zero (fun i _ => ?_)⟩
    by_cases hi : height i = 0
    · rw [hi, mul_zero]
    · have hnot : i ∉ Finset.univ.filter (fun i => height i = 0) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
      rw [hz i hnot, zero_mul]

/-- For a primitive edge basis, the vanishing test above is exactly the
corresponding primal coordinate of the displacement. -/
theorem normalCone_inter_eq_dual_coordinate_face
    (vZ : Lattice n) (w : Ambient n)
    (hv : embed n vZ ∈ P.carrier) (hw : w ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i) :
    P.normalCone (embed n vZ) ∩ P.normalCone w =
      (latticeRayCone ((Finset.univ.filter (fun i =>
        (integralBasisReal b).repr (w - embed n vZ) i = 0)).image
          (integralDualBasis b)) : Set (Ambient n)) := by
  have h := P.normalCone_inter_eq_latticeRayCone (embed n vZ) w hv hw
    (integralDualBasis b)
    (P.normalCone_eq_latticeRayCone vZ b lengths hedges hcone)
  have he (i : Fin n) :
      (∑ j, embed n (integralDualBasis b i) j * (w j - embed n vZ j)) =
        (integralBasisReal b).repr (w - embed n vZ) i :=
    integralDualBasis_real_pairing b i (w - embed n vZ)
  simpa only [he] using h

end PaperVerification.ToricGeometry.LatticePolytope

end
-- END PaperVerification.ToricNormalConeFaces
end

section
-- BEGIN PaperVerification.ToricNormalConeRealization
/-!
# Every coordinate subcone is an actual normal cone

A positive average of a vertex and the omitted incident edge endpoints
realizes any selected subset of primitive normals. This is a direct convex
argument, including the zero-dimensional case.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- The normal cone at an interior point of an actual chord is the
intersection of the endpoint normal cones. The midpoint suffices here. -/
theorem normalCone_midpoint (v w : Ambient n)
    (hv : v ∈ P.carrier) (hw : w ∈ P.carrier) :
    P.normalCone (AffineMap.lineMap v w (1 / 2 : ℝ)) =
      P.normalCone v ∩ P.normalCone w := by
  ext u
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (x : Ambient n) :
      u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hmid : f (AffineMap.lineMap v w (1 / 2 : ℝ)) = (f v + f w) / 2 := by
    simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul]
    ring
  change u ∈ P.normalCone _ ↔ u ∈ P.normalCone v ∧ u ∈ P.normalCone w
  simp only [hmem]
  constructor
  · intro hm
    have hmv := hm v hv
    have hmw := hm w hw
    constructor
    · intro z hz
      have hmz := hm z hz
      linarith
    · intro z hz
      have hmz := hm z hz
      linarith
  · rintro ⟨huv, huw⟩ z hz
    have hvz := huv z hz
    have hwz := huw z hz
    linarith

/-- Every subset of the primitive normal basis at a smooth corner is the
entire ordinary normal cone at an explicitly constructed carrier point. -/
theorem normalCone_subbasis_realized
    (vZ : Lattice n) (hv : embed n vZ ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (I : Finset (Fin n)) :
    ∃ x ∈ P.carrier,
      P.normalCone x = (latticeRayCone (I.image (integralDualBasis b)) : Set (Ambient n)) := by
  classical
  let v := embed n vZ
  let bR := integralBasisReal b
  let t : ℝ := 1 / ((n : ℝ) + 1)
  let s : Fin n → ℝ := fun i => if i ∈ I then 0 else t
  let d : Fin n → Ambient n := fun i => (lengths i : ℝ) • bR i
  let y : Ambient n := v + ∑ i, s i • d i
  let x : Ambient n := AffineMap.lineMap v y (1 / 2 : ℝ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hs (i : Fin n) : 0 ≤ s i ∧ s i ≤ t := by
    dsimp [s]
    split_ifs <;> constructor <;> linarith
  have hsum : ∑ i, s i ≤ (1 : ℝ) := by
    calc
      (∑ i, s i) ≤ ∑ _ : Fin n, t :=
        Finset.sum_le_sum (fun i _ => (hs i).2)
      _ = (n : ℝ) * t := by simp
      _ ≤ 1 := by
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        simpa only [t, div_eq_mul_inv, one_mul] using
          (div_le_one hn).mpr (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
  have hd (i : Fin n) : v + (1 : ℝ) • d i ∈ P.carrier := by
    have he := (P.edge_endpoints_extreme (hedges i).2).2.1
    simpa only [v, d, bR, one_smul, map_add, embed_int_smul, Int.cast_natCast,
      integralBasisReal_apply] using he
  have hy : y ∈ P.carrier :=
    PaperVerification.Toric.corner_simplex_mem P.carrier (convex_convexHull ℝ _)
      v hv d 1 (by norm_num) hd s (fun i => (hs i).1) hsum
  have hx : x ∈ P.carrier :=
    (convex_convexHull ℝ _).lineMap_mem hv hy
      ⟨by norm_num, by norm_num⟩
  have hcy (i : Fin n) : bR.coord i (y - v) = s i * (lengths i : ℝ) := by
    dsimp [y]
    rw [add_sub_cancel_left, map_sum]
    simp [d, map_smul, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply, Finsupp.single_apply, smul_eq_mul]
  have hcx (i : Fin n) :
      bR.repr (x - v) i = (1 / 2 : ℝ) * (s i * (lengths i : ℝ)) := by
    change bR.coord i (x - v) = _
    dsimp [x]
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul,
      smul_eq_mul, hcy]
  have hzero (i : Fin n) : bR.repr (x - v) i = 0 ↔ i ∈ I := by
    rw [hcx]
    by_cases hi : i ∈ I
    · simp [s, hi]
    · have hlen : (0 : ℝ) < lengths i := by exact_mod_cast (hedges i).1
      have hp : (0 : ℝ) < (1 / 2 : ℝ) * (s i * (lengths i : ℝ)) := by
        rw [show s i = t by simp only [s, if_neg hi]]
        exact mul_pos (by norm_num) (mul_pos ht hlen)
      simp only [hi, iff_false]
      exact ne_of_gt hp
  have hsub : P.normalCone x ⊆ P.normalCone v := by
    change P.normalCone (AffineMap.lineMap v y (1 / 2 : ℝ)) ⊆ P.normalCone v
    rw [P.normalCone_midpoint v y hv hy]
    exact Set.inter_subset_left
  have hfilter : Finset.univ.filter
      (fun i => (integralBasisReal b).repr (x - embed n vZ) i = 0) = I := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzero i
  have hinter := P.normalCone_inter_eq_dual_coordinate_face vZ x hv hx
    b lengths hedges hcone
  rw [Set.inter_eq_right.mpr hsub, hfilter] at hinter
  exact ⟨x, hx, hinter⟩

/-- Every subset of a primitive normal basis belongs to the actual normal fan. -/
theorem subbasis_mem_normalFan
    (vZ : Lattice n) (hv : embed n vZ ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (I : Finset (Fin n)) :
    (latticeRayCone (I.image (integralDualBasis b)) : Set (Ambient n)) ∈ P.normalFan := by
  obtain ⟨x, hx, hnormal⟩ := P.normalCone_subbasis_realized vZ hv b lengths hedges hcone I
  exact ⟨x, hx, hnormal.symm⟩

end PaperVerification.ToricGeometry.LatticePolytope

end
-- END PaperVerification.ToricNormalConeRealization
end

section
-- BEGIN PaperVerification.ToricNormalConeAverages
/-!
# Normal cones of finite convex combinations

All support inequalities are the actual coordinate-pairing inequalities of
the lattice polytope. Zero weights are ignored; positive weights force equality
of the support value at every participating point.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators

variable {n : ℕ} (P : LatticePolytope n)

/-- A normal supports a finite convex average exactly when it supports every
point with positive weight. The averaging family need not consist of vertices. -/
theorem mem_normalCone_convex_average {ι : Type*} [Fintype ι]
    (v : ι → Ambient n) (p : ι → ℝ)
    (hv : ∀ i, v i ∈ P.carrier)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (u : Ambient n) :
    u ∈ P.normalCone (∑ i, p i • v i) ↔
      ∀ i, 0 < p i → u ∈ P.normalCone (v i) := by
  classical
  let x : Ambient n := ∑ i, p i • v i
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hmem (z : Ambient n) :
      u ∈ P.normalCone z ↔ ∀ y ∈ P.carrier, f z ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - z)) ↔ _
    simp only [map_sub, sub_nonneg]
  have hfx : f x = ∑ i, p i * f (v i) := by
    simp only [x, map_sum, map_smul, smul_eq_mul]
  change u ∈ P.normalCone x ↔ _
  simp only [hmem]
  constructor
  · intro hx i hi y hy
    have hnonneg (j : ι) : 0 ≤ p j * (f (v j) - f x) :=
      mul_nonneg (hp0 j) (sub_nonneg.mpr (hx (v j) (hv j)))
    have hsum : (∑ j, p j * (f (v j) - f x)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, ← hfx,
        sub_self]
    have hterm : p i * (f (v i) - f x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i
        (Finset.mem_univ i)
    have heq : f (v i) = f x :=
      sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt hi))
    rw [heq]
    exact hx y hy
  · intro h y hy
    have hterm (i : ι) : p i * f (v i) ≤ p i * f y := by
      by_cases hi : p i = 0
      · simp only [hi, zero_mul, le_refl]
      · have hip : 0 < p i := lt_of_le_of_ne (hp0 i) (Ne.symm hi)
        exact mul_le_mul_of_nonneg_left (h i hip y hy) (hp0 i)
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
    rw [← hfx, ← Finset.sum_mul, hp1, one_mul] at hs
    exact hs

/-- Set-valued form: the normal cone of a convex average is the intersection
of the actual normal cones at precisely its positive-weight points. -/
theorem normalCone_convex_average {ι : Type*} [Fintype ι]
    (v : ι → Ambient n) (p : ι → ℝ)
    (hv : ∀ i, v i ∈ P.carrier)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    P.normalCone (∑ i, p i • v i) =
      ⋂ i ∈ Finset.univ.filter (fun i => 0 < p i), P.normalCone (v i) := by
  classical
  ext u
  simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and,
    P.mem_normalCone_convex_average v p hv hp0 hp1 u]

end PaperVerification.ToricGeometry.LatticePolytope

end
-- END PaperVerification.ToricNormalConeAverages
end

section
-- BEGIN PaperVerification.ToricFanPolytopeConstruction



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
-- END PaperVerification.ToricFanPolytopeConstruction
end

section
-- BEGIN PaperVerification.ToricAdjointSupport



/-!
# Interior lattice points and the literal canonical shift

Primitive fan rays are nonzero integral vectors. The topological interior
is therefore cut out by the strict ray inequalities. At a lattice point,
strict integral slack is equivalent to slack at least one, exactly the
coefficient shift by minus one used for the toric canonical divisor.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Set
open scoped BigOperators Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem normalRay_functional_ne_zero (u : Lattice n) (hu : u ∈ «Σ».rays) :
    dotProductEquiv ℝ (Fin n) (embed n u) ≠ 0 := by
  intro he
  have hemb : embed n u = 0 := (dotProductEquiv ℝ (Fin n)).injective (by simpa using he)
  exact «Σ».ray_ne_zero hu ((embed_injective n) (by simpa using hemb))

/-- The topological interior uses strict inequalities for the actual
nonzero primitive rays. This includes dimension zero. -/
theorem interior_fanPolytope_eq (a : Lattice n → ℝ) :
    interior («Σ».fanPolytope a) =
      {x | ∀ u ∈ «Σ».rays, -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) x} := by
  ext x
  constructor
  · intro hx u hu
    rw [«Σ».fanPolytope_eq_normalHalfspaces] at hx
    exact strict_support_of_interior
      (fun v : «Σ».rays => dotProductEquiv ℝ (Fin n) (embed n v))
      (fun v : «Σ».rays => -a v) x hx ⟨u, hu⟩ («Σ».normalRay_functional_ne_zero u hu)
  · intro hx
    let U : Set (Ambient n) :=
      ⋂ u ∈ «Σ».rays, {x | -a u < (dotProductEquiv ℝ (Fin n) (embed n u)) x}
    have hUopen : IsOpen U := by
      apply isOpen_biInter_finset
      intro u hu
      exact isOpen_lt continuous_const
        (dotProductEquiv ℝ (Fin n) (embed n u)).continuous_of_finiteDimensional
    have hxU : x ∈ U := Set.mem_iInter₂.mpr hx
    have hUsub : U ⊆ «Σ».fanPolytope a := by
      intro y hy u hu
      exact (Set.mem_iInter₂.mp hy u hu).le
    exact (interior_maximal hUsub hUopen) hxU

/-- The integral support pairing agrees with the genuine integer dot
product before casting. -/
theorem normalRay_pairing_lattice (u z : Lattice n) :
    (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) =
      ((∑ i, u i * z i : ℤ) : ℝ) := by
  simp [dotProductEquiv, dotProduct, embed]

/-- A lattice point lies in the actual interior exactly when it lies in
the support polytope with every primitive coefficient reduced by one. -/
theorem lattice_mem_interior_iff_adjointSupport (a : Lattice n → ℤ) (z : Lattice n) :
    embed n z ∈ interior («Σ».fanPolytope (fun u => (a u : ℝ))) ↔
      embed n z ∈ «Σ».fanPolytope (fun u => ((a u - 1 : ℤ) : ℝ)) := by
  rw [«Σ».interior_fanPolytope_eq]
  constructor
  · intro hz u hu
    have h := hz u hu
    change -(a u : ℝ) < (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) at h
    change -((a u - 1 : ℤ) : ℝ) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z)
    rw [normalRay_pairing_lattice] at h ⊢
    have hi : -a u < ∑ i, u i * z i := by exact_mod_cast h
    have hi' : -(a u - 1) ≤ ∑ i, u i * z i := by omega
    exact_mod_cast hi'
  · intro hz u hu
    have h := hz u hu
    change -((a u - 1 : ℤ) : ℝ) ≤
      (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z) at h
    change -(a u : ℝ) < (dotProductEquiv ℝ (Fin n) (embed n u)) (embed n z)
    rw [normalRay_pairing_lattice] at h ⊢
    have hi : -(a u - 1) ≤ ∑ i, u i * z i := by exact_mod_cast h
    have hi' : -a u < ∑ i, u i * z i := by omega
    exact_mod_cast hi'

end PaperVerification.ToricGeometry.SmoothCompleteFan
end
-- END PaperVerification.ToricAdjointSupport
end

section
-- BEGIN PaperVerification.ToricCartierCharacterModules



/-!
# Exact intersection of the actual principal character modules

Each affine semigroup chart is a genuine subalgebra of the Laurent
algebra. Its Cartier module is its image under multiplication by the
actual Cartier character. Their intersection is proved to be exactly
the module supported on all integral points of the support polytope.
No global-section or scheme dictionary is assumed by this statement.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set AddMonoidAlgebra
open PaperVerification.ToricCharacters
open scoped BigOperators Classical

def integerPairing {n : ℕ} (u m : Lattice n) : ℤ := ∑ j, u j * m j

theorem integerPairing_add {n : ℕ} (u m p : Lattice n) :
    integerPairing u (m + p) = integerPairing u m + integerPairing u p := by
  simp only [integerPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem integerPairing_sub {n : ℕ} (u m p : Lattice n) :
    integerPairing u (m - p) = integerPairing u m - integerPairing u p := by
  simp only [integerPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

def dualConeMonoid {n : ℕ} (s : Finset (Lattice n)) : AddSubmonoid (Lattice n) where
  carrier := {m | ∀ u ∈ s, 0 ≤ integerPairing u m}
  zero_mem' := by intro u hu; simp [integerPairing]
  add_mem' := by
    intro m p hm hp u hu
    rw [integerPairing_add]
    exact add_nonneg (hm u hu) (hp u hu)

/-- Smoothness gives the actual free semigroup coordinates of the
dual cone, including its unrestricted Laurent directions. -/
theorem dualConeMonoid_basis_eq {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    dualConeMonoid (I.image b) = coordinateConeMonoid (integralDualBasis b) I := by
  ext m
  change (∀ u ∈ I.image b, 0 ≤ integerPairing u m) ↔
    ∀ i ∈ I, 0 ≤ (integralDualBasis b).repr m i
  constructor
  · intro h i hi
    have hh := h (b i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    simpa only [integerPairing, integralDualBasis_repr, mul_comm] using hh
  · intro h u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    simpa only [integerPairing, integralDualBasis_repr, mul_comm] using h i hi

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem cartierLatticePoint_pairing (a : Lattice n → ℤ) (s : «Σ».fullCones)
    (u : Lattice n) (hu : u ∈ (s : Finset (Lattice n))) :
    integerPairing u («Σ».cartierLatticePoint a s) = -a u := by
  have h := «Σ».cartierPoint_support_eq_of_mem (fun v => (a v : ℝ)) s hu
  rw [← «Σ».embed_cartierLatticePoint a s, normalRay_pairing_lattice] at h
  exact_mod_cast h

theorem cartier_translate_dualCone (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    (fun m => «Σ».cartierLatticePoint a s + m) ''
      (dualConeMonoid (s : Finset (Lattice n)) : Set (Lattice n)) =
        {m | ∀ u ∈ (s : Finset (Lattice n)), -a u ≤ integerPairing u m} := by
  ext m
  constructor
  · rintro ⟨w, hw, rfl⟩ u hu
    rw [integerPairing_add, «Σ».cartierLatticePoint_pairing a s u hu]
    exact le_add_of_nonneg_right (hw u hu)
  · intro hm
    refine ⟨m - «Σ».cartierLatticePoint a s, ?_, by abel⟩
    intro u hu
    rw [integerPairing_sub, «Σ».cartierLatticePoint_pairing a s u hu]
    exact sub_nonneg.mpr (hm u hu)

def fanIntegralExponents (a : Lattice n → ℤ) : Set (Lattice n) :=
  {m | embed n m ∈ «Σ».fanPolytope (fun u => (a u : ℝ))}

theorem integral_exponents_eq_chart_intersection (hpure : «Σ».IsPure)
    (a : Lattice n → ℤ) :
    «Σ».fanIntegralExponents a =
      ⋂ s : «Σ».fullCones, (fun m => «Σ».cartierLatticePoint a s + m) ''
        (dualConeMonoid (s : Finset (Lattice n)) : Set (Lattice n)) := by
  ext m
  simp only [Set.mem_iInter, «Σ».cartier_translate_dualCone, Set.mem_setOf_eq]
  constructor
  · intro hm s u hu
    have h := hm u («Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s) hu)
    rw [normalRay_pairing_lattice] at h
    change -(a u : ℝ) ≤ (integerPairing u m : ℝ) at h
    exact_mod_cast h
  · intro hm u hu
    obtain ⟨t, ht, hut⟩ := («Σ».mem_rays_iff u).mp hu
    obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
    let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
    have h := hm s' u (hts hut)
    rw [normalRay_pairing_lattice]
    change -(a u : ℝ) ≤ (integerPairing u m : ℝ)
    exact_mod_cast h

variable (k : Type*) [CommSemiring k]

/-- The local principal module, defined by actual multiplication in the
Laurent algebra of the actual semigroup chart ring. -/
def cartierChartCharacterModule (a : Lattice n → ℤ) (s : «Σ».fullCones) :
    Submodule k (AddMonoidAlgebra k (Lattice n)) :=
  ((monoidChartAlgebra k (dualConeMonoid (s : Finset (Lattice n)))).toSubmodule).map
    (characterTranslation k («Σ».cartierLatticePoint a s)).toLinearMap

/-- Exact global compatibility at the character-module level. This is
the algebraic computation needed after identifying a toric line bundle's
actual global sections with these local principal modules. -/
theorem iInf_cartierChartCharacterModule (hpure : «Σ».IsPure) (a : Lattice n → ℤ) :
    (⨅ s : «Σ».fullCones, «Σ».cartierChartCharacterModule k a s) =
      characterModule k («Σ».fanIntegralExponents a) := by
  rw [«Σ».integral_exponents_eq_chart_intersection hpure a]
  exact intersection_principal_character_modules k
    (fun s : «Σ».fullCones => dualConeMonoid (s : Finset (Lattice n)))
    («Σ».cartierLatticePoint a)

/-- Every genuine smooth cone has the proved polynomial/Laurent chart
algebra, with its actual ray set and a chosen integral basis extension. -/
theorem smooth_chart_algebra (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    ∃ (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)),
      s = I.image b ∧ Nonempty
        (monoidChartAlgebra k (dualConeMonoid s) ≃ₐ[k]
          MvPolynomial I (AddMonoidAlgebra k (FreeCoordinate I → ℤ))) := by
  obtain ⟨b, I, hI⟩ := «Σ».smooth s hs
  refine ⟨b, I, hI, ?_⟩
  rw [hI, dualConeMonoid_basis_eq]
  exact ⟨smoothChartAlgebraEquiv k (integralDualBasis b) I⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.iInf_cartierChartCharacterModule
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.smooth_chart_algebra
end
-- END PaperVerification.ToricCartierCharacterModules
end

#eval "TORIC_DICTIONARY_PART_08_EOF"
