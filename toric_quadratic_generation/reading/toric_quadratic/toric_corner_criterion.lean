module

public import PaperVerification.ToricExtremalCriterion
public import PaperVerification.ToricPolytopeSupport
public import PaperVerification.ToricStarDualBasis

@[expose] public section

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
