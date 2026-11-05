module

public import Continuation.Fano.SegmentSimplexBundleSmooth

/-!
# The single determinant obstruction in the segment–simplex family

For a ≤ 1 the actual vertex bases satisfy the positive-coordinate
criterion, which yields uniform unimodularity of every selection of
normals.  Conversely, replacing the last standard basis vector by the
sloping normal gives the full determinant a.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open scoped BigOperators

theorem localBasis_repr (d : ℕ) (a : ℤ) (t : VertexIndex d)
    (x : Lattice (d + 1)) (i : Fin (d + 1)) :
    (localBasis d a t).repr x i = (cornerEquiv d a t).symm x i := by
  have h := congrArg (cornerEquiv d a t).symm ((localBasis d a t).sum_repr x)
  have h' : (∑ j : Fin (d + 1), (localBasis d a t).repr x j •
      (Pi.basisFun ℤ (Fin (d + 1))) j) = (cornerEquiv d a t).symm x := by
    simpa only [map_sum, map_smul, localBasis, Module.Basis.map_apply,
      LinearEquiv.symm_apply_apply] using h
  have hi := congrArg (fun z : Lattice (d + 1) => z i) h'
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.basisFun_apply, Pi.single_apply] using hi

theorem omitted_repr_last (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    (localBasis d a t).repr (simplexNormal d a t.2) (Fin.last d) = height t.1 * a := by
  rw [localBasis_repr]
  rcases t with ⟨b, k⟩
  cases k <;> simp [cornerEquiv, constantCornerEquiv, otherCornerEquiv, simplexNormal]

theorem omitted_repr_castSucc (d : ℕ) (a : ℤ) (t : VertexIndex d) (i : Fin d) :
    (localBasis d a t).repr (simplexNormal d a t.2) i.castSucc = -1 := by
  rw [localBasis_repr]
  rcases t with ⟨b, k⟩
  cases k with
  | none => simp [cornerEquiv, constantCornerEquiv, simplexNormal]
  | some k =>
      by_cases hi : i = k <;>
        simp [cornerEquiv, otherCornerEquiv, simplexNormal, hi]

theorem omitted_positive_mass_le_one {d : ℕ} {a : ℤ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : VertexIndex d) :
    ∑ i, max ((localBasis d a t).repr (simplexNormal d a t.2) i) 0 ≤ 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [omitted_repr_castSucc, omitted_repr_last]
  norm_num only [max_eq_right (by norm_num : (-1 : ℤ) ≤ 0), Finset.sum_const_zero,
    zero_add]
  rcases t with ⟨b, k⟩
  cases b <;> simp [height, ha, ha1, max_eq_right (neg_nonpos.mpr ha),
    max_eq_left ha]

theorem basis_vector_positive_mass {d : ℕ} (B : Module.Basis (Fin (d + 1)) ℤ
    (Lattice (d + 1))) (j : Fin (d + 1)) :
    ∑ i, max (B.repr (B j) i) 0 = 1 := by
  classical
  calc
    (∑ i, max (B.repr (B j) i) 0) = max (B.repr (B j) j) 0 := by
      apply Finset.sum_eq_single j
      · intro i hi hij
        simp [Module.Basis.repr_self, Finsupp.single_apply, hij, Ne.symm hij]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    _ = 1 := by norm_num [Module.Basis.repr_self, Finsupp.single_apply]

theorem simplex_positive_mass_le_one {d : ℕ} {a : ℤ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : VertexIndex d) (k : Option (Fin d)) :
    ∑ i, max ((localBasis d a t).repr (simplexNormal d a k) i) 0 ≤ 1 := by
  by_cases hk : k = t.2
  · subst k
    exact omitted_positive_mass_le_one ha ha1 t
  · have hactive : ∃ j : Fin (d + 1), localBasis d a t j = simplexNormal d a k := by
      cases k with
      | none =>
          cases ht : t.2 with
          | none => exact (hk ht.symm).elim
          | some j => exact ⟨j.castSucc, by simp [localBasis_castSucc, ht]⟩
      | some j =>
          exact ⟨j.castSucc, by simp [localBasis_castSucc, Ne.symm hk]⟩
    obtain ⟨j, hj⟩ := hactive
    rw [← hj, basis_vector_positive_mass]

theorem cap_positive_mass_le_one (d : ℕ) (a : ℤ) (t : VertexIndex d) (b : Bool) :
    ∑ i, max ((localBasis d a t).repr (capNormal d b) i) 0 ≤ 1 := by
  simp_rw [localBasis_repr]
  rw [Fin.sum_univ_castSucc]
  rcases t with ⟨c, k⟩
  cases k <;> cases c <;> cases b <;>
    simp [cornerEquiv, constantCornerEquiv, otherCornerEquiv, capNormal, height]

theorem normals_positive_mass_le_one {d : ℕ} {a : ℤ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : VertexIndex d)
    (u : Lattice (d + 1)) (hu : u ∈ normals d a) :
    ∑ i, max ((localBasis d a t).repr u i) 0 ≤ 1 := by
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    exact simplex_positive_mass_le_one ha ha1 t k
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hu
    exact cap_positive_mass_le_one d a t b

theorem normals_uniform_of_le_one {d : ℕ} {a : ℤ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a ≤ d) (ha1 : a ≤ 1) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (d + 1)))
      (fun u : {u // u ∈ normals d a} => u.val) := by
  let P := presentation d a hd ha had
  apply BasisCover.uniform_of_basis_cover P.basis
  · intro x
    obtain ⟨v, hv⟩ := P.exists_nonnegative_basis_coordinates (embed x)
    refine ⟨v, ?_⟩
    intro i
    have hi := hv i
    rw [realCoordinates_embed] at hi
    exact_mod_cast hi
  · intro v u
    exact normals_positive_mass_le_one ha ha1 (vertexIndex v) u.val u.property

def obstructionFamily (d : ℕ) (a : ℤ) : Fin (d + 1) → Lattice (d + 1) :=
  Fin.lastCases (simplexNormal d a none) (fun i => simplexNormal d a (some i))

theorem obstructionFamily_eq_update (d : ℕ) (a : ℤ) :
    obstructionFamily d a = Function.update (Pi.basisFun ℤ (Fin (d + 1)))
      (Fin.last d) (simplexNormal d a none) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [obstructionFamily]
  · ext h
    refine Fin.lastCases ?_ (fun k => ?_) h <;>
      simp [obstructionFamily, simplexNormal, Pi.basisFun_apply, Pi.single_apply]

/-- The complete maximal minor consisting of all simplex normals. -/
theorem obstructing_det (d : ℕ) (a : ℤ) :
    (Pi.basisFun ℤ (Fin (d + 1))).det (obstructionFamily d a) = a := by
  rw [obstructionFamily_eq_update, IntegralRigidity.det_replace_basis]
  simp [Pi.basisFun_repr, simplexNormal]

theorem obstructionFamily_mem (d : ℕ) (a : ℤ) (i : Fin (d + 1)) :
    obstructionFamily d a i ∈ normals d a := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [obstructionFamily, Fin.lastCases_last, Fin.lastCases_castSucc]
  · exact simplexNormal_mem _ _ _
  · exact simplexNormal_mem _ _ _

theorem normals_uniform_iff {d : ℕ} {a : ℤ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a ≤ d) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (d + 1)))
      (fun u : {u // u ∈ normals d a} => u.val) ↔ a ≤ 1 := by
  constructor
  · intro h
    have hb := h (fun i => ⟨obstructionFamily d a i, obstructionFamily_mem d a i⟩)
    change |(Pi.basisFun ℤ (Fin (d + 1))).det (obstructionFamily d a)| ≤ 1 at hb
    rwa [obstructing_det, abs_of_nonneg ha] at hb
  · exact normals_uniform_of_le_one hd ha had

theorem geometric_normals_uniform_iff {d : ℕ} {a : ℤ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a ≤ d) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin (d + 1)))
      (fun u : {u // u ∈ (presentation d a hd ha had).geometricFacetNormals} => u.val)
      ↔ a ≤ 1 := by
  rw [geometricFacetNormals_eq]
  exact normals_uniform_iff hd ha had

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.obstructing_det
#print axioms Unimodular.SegmentSimplexBundle.normals_uniform_iff
#print axioms Unimodular.SegmentSimplexBundle.geometric_normals_uniform_iff
