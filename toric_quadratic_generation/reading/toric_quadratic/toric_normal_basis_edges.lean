module

public import PaperVerification.ToricPolytopeSupport
public import PaperVerification.ToricStarDualBasis

@[expose] public section

/-!
# Actual primitive edges dual to a full normal-cone basis

Equality of actual integral basis cones gives a permutation, with no
rescaling. Its dual identifies every basis direction with a genuine edge
of the smooth polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem integral_bases_perm_of_equal_ray_cones {n : ℕ}
    (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : latticeRayCone (Finset.univ.image b) = latticeRayCone (Finset.univ.image c)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, b i = c (σ i) := by
  have hcoords (b c : Module.Basis (Fin n) ℤ (Lattice n))
      (hcone : latticeRayCone (Finset.univ.image b) = latticeRayCone (Finset.univ.image c)) :
      ∀ i j, 0 ≤ b.repr (c j) i := by
    intro i j
    have hc : embed n (c j) ∈ latticeRayCone (Finset.univ.image b) := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    have hi := ((mem_latticeRayCone_basis_iff b Finset.univ _).mp hc).1 i
    rw [integralBasisReal_repr] at hi
    exact_mod_cast hi
  exact integral_bases_perm_of_nonnegative_coordinates b c (hcoords b c hcone)
    (hcoords c b hcone.symm)

theorem integralDualBasis_of_permuted_normals {n : ℕ}
    (d c : Module.Basis (Fin n) ℤ (Lattice n)) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, d i = integralDualBasis c (σ i)) :
    ∀ i, integralDualBasis d i = c (σ i) := by
  intro i
  apply (integralDualBasis d).ext_elem
  intro j
  rw [Module.Basis.repr_self_apply, integralDualBasis_repr, hσ j]
  have h := integralDualBasis_pairing c (σ j) (c (σ i))
  have hpair : (∑ k, c (σ i) k * integralDualBasis c (σ j) k) =
      if i = j then (1 : ℤ) else 0 := by
    simpa only [Module.Basis.repr_self_apply, σ.injective.eq_iff, mul_comm] using h
  exact hpair.symm

/-- A smooth cone containing a complete basis cone has the full ambient
number of rays. This is proved by coordinates, without a purity assumption. -/
theorem SmoothCompleteFan.card_eq_dim_of_basis_cone_le {n : ℕ}
    («Σ» : SmoothCompleteFan n) {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hle : latticeRayCone (Finset.univ.image d) ≤ latticeRayCone s) :
    s.card = n := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  have hI : I = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have hz (k : Fin n) :
        (integralBasisReal b).repr (integralBasisReal d k) i = 0 := by
      have hk := hle (latticeRayCone_generator (Finset.univ.image d)
        (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩))
      have hzero := ((mem_latticeRayCone_basis_iff b I _).mp hk).2 i hi
      simpa only [integralBasisReal_apply] using hzero
    have he := congrArg (fun x => (integralBasisReal b).repr x i)
      ((integralBasisReal d).sum_repr (integralBasisReal b i))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      hz, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      Module.Basis.repr_self_apply, if_pos rfl] at he
    norm_num at he
  rw [hI, Finset.card_image_of_injective _ b.injective, Finset.card_fin]

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- A full actual integral normal basis supplies the literal primitive
edge basis at its vertex, including all positive integer edge lengths. -/
theorem full_normal_basis_edges (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier)
    (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hcone : P.normalCone v =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n))) :
    ∃ (vZ : Lattice n) (lengths : Fin n → ℕ), embed n vZ = v ∧
      ∀ i, 0 < lengths i ∧ P.IsEdge (embed n vZ)
        (embed n (vZ + (lengths i : ℤ) • integralDualBasis d i)) := by
  let b := integralDualBasis d
  have horthant : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - v) i := by
    intro x hx i
    have hi : embed n (d i) ∈ P.normalCone v := by
      rw [hcone]
      exact latticeRayCone_generator _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have h := hi x hx
    rw [integralDualBasis_real_repr]
    simpa only [integralBasisReal_apply, Pi.sub_apply, mul_comm] using h
  have hvertex := P.extreme_of_supporting_basis v hv (integralBasisReal b) horthant
  obtain ⟨vZ, c, lengths, hvZ, hedges, hcoord⟩ := P.smooth_vertex_basis_cone hP v hvertex
  have hedges' : ∀ i, 0 < lengths i ∧ P.IsEdge (embed n vZ)
      (embed n (vZ + (lengths i : ℤ) • c i)) := by
    simpa only [hvZ] using hedges
  have hcoord' : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal c).repr (x - embed n vZ) i := by
    simpa only [hvZ] using hcoord
  have hconeC : P.normalCone v =
      (latticeRayCone (Finset.univ.image (integralDualBasis c)) : Set (Ambient n)) := by
    simpa only [hvZ] using P.normalCone_eq_latticeRayCone vZ c lengths hedges' hcoord'
  have heq : latticeRayCone (Finset.univ.image d) =
      latticeRayCone (Finset.univ.image (integralDualBasis c)) :=
    SetLike.coe_injective (hcone.symm.trans hconeC)
  obtain ⟨σ, hσ⟩ := integral_bases_perm_of_equal_ray_cones d (integralDualBasis c) heq
  have hb := integralDualBasis_of_permuted_normals d c σ hσ
  refine ⟨vZ, fun i => lengths (σ i), hvZ, ?_⟩
  intro i
  simpa only [hb i] using hedges' (σ i)

end LatticePolytope

end PaperVerification.ToricGeometry
