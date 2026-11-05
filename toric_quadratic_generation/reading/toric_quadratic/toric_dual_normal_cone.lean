module
public import PaperVerification.ToricNormalFan
public import PaperVerification.ToricFanFoundations
public import Mathlib.LinearAlgebra.Matrix.Dual
@[expose] public section
/-!
# Integral dual bases of actual smooth normal cones

The standard coordinate pairing identifies the dual lattice with the original
coordinate lattice. Under this genuine integral linear equivalence, the dual of
a primitive edge basis is again an integral basis. Its nonnegative real span is
exactly the ordinary supporting normal cone of the polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators

/-- The dual integral basis, represented in the standard coordinate lattice by
the ordinary dot-product pairing. -/
def integralDualBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) ℤ (Lattice n) :=
  b.dualBasis.map (dotProductEquiv ℤ (Fin n)).symm

/-- The defining duality holds for every lattice vector, without any
primitivity or index assumption beyond the genuine integral basis. -/
@[simp] theorem integralDualBasis_pairing {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (z : Lattice n) :
    (∑ j, integralDualBasis b i j * z j) = b.repr z i := by
  rw [integralDualBasis, Module.Basis.map_apply]
  change (dotProductEquiv ℤ (Fin n)
    ((dotProductEquiv ℤ (Fin n)).symm (b.dualBasis i))) z = _
  rw [LinearEquiv.apply_symm_apply]
  exact b.dualBasis_apply i z

/-- Coordinates in the dual integral basis are evaluations on the original
basis vectors. -/
@[simp] theorem integralDualBasis_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (z : Lattice n) (i : Fin n) :
    (integralDualBasis b).repr z i = ∑ j, z j * b i j := by
  change b.dualBasis.repr ((dotProductEquiv ℤ (Fin n)) z) i = _
  rw [Module.Basis.dualBasis_repr]
  rfl

/-- Real extension of the integral duality. -/
@[simp] theorem integralDualBasis_real_pairing {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (x : Ambient n) :
    (∑ j, embed n (integralDualBasis b i) j * x j) =
      (integralBasisReal b).repr x i := by
  let f : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (embed n (integralDualBasis b i))
  have hf : f = (integralBasisReal b).coord i := by
    apply (integralBasisReal b).ext
    intro k
    change (∑ j, embed n (integralDualBasis b i) j *
      integralBasisReal b k j) = (integralBasisReal b).repr (integralBasisReal b k) i
    rw [integralBasisReal_apply, integralBasisReal_repr]
    have hz := integralDualBasis_pairing b i (b k)
    change (∑ j, (integralDualBasis b i j : ℝ) * (b k j : ℝ)) =
      (b.repr (b k) i : ℝ)
    exact_mod_cast hz
  exact LinearMap.congr_fun hf x

/-- The primitive normal vector is precisely the coefficient vector of the
corresponding real dual coordinate functional. -/
theorem embed_integralDualBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    embed n (integralDualBasis b i) = dualVector ((integralBasisReal b).coord i) := by
  funext j
  change embed n (integralDualBasis b i) j =
    (integralBasisReal b).repr (Pi.basisFun ℝ (Fin n) j) i
  calc
    embed n (integralDualBasis b i) j =
        embed n (integralDualBasis b i) ⬝ᵥ Pi.basisFun ℝ (Fin n) j := by
      rw [Pi.basisFun_apply, dotProduct_single_one]
    _ = _ := integralDualBasis_real_pairing b i (Pi.basisFun ℝ (Fin n) j)

/-- Coordinates in the real dual basis are ordinary pairings with the real
edge basis. This identifies nonnegative coordinates with supporting normals. -/
@[simp] theorem integralDualBasis_real_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (u : Ambient n) (i : Fin n) :
    (integralBasisReal (integralDualBasis b)).repr u i =
      ∑ j, u j * integralBasisReal b i j := by
  let d := integralBasisReal (integralDualBasis b)
  let f : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (integralBasisReal b i)
  have hf : d.coord i = f := by
    apply d.ext
    intro k
    change d.repr (d k) i = ∑ j, integralBasisReal b i j * d k j
    rw [Module.Basis.repr_self_apply]
    have hp := integralDualBasis_real_pairing b k (integralBasisReal b i)
    rw [Module.Basis.repr_self_apply] at hp
    simpa only [d, integralBasisReal_apply, mul_comm, eq_comm] using hp.symm
  have h := LinearMap.congr_fun hf u
  change d.repr u i = (integralBasisReal b i) ⬝ᵥ u at h
  simpa only [d, dotProduct, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Membership of the actual supporting normal cone is exactly
nonnegativity on a complete primitive edge basis. -/
theorem mem_normalCone_iff_basis_pairing
    (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (u : Ambient n) :
    u ∈ P.normalCone (embed n vZ) ↔
      ∀ i, 0 ≤ ∑ j, u j * integralBasisReal b i j := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
  have hnormal : u ∈ P.normalCone (embed n vZ) ↔
      ∀ x ∈ P.carrier, f (embed n vZ) ≤ f x := by
    change (∀ x ∈ P.carrier, 0 ≤ f (x - embed n vZ)) ↔ _
    simp only [map_sub, sub_nonneg]
  rw [hnormal]
  constructor
  · intro hu i
    have h := hu _ (P.edge_endpoints_extreme (hedges i).2).2.1
    rw [map_add, embed_int_smul, map_add, map_smul,
      smul_eq_mul, Int.cast_natCast, ← integralBasisReal_apply b i] at h
    have hl : (0 : ℝ) < lengths i := by exact_mod_cast (hedges i).1
    have hnonneg : 0 ≤ f (integralBasisReal b i) := by nlinarith
    exact hnonneg
  · intro hu x hx
    exact linear_le_of_basis_coordinates (integralBasisReal b) f
      (embed n vZ) x hu (hcone x hx)

/-- The actual normal cone is the nonnegative real cone generated by the
genuine primitive dual integral basis. -/
theorem normalCone_eq_latticeRayCone
    (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
    (lengths : Fin n → ℕ)
    (hedges : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (hcone : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i) :
    P.normalCone (embed n vZ) =
      (latticeRayCone (Finset.univ.image (integralDualBasis b)) : Set (Ambient n)) := by
  ext u
  change (u ∈ P.normalCone (embed n vZ)) ↔
    u ∈ latticeRayCone (Finset.univ.image (integralDualBasis b))
  rw [P.mem_normalCone_iff_basis_pairing vZ b lengths hedges hcone u,
    mem_latticeRayCone_basis_iff]
  simp only [Finset.mem_univ, not_true_eq_false, false_implies, implies_true,
    and_true, integralDualBasis_real_repr]

/-- Every actual smooth vertex normal cone is generated by a complete
primitive integral basis of normals. No normal-fan smoothness is assumed. -/
theorem smooth_vertex_normalCone_basis (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ d : Module.Basis (Fin n) ℤ (Lattice n),
      P.normalCone v = (latticeRayCone (Finset.univ.image d) : Set (Ambient n)) := by
  obtain ⟨vZ, b, lengths, hvZ, hedges, hcone⟩ := P.smooth_vertex_basis_cone hP v hv
  refine ⟨integralDualBasis b, ?_⟩
  have hedges' : ∀ i, 0 < lengths i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)) := by
    simpa only [hvZ] using hedges
  have hcone' : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i := by
    simpa only [hvZ] using hcone
  simpa only [hvZ] using P.normalCone_eq_latticeRayCone vZ b lengths hedges' hcone'

end LatticePolytope

end PaperVerification.ToricGeometry

