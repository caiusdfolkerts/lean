module
public import PaperVerification.ToricStatements
public import PaperVerification.ToricCornerBoxes
public import Mathlib.Algebra.Module.ZLattice.Basic
@[expose] public section
/-!
# Integral edge bases and real corner boxes

The integral basis appearing in the literal smoothness definition is extended to
an actual real basis. The extension preserves every lattice coordinate. Thus
integer supporting normals and the geometric edge lengths can be used directly
in the real box covering argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators

@[simp] theorem embed_int_smul {n : ℕ} (k : ℤ) (z : Lattice n) :
    embed n (k • z) = (k : ℝ) • embed n z := by
  ext i
  simp [embed, Int.cast_mul]

/-- The standard integral lattice as a genuine real-space submodule. -/
def standardIntegerLattice (n : ℕ) : Submodule ℤ (Ambient n) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

instance standardIntegerLattice_discreteTopology (n : ℕ) :
    DiscreteTopology (standardIntegerLattice n) := by
  exact ZSpan.discreteTopology_pi_basisFun (ι := Fin n)

instance standardIntegerLattice_isZLattice (n : ℕ) :
    IsZLattice ℝ (standardIntegerLattice n) := by
  dsimp [standardIntegerLattice]
  infer_instance

/-- The usual coordinate lattice and its embedded real submodule are linearly equivalent. -/
def standardLatticeEquiv (n : ℕ) : Lattice n ≃ₗ[ℤ] standardIntegerLattice n :=
  ((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ).equivFun.symm

@[simp] theorem standardLatticeEquiv_coe {n : ℕ} (z : Lattice n) :
    ((standardLatticeEquiv n z : standardIntegerLattice n) : Ambient n) = embed n z := by
  classical
  change (((Pi.basisFun ℝ (Fin n)).restrictScalars ℤ).equivFun.symm z : Ambient n) = _
  rw [Module.Basis.equivFun_symm_apply]
  ext j
  simp [Submodule.coe_sum, Submodule.coe_smul_of_tower, Module.Basis.restrictScalars_apply,
    Finset.sum_apply, Pi.basisFun_apply, Pi.single_apply, embed]

/-- Every integral basis of the coordinate lattice gives the same vectors as a real basis. -/
def integralBasisReal {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Module.Basis (Fin n) ℝ (Ambient n) :=
  (b.map (standardLatticeEquiv n)).ofZLatticeBasis ℝ (standardIntegerLattice n)

@[simp] theorem integralBasisReal_apply {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    integralBasisReal b i = embed n (b i) := by
  simp [integralBasisReal]

/-- Real coordinates of a lattice vector in an integral basis are exactly its integer coordinates. -/
@[simp] theorem integralBasisReal_repr {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (z : Lattice n) (i : Fin n) :
    (integralBasisReal b).repr (embed n z) i = (b.repr z i : ℝ) := by
  have h := (b.map (standardLatticeEquiv n)).ofZLatticeBasis_repr_apply
    ℝ (standardIntegerLattice n) (standardLatticeEquiv n z) i
  simpa only [integralBasisReal, standardLatticeEquiv_coe, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using h

/-- Each real dual basis functional is integral on the embedded coordinate lattice. -/
theorem integralBasisReal_coordinate_integral {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) (z : Lattice n) :
    ∃ k : ℤ, (integralBasisReal b).repr (embed n z) i = k :=
  ⟨b.repr z i, integralBasisReal_repr b z i⟩

namespace LatticePolytope

/-- A specified integral edge basis with the required actual edge lengths
contains its entire unit corner box. This formulation keeps the chosen basis
fixed when matching two polytopes with the same normal fan. -/
theorem integral_edges_unit_corner_box {n : ℕ} (P : LatticePolytope n)
    (hlength : P.EdgesAtLeast n) (vZ : Lattice n)
    (hv : embed n vZ ∈ P.carrier)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (lengths : Fin n → ℕ)
    (hedges : ∀ i, P.IsEdge (embed n vZ) (embed n (vZ + (lengths i : ℤ) • b i)))
    (t : Fin n → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    embed n vZ + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  by_cases hn : n = 0
  · subst n
    exact (Subsingleton.elim (embed 0 vZ)
      (embed 0 vZ + ∑ i, t i • integralBasisReal b i)) ▸ hv
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply PaperVerification.Toric.unit_corner_box_of_long_segments hnpos P.carrier
      (convex_convexHull ℝ _) (embed n vZ) hv (integralBasisReal b)
      (fun i => (lengths i : ℝ)) ?_ ?_ t ht
    · intro i
      exact_mod_cast P.edge_basis_length_bound hlength vZ b i (lengths i) (hedges i)
    · intro i
      have hmem := (P.edge_endpoints_extreme (hedges i)).2.1
      simpa only [map_add, embed_int_smul, integralBasisReal_apply,
        Int.cast_natCast] using hmem

/-- The ordinary unit corner box supplied by every smooth vertex and the exact
edge-length bound of Theorem 1.1. This includes dimension zero. -/
theorem smooth_unit_corner_box {n : ℕ} (P : LatticePolytope n)
    (hP : P.Smooth) (hlength : P.EdgesAtLeast n)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)),
      embed n vZ = v ∧
      ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
        v + ∑ i, t i • integralBasisReal b i ∈ P.carrier := by
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨vZ, b, hvZ, ?_⟩
  intro t ht
  by_cases hn : n = 0
  · subst n
    exact (Subsingleton.elim v (v + ∑ i, t i • integralBasisReal b i)) ▸ hv.1
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply PaperVerification.Toric.unit_corner_box_of_long_segments hnpos P.carrier
      (convex_convexHull ℝ _) v hv.1 (integralBasisReal b)
      (fun i => (lengths i : ℝ)) ?_ ?_ t ht
    · intro i
      have hbound := P.edge_basis_length_bound hlength vZ b i (lengths i)
        (by simpa only [hvZ] using (hedges i).2)
      exact_mod_cast hbound
    · intro i
      have hmem := (P.edge_endpoints_extreme (hedges i).2).2.1
      have he : embed n (vZ + (lengths i : ℤ) • b i) =
          v + (lengths i : ℝ) • integralBasisReal b i := by
        rw [map_add, hvZ, integralBasisReal_apply]
        ext j
        simp [embed, Int.cast_mul]
      rwa [he] at hmem

end LatticePolytope

end PaperVerification.ToricGeometry
