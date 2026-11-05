module
public import PaperVerification.ToricIntegralBasis
public import PaperVerification.ToricVertexCone
public import PaperVerification.ToricShiftedPolytopes
public import Mathlib.Data.Set.Finite.Lemmas
@[expose] public section
/-!
# Actual vertices, basis cones, and normal-fan matching

All normal cones below are the ordinary supporting cones from the literal
polytope definition. The lemmas identify their dual basis coordinates and
show that equality of integral basis cones preserves primitive directions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators
open PaperVerification.ToricVertexCone

/-- The coefficient vector representing a real linear functional in the
standard coordinate pairing used by the paper's normal cones. -/
def dualVector {n : ℕ} (f : Ambient n →ₗ[ℝ] ℝ) : Ambient n :=
  fun i => f (Pi.basisFun ℝ (Fin n) i)

@[simp] theorem dualVector_pairing {n : ℕ}
    (f : Ambient n →ₗ[ℝ] ℝ) (x y : Ambient n) :
    (∑ i, dualVector f i * (y i - x i)) = f (y - x) := by
  have h := congrArg f ((Pi.basisFun ℝ (Fin n)).sum_repr (y - x))
  simpa [dualVector, map_sum, map_smul, smul_eq_mul, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The actual vertex set is finite, independently of the chosen redundant generators. -/
theorem finite_vertices : (P.carrier.extremePoints ℝ).Finite := by
  exact (P.generators.finite_toSet.image (embed n)).subset extremePoints_convexHull_subset

/-- The convex hull of the actual vertices equals the whole polytope. -/
theorem hull_vertices : convexHull ℝ (P.carrier.extremePoints ℝ) = P.carrier := by
  classical
  have h := finite_hull_eq_hull_extremePoints (P.generators.image (embed n))
  simpa [carrier, Finset.coe_image] using h

/-- A lattice polytope has an actual vertex, also in dimension zero. -/
theorem vertices_nonempty : (P.carrier.extremePoints ℝ).Nonempty := by
  apply (convexHull_nonempty_iff (𝕜 := ℝ)).mp
  rw [P.hull_vertices]
  obtain ⟨z, hz⟩ := P.nonempty
  exact ⟨embed n z, subset_convexHull ℝ _ ⟨z, hz, rfl⟩⟩

/-- Every linear functional attains its minimum at an actual vertex. -/
theorem exists_minimizing_vertex (f : Ambient n →ₗ[ℝ] ℝ) :
    ∃ v ∈ P.carrier.extremePoints ℝ, ∀ x ∈ P.carrier, f v ≤ f x := by
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image (P.carrier.extremePoints ℝ)
    f P.finite_vertices P.vertices_nonempty
  refine ⟨v, hv, ?_⟩
  rw [← P.hull_vertices]
  exact convexHull_min hmin ((convex_Ici (f v)).linear_preimage f)

/-- A linear functional is in the actual normal cone precisely when it is
minimized at the selected point. -/
theorem dualVector_mem_normalCone_iff (f : Ambient n →ₗ[ℝ] ℝ) (v : Ambient n) :
    dualVector f ∈ P.normalCone v ↔ ∀ x ∈ P.carrier, f v ≤ f x := by
  simp only [normalCone, Set.mem_setOf_eq, dualVector_pairing, map_sub, sub_nonneg]

/-- Every smooth vertex has a supporting orthant in its actual primitive
integral edge basis. This is a consequence of the finite-polytope tangent-cone
argument, not an extra clause in the definition of smoothness. -/
theorem smooth_vertex_basis_cone (hP : P.Smooth)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n))
      (lengths : Fin n → ℕ),
      embed n vZ = v ∧
      (∀ i, 0 < lengths i ∧ P.IsEdge v (embed n (vZ + (lengths i : ℤ) • b i))) ∧
      (∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i) := by
  classical
  obtain ⟨vZ, b, lengths, hvZ, hedges, hall⟩ := hP v hv
  refine ⟨vZ, b, lengths, hvZ, hedges, ?_⟩
  let s := P.generators.image (embed n)
  have hcarrier : convexHull ℝ (s : Set (Ambient n)) = P.carrier := by
    simp [s, carrier, Finset.coe_image]
  have hv' : v ∈ (convexHull ℝ (s : Set (Ambient n))).extremePoints ℝ := by
    simpa only [hcarrier] using hv
  have hedgeRay : ∀ w : Ambient n, v ≠ w →
      IsExtreme ℝ (convexHull ℝ (s : Set (Ambient n))) (segment ℝ v w) →
      ∃ i : Fin n, ∃ a : ℝ, 0 ≤ a ∧ w - v = a • integralBasisReal b i := by
    intro w hvw hface
    have hedge : P.IsEdge v w := ⟨hvw, by simpa only [hcarrier] using hface⟩
    obtain ⟨i, rfl⟩ := hall w hedge
    refine ⟨i, (lengths i : ℝ), Nat.cast_nonneg _, ?_⟩
    rw [map_add, hvZ, integralBasisReal_apply, add_sub_cancel_left]
    ext j
    simp [embed, Int.cast_mul]
  have h := nonnegative_basis_coordinates_of_incident_edges s v hv'
    (integralBasisReal b) hedgeRay
  simpa only [hcarrier] using h

/-- A family containing the primitive edge basis at every actual vertex is
complete: every linear functional is nonnegative on one whole basis. -/
theorem smooth_basis_cones_complete
    (b : P.carrier.extremePoints ℝ → Module.Basis (Fin n) ℤ (Lattice n))
    (vZ : P.carrier.extremePoints ℝ → Lattice n)
    (lengths : P.carrier.extremePoints ℝ → Fin n → ℕ)
    (hvZ : ∀ v, embed n (vZ v) = (v : Ambient n))
    (hedges : ∀ v i, 0 < lengths v i ∧
      P.IsEdge v (embed n (vZ v + (lengths v i : ℤ) • b v i)))
    (f : Ambient n →ₗ[ℝ] ℝ) :
    ∃ v : P.carrier.extremePoints ℝ, ∀ i, 0 ≤ f (integralBasisReal (b v) i) := by
  obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
  refine ⟨⟨v, hv⟩, ?_⟩
  intro i
  let j : P.carrier.extremePoints ℝ := ⟨v, hv⟩
  have hedge := (hedges j i).2
  have hm := hmin _ (P.edge_endpoints_extreme hedge).2.1
  have he : embed n (vZ j + (lengths j i : ℤ) • b j i) =
      v + (lengths j i : ℝ) • integralBasisReal (b j) i := by
    rw [map_add, hvZ, integralBasisReal_apply]
    ext k
    simp [embed, Int.cast_mul, j]
  rw [he, map_add, map_smul, smul_eq_mul] at hm
  have hl : (0 : ℝ) < lengths j i := by exact_mod_cast (hedges j i).1
  nlinarith

/-- A point with a supporting real basis orthant is an actual vertex. -/
theorem extreme_of_supporting_basis (v : Ambient n) (hv : v ∈ P.carrier)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (hcone : ∀ x ∈ P.carrier, ∀ i, 0 ≤ b.repr (x - v) i) :
    v ∈ P.carrier.extremePoints ℝ := by
  refine ⟨hv, ?_⟩
  intro x hx y hy hseg
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  apply b.ext_elem
  intro i
  have hx0 := hcone x hx i
  have hy0 := hcone y hy i
  have he' := congrArg (fun z => b.repr z i) he
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at he'
  simp only [map_sub, Finsupp.sub_apply] at hx0 hy0
  have hbalance : r * (b.repr x i - b.repr v i) +
      s * (b.repr y i - b.repr v i) = 0 := by
    calc
      r * (b.repr x i - b.repr v i) + s * (b.repr y i - b.repr v i) =
          (r * b.repr x i + s * b.repr y i) - (r + s) * b.repr v i := by ring
      _ = 0 := by rw [he', hrs, one_mul, sub_self]
  have hrx := mul_nonneg hr.le hx0
  have hsy := mul_nonneg hs.le hy0
  have hzero : r * (b.repr x i - b.repr v i) = 0 := by
    linarith only [hbalance, hrx, hsy]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hr.ne')

/-- Equality of the genuine normal fans matches every supporting-basis vertex
with an actual vertex of the other polytope and preserves its supporting cone. -/
theorem exists_matched_vertex (Q : LatticePolytope n) (hfan : P.SameNormalFan Q)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (hcone : ∀ x ∈ P.carrier, ∀ i, 0 ≤ b.repr (x - v) i) :
    ∃ w ∈ Q.carrier.extremePoints ℝ, P.normalCone v = Q.normalCone w ∧
      ∀ x ∈ Q.carrier, ∀ i, 0 ≤ b.repr (x - w) i := by
  have hmem : P.normalCone v ∈ P.normalFan := ⟨v, hv.1, rfl⟩
  rw [show P.normalFan = Q.normalFan from hfan] at hmem
  obtain ⟨w, hw, hcw⟩ := hmem
  have hnew : ∀ x ∈ Q.carrier, ∀ i, 0 ≤ b.repr (x - w) i := by
    intro x hx i
    have hi : dualVector (b.coord i) ∈ P.normalCone v := by
      intro y hy
      simpa only [dualVector_pairing, Module.Basis.coord_apply] using hcone y hy i
    rw [hcw] at hi
    have h := hi x hx
    simpa only [dualVector_pairing, Module.Basis.coord_apply] using h
  exact ⟨w, Q.extreme_of_supporting_basis w hw b hnew, hcw, hnew⟩

end LatticePolytope

/-- Two integral bases spanning the same positive orthant differ by a permutation,
with no rescaling. The proof uses nonnegative integer transition coefficients. -/
theorem integral_bases_perm_of_nonnegative_coordinates {K M : Type*}
    [Fintype K] [AddCommGroup M] [Module ℤ M]
    (b c : Module.Basis K ℤ M)
    (hbc : ∀ i j, 0 ≤ b.repr (c j) i)
    (hcb : ∀ i j, 0 ≤ c.repr (b j) i) :
    ∃ σ : Equiv.Perm K, ∀ i, b i = c (σ i) := by
  classical
  have hcoord (i k : K) :
      (∑ j, c.repr (b i) j * b.repr (c j) k) = if i = k then 1 else 0 := by
    have h := congrArg (fun x : M => b.repr x k) (c.sum_repr (b i))
    simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] using h
  have hex (i : K) : ∃ j, c j = b i := by
    have hdiag : (∑ j, c.repr (b i) j * b.repr (c j) i) = 1 := by
      simpa using hcoord i i
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (show (∑ j, c.repr (b i) j * b.repr (c j) i) ≠ 0 by rw [hdiag]; norm_num)
    have ha0 := hcb j i
    have hb0 := hbc i j
    have ha1 : 1 ≤ c.repr (b i) j := by
      have hne := (mul_ne_zero_iff.mp hj).1
      omega
    have hb1 : 1 ≤ b.repr (c j) i := by
      have hne := (mul_ne_zero_iff.mp hj).2
      omega
    have hp := Finset.single_le_sum
      (fun k _ => mul_nonneg (hcb k i) (hbc i k)) (Finset.mem_univ j)
    rw [hdiag] at hp
    have ha_le : c.repr (b i) j ≤ c.repr (b i) j * b.repr (c j) i := by
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hb1)]
    have ha : c.repr (b i) j = 1 := by omega
    have hb : b.repr (c j) i = 1 := by rw [ha, one_mul] at hp; omega
    refine ⟨j, b.ext_elem (fun k => ?_)⟩
    by_cases hik : i = k
    · subst k
      simpa only [Module.Basis.repr_self, Finsupp.single_eq_same] using hb
    · have hpk := Finset.single_le_sum
        (fun l _ => mul_nonneg (hcb l i) (hbc k l)) (Finset.mem_univ j)
      rw [hcoord i k, if_neg hik, ha, one_mul] at hpk
      have hk : b.repr (c j) k = 0 := le_antisymm hpk (hbc k j)
      simpa only [Module.Basis.repr_self, Finsupp.single_apply, if_neg hik] using hk
  choose σ hσ using hex
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply b.injective
    rw [← hσ i, ← hσ j, hij]
  exact ⟨Equiv.ofBijective σ
    ((Fintype.bijective_iff_injective_and_card σ).mpr ⟨hσinj, rfl⟩),
    fun i => (hσ i).symm⟩

/-- A positive-length integral edge contained in a basis orthant has
nonnegative integer coordinates in that basis. -/
theorem basis_coordinates_nonneg_of_edge {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (v z : Lattice n) (k : ℕ) (hk : 0 < k)
    (h : ∀ i, 0 ≤ (integralBasisReal b).repr
      (embed n (v + (k : ℤ) • z) - embed n v) i) :
    ∀ i, 0 ≤ b.repr z i := by
  intro i
  have hi := h i
  rw [map_add, add_sub_cancel_left, embed_int_smul, map_smul,
    Finsupp.smul_apply, smul_eq_mul, integralBasisReal_repr] at hi
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : (0 : ℝ) ≤ (b.repr z i : ℝ) := by
    push_cast at hi
    nlinarith
  exact_mod_cast hn

namespace LatticePolytope

/-- The actual common normal fan matches smooth vertices with the same
primitive lattice edge directions. Equality of the directions, rather than
merely equality of their rays, follows from integral-basis primitivity. -/
theorem sameNormalFan_matched_bases {n : ℕ} (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (v : Ambient n) (hv : v ∈ P.carrier.extremePoints ℝ) :
    ∃ (w : Ambient n) (vZ wZ : Lattice n)
      (b : Module.Basis (Fin n) ℤ (Lattice n)) (p q : Fin n → ℕ),
      w ∈ Q.carrier.extremePoints ℝ ∧ embed n vZ = v ∧ embed n wZ = w ∧
      P.normalCone v = Q.normalCone w ∧
      (∀ i, 0 < p i ∧ P.IsEdge v (embed n (vZ + (p i : ℤ) • b i))) ∧
      (∀ i, 0 < q i ∧ Q.IsEdge w (embed n (wZ + (q i : ℤ) • b i))) ∧
      (∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i) ∧
      (∀ x ∈ Q.carrier, ∀ i, 0 ≤ (integralBasisReal b).repr (x - w) i) := by
  obtain ⟨vZ, b, p, hvZ, hp, hPb⟩ := P.smooth_vertex_basis_cone hP v hv
  obtain ⟨w, hw, hcones, hQb⟩ :=
    P.exists_matched_vertex Q hfan v hv (integralBasisReal b) hPb
  obtain ⟨wZ, c, q, hwZ, hq, hQc⟩ := Q.smooth_vertex_basis_cone hQ w hw
  have hPc : ∀ x ∈ P.carrier, ∀ i, 0 ≤ (integralBasisReal c).repr (x - v) i := by
    intro x hx i
    have hi : dualVector ((integralBasisReal c).coord i) ∈ Q.normalCone w := by
      intro y hy
      simpa only [dualVector_pairing, Module.Basis.coord_apply] using hQc y hy i
    rw [← hcones] at hi
    have h := hi x hx
    simpa only [dualVector_pairing, Module.Basis.coord_apply] using h
  have hbc : ∀ i j, 0 ≤ b.repr (c j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge b wZ (c j) (q j) (hq j).1
    intro k
    have h := hQb _ (Q.edge_endpoints_extreme (hq j).2).2.1 k
    simpa only [hwZ] using h
  have hcb : ∀ i j, 0 ≤ c.repr (b j) i := by
    intro i j
    apply basis_coordinates_nonneg_of_edge c vZ (b j) (p j) (hp j).1
    intro k
    have h := hPc _ (P.edge_endpoints_extreme (hp j).2).2.1 k
    simpa only [hvZ] using h
  obtain ⟨σ, hσ⟩ := integral_bases_perm_of_nonnegative_coordinates b c hbc hcb
  refine ⟨w, vZ, wZ, b, p, fun i => q (σ i), hw, hvZ, hwZ, hcones, hp, ?_, hPb, hQb⟩
  intro i
  simpa only [hσ i] using hq (σ i)

end LatticePolytope

end PaperVerification.ToricGeometry
