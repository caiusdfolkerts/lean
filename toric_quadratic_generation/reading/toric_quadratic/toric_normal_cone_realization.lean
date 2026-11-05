module
public import PaperVerification.ToricNormalConeFaces
public import Mathlib.Analysis.Convex.Combination
@[expose] public section
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

