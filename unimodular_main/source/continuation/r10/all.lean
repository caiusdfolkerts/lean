module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Continuation.R10.FiniteMinors
public import Continuation.R10.Data
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Unimodular
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Push
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Recovery.Unimodular.WeakFano.CanonicalSeed
public import Mathlib.Tactic.Choose
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Data.Set.Card
public import Continuation.Runtime.R10MatroidData

@[expose] public section

/-! ## Source module: Data -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Matrix
open scoped BigOperators

namespace Unimodular.ExplicitR10
#print axioms quotient_columns
end Unimodular.ExplicitR10


/-! ## Source module: RaySet -/
namespace Unimodular.ExplicitR10

/-- The actual finite set of the thirteen distinct lattice vectors. -/
def normalSet : Finset (Lattice 8) := Finset.univ.image rays

@[simp] theorem mem_normalSet (u : Lattice 8) :
    u ∈ normalSet ↔ ∃ i, rays i = u := by
  constructor
  · intro hu
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hu
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

theorem normalSet_card : normalSet.card = 13 := thirteen_rays

theorem zero_not_mem_normalSet : (0 : Lattice 8) ∉ normalSet := by
  rintro h
  obtain ⟨i, hi⟩ := (mem_normalSet 0).1 h
  exact rays_nonzero i hi

end Unimodular.ExplicitR10


/-! ## Source module: FiniteMinors -/
open Matrix
open scoped BigOperators

namespace Unimodular.ExplicitR10
#print axioms all_ray_determinants
end Unimodular.ExplicitR10


/-! ## Source module: Farkas -/
open scoped BigOperators

namespace Unimodular.ExplicitR10

def margins : Fin 5 → ℤ := ![7,1,3,3,4]

def standardColumns : Matrix (Fin 10) (Fin 5) ℤ :=
  ![![1,1,0,0,0], ![1,0,1,0,0], ![1,0,0,1,0], ![1,0,0,0,1],
    ![0,-1,-1,0,0], ![0,-1,0,-1,0], ![0,1,0,0,1],
    ![0,0,1,1,0], ![0,0,1,0,1], ![0,0,0,1,1]]

def repeatedEdge : Fin 13 → Fin 10 := ![0,0,1,1,2,2,3,4,5,6,7,8,9]

/-- A small exact Farkas certificate covering every set of at most four edge labels. -/
def separatingFunctionals : Matrix (Fin 12) (Fin 5) ℤ :=
  ![![0,-1,0,0,0], ![-1,1,1,-1,1], ![-1,1,-1,1,1],
    ![1,1,-1,-1,-1], ![-1,1,1,1,-1], ![-1,-1,1,-1,1],
    ![0,0,0,0,-1], ![0,0,-1,0,0], ![0,0,0,-1,0],
    ![-1,-1,-1,1,1], ![0,0,1,0,-1], ![0,0,0,1,-1]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem farkas_certificate :
    ∀ s : Finset (Fin 10), s.card ≤ 4 → ∃ k : Fin 12,
      (∀ e ∈ s, 0 ≤ ∑ j : Fin 5, separatingFunctionals k j * standardColumns e j) ∧
      (∑ j : Fin 5, separatingFunctionals k j * margins j) < 0 := by decide

/-- The certificate proves a statement about every real feasible point, without
enumerating or assuming the vertices of the polytope. -/
theorem support_card_ge_five (x : Fin 13 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, ∑ i : Fin 13, (standardColumns (repeatedEdge i) j : ℝ) * x i =
      (margins j : ℝ)) :
    5 ≤ (Finset.univ.filter (fun i => 0 < x i)).card := by
  classical
  by_contra hcard
  let T : Finset (Fin 13) := Finset.univ.filter (fun i => 0 < x i)
  let s : Finset (Fin 10) := T.image repeatedEdge
  have hT : T.card ≤ 4 := by dsimp [T]; omega
  have hs : s.card ≤ 4 := (Finset.card_image_le).trans hT
  obtain ⟨k, hk, hb⟩ := farkas_certificate s hs
  have hprod : ∀ i : Fin 13,
      0 ≤ (∑ j : Fin 5, (separatingFunctionals k j : ℝ) *
        (standardColumns (repeatedEdge i) j : ℝ)) * x i := by
    intro i
    by_cases hi : 0 < x i
    · have him : repeatedEdge i ∈ s :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
      have hh : 0 ≤ ∑ j : Fin 5, (separatingFunctionals k j : ℝ) *
          (standardColumns (repeatedEdge i) j : ℝ) := by
        exact_mod_cast hk (repeatedEdge i) him
      exact mul_nonneg hh (hx i)
    · have hzero : x i = 0 := le_antisymm (le_of_not_gt hi) (hx i)
      simp [hzero]
  have hsum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 13))) => hprod i)
  have heq :
      (∑ i : Fin 13, (∑ j : Fin 5, (separatingFunctionals k j : ℝ) *
        (standardColumns (repeatedEdge i) j : ℝ)) * x i) =
      ∑ j : Fin 5, (separatingFunctionals k j : ℝ) * (margins j : ℝ) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin 5, (separatingFunctionals k j : ℝ) *
          (∑ i : Fin 13, (standardColumns (repeatedEdge i) j : ℝ) * x i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp_rw [hAx]
  rw [heq] at hsum
  have hbR : (∑ j : Fin 5, (separatingFunctionals k j : ℝ) * (margins j : ℝ)) < 0 := by
    exact_mod_cast hb
  linarith

#print axioms support_card_ge_five
end Unimodular.ExplicitR10


/-! ## Source module: Polar -/
noncomputable section
open Matrix
open scoped BigOperators

namespace Unimodular.ExplicitR10

def rayPairing (p : Fin 8 → ℝ) (i : Fin 13) : ℝ :=
  ∑ j : Fin 8, (rays i j : ℝ) * p j

def slack (p : Fin 8 → ℝ) (i : Fin 13) : ℝ := 1 - rayPairing p i

def polar : Set (Fin 8 → ℝ) := {p | ∀ i, rayPairing p i ≤ 1}

def activeNormals (p : Fin 8 → ℝ) : Finset (Fin 13) := by
  classical
  exact Finset.univ.filter (fun i => rayPairing p i = 1)

theorem slack_equations (p : Fin 8 → ℝ) :
    ∀ j, ∑ i : Fin 13, (standardColumns (repeatedEdge i) j : ℝ) * slack p i =
      (margins j : ℝ) := by
  intro j
  fin_cases j <;>
    norm_num [slack, rayPairing, standardColumns, repeatedEdge, rays, margins,
      Fin.sum_univ_succ] <;> ring

theorem activeNormals_card_le_eight (p : Fin 8 → ℝ) (hp : p ∈ polar) :
    (activeNormals p).card ≤ 8 := by
  classical
  have hx : ∀ i, 0 ≤ slack p i := fun i => sub_nonneg.mpr (hp i)
  have hfive := support_card_ge_five (slack p) hx (slack_equations p)
  have heq : activeNormals p =
      (Finset.univ.filter (fun i : Fin 13 => 0 < slack p i))ᶜ := by
    ext i
    simp only [activeNormals, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    dsimp [slack]
    constructor
    · intro hi
      rw [hi]
      norm_num
    · intro hi
      have h := hp i
      push_neg at hi
      linarith
  rw [heq, Finset.card_compl]
  simp only [Fintype.card_fin]
  omega

def unitIndex : Fin 8 → Fin 13 := ![1,3,5,8,9,10,11,12]

theorem coordinate_slack (p : Fin 8 → ℝ) (j : Fin 8) :
    slack p (unitIndex j) = 1 - p j := by
  fin_cases j <;> simp [slack, rayPairing, unitIndex, rays, Fin.sum_univ_succ]

theorem weighted_slacks (p : Fin 8 → ℝ) :
    (∑ i : Fin 13, (positiveWeights i : ℝ) * slack p i) = 37 := by
  norm_num [positiveWeights, slack, rayPairing, rays, Fin.sum_univ_succ]
  ring

theorem coordinate_bounds (p : Fin 8 → ℝ) (hp : p ∈ polar) (j : Fin 8) :
    -36 ≤ p j ∧ p j ≤ 1 := by
  have hx : ∀ i, 0 ≤ slack p i := fun i => sub_nonneg.mpr (hp i)
  have hb : ∀ i, slack p i ≤ 37 := by
    intro i
    have hwI : 1 ≤ positiveWeights i := by
      have := positiveWeights_pos i
      omega
    have hw : (1 : ℝ) ≤ (positiveWeights i : ℝ) := by exact_mod_cast hwI
    have ht : (positiveWeights i : ℝ) * slack p i ≤ 37 := by
      rw [← weighted_slacks p]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin 13 => (positiveWeights k : ℝ) * slack p k)
        (fun k _ => mul_nonneg (by exact_mod_cast (positiveWeights_pos k).le) (hx k))
        (Finset.mem_univ i)
    have hh := mul_nonneg (sub_nonneg.mpr hw) (hx i)
    nlinarith
  have hzero := hx (unitIndex j)
  have hupper := hb (unitIndex j)
  rw [coordinate_slack] at hzero hupper
  constructor <;> linarith

theorem continuous_rayPairing (i : Fin 13) :
    Continuous (fun p : Fin 8 → ℝ => rayPairing p i) := by
  unfold rayPairing
  fun_prop

theorem polar_eq_iInter :
    polar = ⋂ i : Fin 13, {p : Fin 8 → ℝ | rayPairing p i ≤ 1} := by
  ext p
  simp [polar]

theorem isClosed_polar : IsClosed polar := by
  rw [polar_eq_iInter]
  exact isClosed_iInter (fun i => isClosed_le (continuous_rayPairing i) continuous_const)

theorem isCompact_polar : IsCompact polar := by
  have hc : IsCompact (Set.Icc (fun _ : Fin 8 => (-36 : ℝ)) (fun _ => (1 : ℝ))) :=
    isCompact_Icc
  apply hc.of_isClosed_subset isClosed_polar
  intro p hp
  exact ⟨fun j => (coordinate_bounds p hp j).1, fun j => (coordinate_bounds p hp j).2⟩

theorem convex_polar : Convex ℝ polar := by
  intro p hp q hq a b ha hb hab i
  have hpair : rayPairing (a • p + b • q) i =
      a * rayPairing p i + b * rayPairing q i := by
    simp only [rayPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hpair]
  calc
    a * rayPairing p i + b * rayPairing q i ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (hp i) ha)
        (mul_le_mul_of_nonneg_left (hq i) hb)
    _ = 1 := by nlinarith [hab]

theorem zero_mem_interior_polar : (0 : Fin 8 → ℝ) ∈ interior polar := by
  let U : Set (Fin 8 → ℝ) := ⋂ i : Fin 13, {p | rayPairing p i < 1}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_rayPairing i) continuous_const)
  have hz : (0 : Fin 8 → ℝ) ∈ U := by simp [U, rayPairing]
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (hU.mem_nhds hz)
  intro p hp i
  exact (Set.mem_iInter.mp hp i).le

def facetWitnessNumerator : Matrix (Fin 13) (Fin 8) ℤ :=
  ![![-4,0,0,0,0,0,0,0], ![4,0,0,0,0,0,0,0],
    ![0,-4,0,0,0,0,0,0], ![0,4,0,0,0,0,0,0],
    ![0,0,-4,0,0,0,0,0], ![0,0,4,0,0,0,0,0],
    ![0,0,-2,-4,-4,0,0,0], ![0,2,-2,-4,0,0,0,0],
    ![0,-2,2,4,0,0,0,0], ![-2,2,0,0,4,0,-4,0],
    ![2,-1,-1,2,0,4,0,0], ![2,-2,0,0,-4,0,4,0],
    ![2,0,-2,0,-4,0,0,4]]

set_option maxRecDepth 100000 in
theorem facetWitness_certificate :
    ∀ i : Fin 13, (∑ j : Fin 8, rays i j * facetWitnessNumerator i j) = 4 ∧
      ∀ k : Fin 13, k ≠ i →
        (∑ j : Fin 8, rays k j * facetWitnessNumerator i j) ≤ 2 := by decide

def facetWitness (i : Fin 13) : Fin 8 → ℝ :=
  fun j => (facetWitnessNumerator i j : ℝ) / 4

theorem facetWitness_pairing (i k : Fin 13) :
    rayPairing (facetWitness i) k =
      ((∑ j : Fin 8, rays k j * facetWitnessNumerator i j : ℤ) : ℝ) / 4 := by
  simp only [rayPairing, facetWitness, Int.cast_sum, Int.cast_mul, Finset.sum_div,
    mul_div_assoc]

theorem facetWitness_eq (i : Fin 13) : rayPairing (facetWitness i) i = 1 := by
  rw [facetWitness_pairing, (facetWitness_certificate i).1]
  norm_num

theorem facetWitness_lt (i k : Fin 13) (hki : k ≠ i) :
    rayPairing (facetWitness i) k < 1 := by
  rw [facetWitness_pairing]
  have hI := (facetWitness_certificate i).2 k hki
  have hR : ((∑ j : Fin 8, rays k j * facetWitnessNumerator i j : ℤ) : ℝ) ≤ 2 := by
    exact_mod_cast hI
  linarith

theorem facetWitness_mem (i : Fin 13) : facetWitness i ∈ polar := by
  intro k
  by_cases hki : k = i
  · subst k
    exact (facetWitness_eq i).le
  · exact (facetWitness_lt i k hki).le

theorem activeNormals_facetWitness (i : Fin 13) :
    activeNormals (facetWitness i) = {i} := by
  ext k
  simp only [activeNormals, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hk
    by_contra hki
    exact (ne_of_lt (facetWitness_lt i k hki)) hk
  · intro hk
    rw [hk]
    exact facetWitness_eq i

#print axioms isCompact_polar
#print axioms activeNormals_facetWitness
end Unimodular.ExplicitR10


/-! ## Source module: Extremes -/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology

namespace Unimodular.ExplicitR10

theorem rayPairing_add_smul (p v : Fin 8 → ℝ) (t : ℝ) (i : Fin 13) :
    rayPairing (p + t • v) i = rayPairing p i + t * rayPairing v i := by
  simp only [rayPairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A real extreme point cannot move in an annihilator of its active normals. -/
theorem extreme_active_annihilator (p : Fin 8 → ℝ)
    (hp : p ∈ polar.extremePoints ℝ) (v : Fin 8 → ℝ)
    (hv : ∀ i, rayPairing p i = 1 → rayPairing v i = 0) : v = 0 := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i : Fin 13, rayPairing (p + t • v) i ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : rayPairing p i = 1
    · filter_upwards [] with t
      rw [rayPairing_add_smul, hi, hv i hi]
      norm_num
    · have hlt : rayPairing p i < 1 := (lt_or_eq_of_le (hp.1 i)).resolve_right hi
      have hc : Continuous (fun t : ℝ => rayPairing (p + t • v) i) :=
        (continuous_rayPairing i).comp
          (continuous_const.add (continuous_id.smul continuous_const))
      have ho : IsOpen {t : ℝ | rayPairing (p + t • v) i < 1} :=
        isOpen_lt hc continuous_const
      have hz : (0 : ℝ) ∈ {t : ℝ | rayPairing (p + t • v) i < 1} := by
        simpa using hlt
      exact Filter.Eventually.mono (ho.mem_nhds hz) (fun _ ht => ht.le)
  have hn : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg : Continuous (fun t : ℝ => -t)).tendsto (0 : ℝ)
  obtain ⟨t, ht, hplus, hminus⟩ := (hnear.and (hn.eventually hnear)).exists_gt
  have hs : p ∈ openSegment ℝ (p + t • v) (p + (-t) • v) := by
    refine ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq : p + t • v = p := hp.2 hplus hminus hs
  have hzero : t • v = 0 := add_left_cancel (show p + t • v = p + 0 by simpa using heq)
  exact (smul_eq_zero.mp hzero).resolve_left (ne_of_gt ht)

def activeMatrix (p : Fin 8 → ℝ) : Matrix (activeNormals p) (Fin 8) ℝ :=
  fun i j => (rays i.val j : ℝ)

theorem activeMatrix_mulVec_injective (p : Fin 8 → ℝ)
    (hp : p ∈ polar.extremePoints ℝ) : Function.Injective (activeMatrix p).mulVec := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply extreme_active_annihilator p hp
  intro i hi
  have him : i ∈ activeNormals p := by simp [activeNormals, hi]
  have hh : rayPairing x i = rayPairing y i := congrFun hxy ⟨i, him⟩
  simp only [rayPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  change rayPairing x i - rayPairing y i = 0
  exact sub_eq_zero.mpr hh

theorem extreme_activeNormals_card (p : Fin 8 → ℝ)
    (hp : p ∈ polar.extremePoints ℝ) : (activeNormals p).card = 8 := by
  have hd := LinearMap.finrank_le_finrank_of_injective
    (f := (activeMatrix p).mulVecLin) (activeMatrix_mulVec_injective p hp)
  have hl : 8 ≤ (activeNormals p).card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fintype.card_coe] using hd
  exact le_antisymm (activeNormals_card_le_eight p hp.1) hl

/-- Every extreme point is integral and its eight active normals form an integral basis. -/
theorem extreme_smooth_integral (p : Fin 8 → ℝ)
    (hp : p ∈ polar.extremePoints ℝ) :
    ∃ f : Fin 8 → Fin 13, Function.Injective f ∧
      (∀ i, i ∈ activeNormals p ↔ ∃ j, f j = i) ∧
      |(rays.submatrix f id).det| = 1 ∧
      ∃ z : Fin 8 → ℤ, (fun j => (z j : ℝ)) = p := by
  let e := (activeNormals p).orderIsoOfFin (extreme_activeNormals_card p hp)
  let f : Fin 8 → Fin 13 := fun j => (e j).val
  let A : Matrix (Fin 8) (Fin 8) ℤ := rays.submatrix f id
  let B : Matrix (Fin 8) (Fin 8) ℝ := A.map (fun z : ℤ => (z : ℝ))
  have hf : Function.Injective f := by
    intro j k hjk
    exact e.injective (Subtype.ext hjk)
  have hrange : ∀ i, i ∈ activeNormals p ↔ ∃ j, f j = i := by
    intro i
    constructor
    · intro hi
      obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
      exact ⟨j, congrArg Subtype.val hj⟩
    · rintro ⟨j, rfl⟩
      exact (e j).property
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    apply activeMatrix_mulVec_injective p hp
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun hxy j
  have hunitR : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hdetZ : A.det ≠ 0 := by
    intro hzero
    apply hunitR.ne_zero
    change (A.map (fun z : ℤ => (z : ℝ))).det = 0
    rw [← Int.cast_det, hzero]
    norm_num
  have habs : |A.det| = 1 := by
    have hu : |A.det| ≤ 1 := all_ray_determinants f
    have hl : 0 < |A.det| := abs_pos.mpr hdetZ
    omega
  have hunitZ : IsUnit A.det := Int.isUnit_iff_abs_eq.mpr habs
  obtain ⟨z, hz⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr hunitZ)) (fun _ : Fin 8 => (1 : ℤ))
  have hzr : B.mulVec (fun j => (z j : ℝ)) = (fun _ => 1) := by
    ext j
    change (∑ k : Fin 8, (A j k : ℝ) * (z k : ℝ)) = 1
    have hzj : (∑ k : Fin 8, A j k * z k) = 1 := congrFun hz j
    exact_mod_cast hzj
  have hpr : B.mulVec p = (fun _ => 1) := by
    ext j
    change rayPairing p (f j) = 1
    exact (Finset.mem_filter.mp (e j).property).2
  exact ⟨f, hf, hrange, habs, z, hinj (hzr.trans hpr.symm)⟩

theorem extremePoints_finite : (polar.extremePoints ℝ).Finite := by
  classical
  let f : polar.extremePoints ℝ → Finset (Fin 13) := fun p => activeNormals p.val
  have hi : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply extreme_active_annihilator p.val p.property
    intro i hi
    have him : i ∈ activeNormals p.val := by simp [activeNormals, hi]
    have hiq : i ∈ activeNormals q.val := by
      change i ∈ f q
      rw [← hpq]
      exact him
    have hq : rayPairing q.val i = 1 := (Finset.mem_filter.mp hiq).2
    simp only [rayPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    change rayPairing p.val i - rayPairing q.val i = 0
    rw [hi, hq, sub_self]
  exact Set.finite_coe_iff.mp (Finite.of_injective f hi)

theorem polar_eq_convexHull_extremePoints : polar = convexHull ℝ (polar.extremePoints ℝ) := by
  have hclosed := extremePoints_finite.isClosed_convexHull ℝ
  have hh := closure_convexHull_extremePoints isCompact_polar convex_polar
  rw [hclosed.closure_eq] at hh
  exact hh.symm

noncomputable def integralRowBasis (A : Matrix (Fin 8) (Fin 8) ℤ)
    (hA : IsUnit A.det) : Module.Basis (Fin 8) ℤ (Fin 8 → ℤ) :=
  (Pi.basisFun ℤ (Fin 8)).map
    (Matrix.toLinearEquiv (Pi.basisFun ℤ (Fin 8)) A.transpose
      (by simpa only [Matrix.det_transpose] using hA))

theorem integralRowBasis_apply (A : Matrix (Fin 8) (Fin 8) ℤ)
    (hA : IsUnit A.det) (i : Fin 8) : integralRowBasis A hA i = A i := by
  simp only [integralRowBasis, Module.Basis.map_apply, Matrix.toLinearEquiv_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply]
  ext j
  rfl

#print axioms extreme_smooth_integral
#print axioms polar_eq_convexHull_extremePoints
end Unimodular.ExplicitR10


/-! ## Source module: Configuration -/
/-! # The actual lattice and convex hull of the thirteen rays

This file applies the general terminal-reflexive hull theorem to the explicit
configuration.  Positive spanning is proved from the displayed positive relation
and the eight coordinate vectors; it is not supplied as a geometric assumption.
-/

noncomputable section
open scoped BigOperators

namespace Unimodular.ExplicitR10

theorem pairing_ray (p : Ambient 8) (i : Fin 13) :
    pairing p (rays i) = rayPairing p i := by
  simp only [pairing, rayPairing, mul_comm]

theorem polar_eq_polarCarrier : polar = GenericReflexivity.polarCarrier normalSet := by
  ext p
  constructor
  · intro hp u hu
    obtain ⟨i, rfl⟩ := (mem_normalSet u).1 hu
    simpa only [pairing_ray] using hp i
  · intro hp i
    simpa only [pairing_ray] using hp (rays i) ((mem_normalSet _).2 ⟨i, rfl⟩)

theorem rays_uniform :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 8)) rays := by
  intro a
  rw [Pi.basisFun_det_apply]
  exact all_ray_determinants a

theorem normalSet_uniform :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 8))
      (fun u : (normalSet : Set (Lattice 8)) => u.val) := by
  intro a
  choose f hf using fun i => (mem_normalSet (a i).val).1 (a i).property
  have h : (fun u : (normalSet : Set (Lattice 8)) => u.val) ∘ a = rays ∘ f := by
    funext i
    exact (hf i).symm
  rw [h]
  exact rays_uniform f

theorem real_unit_rays (j : Fin 8) :
    embed (rays (unitIndex j)) = (Pi.basisFun ℝ (Fin 8)) j := by
  fin_cases j <;> ext k <;> fin_cases k <;>
    norm_num [embed, rays, unitIndex, Pi.basisFun_apply, Pi.single_apply]

theorem rays_real_span :
    Submodule.span ℝ (Set.range (fun i => embed (rays i))) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin 8)).span_eq]
  apply Submodule.span_mono
  rintro x ⟨j, rfl⟩
  exact ⟨unitIndex j, real_unit_rays j⟩

theorem normalSet_positive_span :
    PointedCone.hull ℝ (embed '' (normalSet : Set (Lattice 8))) = ⊤ := by
  have hset : embed '' (normalSet : Set (Lattice 8)) =
      Set.range (fun i => embed (rays i)) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, rfl⟩ := (mem_normalSet u).1 hu
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨rays i, (mem_normalSet _).2 ⟨i, rfl⟩, rfl⟩
  rw [hset, FlowOrientations.hull_top_iff_span_and_positive_relation]
  refine ⟨rays_real_span, fun i => (positiveWeights i : ℝ), ?_, ?_⟩
  · intro i
    exact Int.cast_pos.mpr (positiveWeights_pos i)
  · ext j
    change (∑ i : Fin 13, (positiveWeights i : ℝ) * (rays i j : ℝ)) = 0
    have h : (∑ i : Fin 13, positiveWeights i * rays i j) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        using congrFun positive_dependence j
    exact_mod_cast h

/-- The polytope in Proposition 5.1, in an explicit integral coordinate system. -/
def polytope : Set (Ambient 8) :=
  convexHull ℝ (embed '' (normalSet : Set (Lattice 8)))

theorem polytope_reflexive_terminal :
    (0 : Ambient 8) ∈ interior polytope ∧
      (∃ W : Finset (Lattice 8), realPolar polytope =
        convexHull ℝ (embed '' (W : Set (Lattice 8)))) ∧
      polytope.extremePoints ℝ = embed '' (normalSet : Set (Lattice 8)) ∧
      (∀ x : Lattice 8, embed x ∈ polytope ↔ x = 0 ∨ x ∈ normalSet) :=
  GenericReflexivity.terminal_reflexive_hull (by decide) normalSet
    normalSet_uniform normalSet_positive_span zero_not_mem_normalSet

theorem realPolar_polytope : realPolar polytope = polar := by
  rw [polytope, GenericReflexivity.realPolar_hull_eq_polarCarrier,
    ← polar_eq_polarCarrier]

#print axioms polytope_reflexive_terminal
end Unimodular.ExplicitR10


/-! ## Source module: Presentation -/
/-! # A smooth reflexive presentation of the polar

The vertex set below is defined by the actual real extreme points.  Finiteness,
integrality, and the complete active-normal basis at each such point are theorems
proved in `Extremes`; no precomputed list is assumed to be exhaustive.
-/

noncomputable section
open scoped BigOperators

namespace Unimodular.ExplicitR10

def vertexSet : Finset (Lattice 8) :=
  (Set.Finite.preimage (f := embed) LatticeHull.embed_injective.injOn
    extremePoints_finite).toFinset

@[simp] theorem mem_vertexSet (z : Lattice 8) :
    z ∈ vertexSet ↔ embed z ∈ polar.extremePoints ℝ := by
  simp [vertexSet]

theorem vertexSet_image :
    embed '' (vertexSet : Set (Lattice 8)) = polar.extremePoints ℝ := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_vertexSet z).1 hz
  · intro hp
    obtain ⟨f, hf, hrange, hdet, z, hz⟩ := extreme_smooth_integral p hp
    have hz' : embed z = p := hz
    exact ⟨z, (mem_vertexSet z).2 (hz'.symm ▸ hp), hz'⟩

theorem polar_eq_convexHull_vertexSet :
    polar = convexHull ℝ (embed '' (vertexSet : Set (Lattice 8))) := by
  rw [vertexSet_image]
  exact polar_eq_convexHull_extremePoints

theorem vertexSet_nonempty : vertexSet.Nonempty := by
  apply GenericReflexivity.polar_hull_nonempty normalSet
  rw [← polar_eq_polarCarrier]
  exact polar_eq_convexHull_vertexSet

theorem vertex_basis_exists (v : {z // z ∈ vertexSet}) :
    ∃ b : Module.Basis (Fin 8) ℤ (Lattice 8),
      (∀ i, b i ∈ normalSet ∧ pairing (embed v.val) (b i) = 1) ∧
      (∀ u ∈ normalSet, pairing (embed v.val) u = 1 → ∃ i, b i = u) := by
  obtain ⟨f, hf, hrange, hdet, z, hz⟩ :=
    extreme_smooth_integral (embed v.val) ((mem_vertexSet v.val).1 v.property)
  let A : Matrix (Fin 8) (Fin 8) ℤ := rays.submatrix f id
  let b := integralRowBasis A (Int.isUnit_iff_abs_eq.mpr hdet)
  have hb (i : Fin 8) : b i = rays (f i) := integralRowBasis_apply A _ i
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hb]
    refine ⟨(mem_normalSet _).2 ⟨f i, rfl⟩, ?_⟩
    rw [pairing_ray]
    exact (Finset.mem_filter.mp ((hrange (f i)).2 ⟨i, rfl⟩)).2
  · intro u hu hactive
    obtain ⟨k, rfl⟩ := (mem_normalSet u).1 hu
    have hk : k ∈ activeNormals (embed v.val) := by
      simp only [activeNormals, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [pairing_ray] using hactive
    obtain ⟨i, hi⟩ := (hrange k).1 hk
    exact ⟨i, (hb i).trans (congrArg rays hi)⟩

def vertexBasis (v : {z // z ∈ vertexSet}) : Module.Basis (Fin 8) ℤ (Lattice 8) :=
  (vertex_basis_exists v).choose

theorem vertexBasis_mem (v : {z // z ∈ vertexSet}) (i : Fin 8) :
    vertexBasis v i ∈ normalSet := ((vertex_basis_exists v).choose_spec.1 i).1

theorem vertexBasis_active (v : {z // z ∈ vertexSet}) (i : Fin 8) :
    pairing (embed v.val) (vertexBasis v i) = 1 :=
  ((vertex_basis_exists v).choose_spec.1 i).2

theorem vertexBasis_exhausts (v : {z // z ∈ vertexSet}) (u : Lattice 8)
    (hu : u ∈ normalSet) (hactive : pairing (embed v.val) u = 1) :
    ∃ i, vertexBasis v i = u := (vertex_basis_exists v).choose_spec.2 u hu hactive

/-- Every one of the thirteen inequalities is active at an actual vertex. -/
theorem exists_vertex_active (i : Fin 13) :
    ∃ v ∈ vertexSet, pairing (embed v) (rays i) = 1 := by
  by_contra h
  push_neg at h
  have hstrict : ∀ v ∈ vertexSet, pairing (embed v) (rays i) < 1 := by
    intro v hv
    have hle : rayPairing (embed v) i ≤ 1 := ((mem_vertexSet v).1 hv).1 i
    rw [← pairing_ray] at hle
    exact (lt_or_eq_of_le hle).resolve_right (h v hv)
  have hc : Convex ℝ {p : Ambient 8 | pairing p (rays i) < 1} :=
    (convex_Iio (𝕜 := ℝ) (1 : ℝ)).linear_preimage
      (GenericReflexivity.polarFunctional (rays i))
  have hs : polar ⊆ {p : Ambient 8 | pairing p (rays i) < 1} := by
    rw [polar_eq_convexHull_vertexSet]
    exact convexHull_min (by rintro p ⟨v, hv, rfl⟩; exact hstrict v hv) hc
  have hbad := hs (facetWitness_mem i)
  change pairing (facetWitness i) (rays i) < 1 at hbad
  rw [pairing_ray, facetWitness_eq] at hbad
  exact (lt_irrefl (1 : ℝ)) hbad

/-- A complete smooth reflexive presentation, with no assumed normal fan. -/
def smoothPresentation : SmoothReflexivePresentation 8 where
  vertices := vertexSet
  normals := normalSet
  vertices_nonempty := vertexSet_nonempty
  basis := vertexBasis
  basis_mem := vertexBasis_mem
  basis_active := vertexBasis_active
  active_subset := vertexBasis_exhausts
  normals_occur := by
    intro u hu
    obtain ⟨i, rfl⟩ := (mem_normalSet u).1 hu
    obtain ⟨v, hv, hactive⟩ := exists_vertex_active i
    obtain ⟨j, hj⟩ := vertexBasis_exhausts ⟨v, hv⟩ (rays i)
      ((mem_normalSet _).2 ⟨i, rfl⟩) hactive
    exact ⟨⟨v, hv⟩, j, hj⟩
  hull_eq := by
    rw [← polar_eq_convexHull_vertexSet, polar_eq_polarCarrier]
    rfl

theorem smoothPresentation_normals : smoothPresentation.normals = normalSet := rfl

theorem smoothPresentation_carrier : smoothPresentation.carrier = polar :=
  polar_eq_convexHull_vertexSet.symm

#print axioms smoothPresentation
end Unimodular.ExplicitR10


/-! ## Source module: SmoothFano -/
/-! # The smooth Fano polytope in Proposition 5.1

Facets are defined as maximal nonempty proper convex extreme faces of the actual
real convex hull.  Every such face is proved to have exactly an integral basis as
its vertices.  Thus the smoothness assertion concerns all geometric facets, not
merely a selected list of candidate supporting hyperplanes.
-/

noncomputable section

namespace Unimodular.ExplicitR10

/-- The usual maximal-proper-face definition of a facet of a polytope. -/
structure IsFacet {n : ℕ} (P F : Set (Ambient n)) : Prop where
  convex : Convex ℝ F
  extreme : IsExtreme ℝ P F
  nonempty : F.Nonempty
  ne_whole : F ≠ P
  maximal : ∀ G : Set (Ambient n), Convex ℝ G → IsExtreme ℝ P G →
    F ⊆ G → G ≠ P → F = G

theorem lattice_pairing_comm (u v : Lattice 8) :
    pairing (embed u) v = pairing (embed v) u := by
  simp only [pairing, embed, mul_comm]

theorem facet_has_integral_basis (F : Set (Ambient 8)) (hF : IsFacet polytope F) :
    ∃ b : Module.Basis (Fin 8) ℤ (Lattice 8),
      F.extremePoints ℝ = Set.range (fun i => embed (b i)) ∧
      F = convexHull ℝ (Set.range (fun i => embed (b i))) := by
  have hW : GenericReflexivity.polarCarrier normalSet =
      convexHull ℝ (embed '' (vertexSet : Set (Lattice 8))) := by
    rw [← polar_eq_polarCarrier]
    exact polar_eq_convexHull_vertexSet
  have hz : (0 : Ambient 8) ∈ GenericReflexivity.rayHull normalSet :=
    interior_subset polytope_reflexive_terminal.1
  obtain ⟨q, hq, hsub⟩ := GenericReflexivity.proper_face_subset_polarFace
    normalSet vertexSet hW hz hF.convex hF.extreme hF.nonempty hF.ne_whole
  have hqpolar : embed q ∈ GenericReflexivity.polarCarrier normalSet := by
    rw [← polar_eq_polarCarrier]
    exact ((mem_vertexSet q).1 hq).1
  have hproper : GenericReflexivity.polarFace normalSet q ≠ polytope := by
    intro heq
    have hzero : (0 : Ambient 8) ∈ GenericReflexivity.polarFace normalSet q := by
      rw [heq]
      exact hz
    have hh := hzero.2
    norm_num [pairing] at hh
  have hFeq : F = GenericReflexivity.polarFace normalSet q :=
    hF.maximal _ (GenericReflexivity.polarFace_convex normalSet q)
      (GenericReflexivity.polarFace_extreme normalSet q hqpolar) hsub hproper
  let v : {z // z ∈ vertexSet} := ⟨q, hq⟩
  let b : Module.Basis (Fin 8) ℤ (Lattice 8) := vertexBasis v
  have hgens : embed '' (GenericReflexivity.faceGenerators normalSet q :
      Set (Lattice 8)) = Set.range (fun i => embed (b i)) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hum, hactive⟩ := (GenericReflexivity.mem_faceGenerators _ _ _).1 hu
      rw [lattice_pairing_comm] at hactive
      obtain ⟨i, hi⟩ := vertexBasis_exhausts v u hum hactive
      exact ⟨i, congrArg embed hi⟩
    · rintro ⟨i, rfl⟩
      refine ⟨b i, (GenericReflexivity.mem_faceGenerators _ _ _).2
        ⟨vertexBasis_mem v i, ?_⟩, rfl⟩
      rw [lattice_pairing_comm]
      exact vertexBasis_active v i
  refine ⟨b, ?_, ?_⟩
  · rw [hF.extreme.extremePoints_eq, polytope_reflexive_terminal.2.2.1, hFeq]
    rw [← hgens]
    ext x
    constructor
    · rintro ⟨hxf, u, hu, rfl⟩
      exact ⟨u, (GenericReflexivity.mem_faceGenerators _ _ _).2 ⟨hu, hxf.2⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hum, hactive⟩ := (GenericReflexivity.mem_faceGenerators _ _ _).1 hu
      exact ⟨⟨subset_convexHull ℝ _ ⟨u, hum, rfl⟩, hactive⟩, u, hum, rfl⟩
  · rw [hFeq, GenericReflexivity.polarFace_eq_convexHull normalSet q hqpolar, hgens]

theorem polytope_has_thirteen_vertices : (polytope.extremePoints ℝ).ncard = 13 := by
  rw [polytope_reflexive_terminal.2.2.1,
    Set.ncard_image_of_injective _ LatticeHull.embed_injective, Set.ncard_coe_finset]
  exact normalSet_card

theorem polytope_full_dimensional : affineSpan ℝ polytope = ⊤ :=
  (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.1
    ⟨0, polytope_reflexive_terminal.1⟩

/-- All geometric assertions of Proposition 5.1 for the displayed eight-dimensional
configuration.  The actual `R₁₀` matroid minor is constructed in `MatroidMinor`. -/
theorem proposition_5_1_geometry :
    normalSet.card = 13 ∧
      affineSpan ℝ polytope = ⊤ ∧
      (0 : Ambient 8) ∈ interior polytope ∧
      polytope.extremePoints ℝ = embed '' (normalSet : Set (Lattice 8)) ∧
      IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 8))
        (fun u : (normalSet : Set (Lattice 8)) => u.val) ∧
      (∀ F, IsFacet polytope F → ∃ b : Module.Basis (Fin 8) ℤ (Lattice 8),
        F.extremePoints ℝ = Set.range (fun i => embed (b i))) := by
  refine ⟨normalSet_card, polytope_full_dimensional, polytope_reflexive_terminal.1,
    polytope_reflexive_terminal.2.2.1, normalSet_uniform, ?_⟩
  intro F hF
  obtain ⟨b, hb, _⟩ := facet_has_integral_basis F hF
  exact ⟨b, hb⟩

#print axioms proposition_5_1_geometry
end Unimodular.ExplicitR10


/-! ## Source module: MatroidMinor -/
/-! # The actual R₁₀ matroid minor

Contract the coordinate rays numbered 1, 3, and 5 (zero-based numbering).
The quotient map is the signed coordinate projection
`p ↦ (-p 3, p 4, p 6, p 5, p 7)`.  Its kernel is proved to be exactly the
span of the contracted rays.  After a displayed relabeling and three harmless
column reorientations, all ten quotient columns are the standard R₁₀ columns.
The endpoint uses Mathlib's ordinary matroid contraction/deletion minor relation.
-/

noncomputable section
open scoped BigOperators Matroid

namespace Unimodular.ExplicitR10

def embeddedRays (i : Fin 13) : Ambient 8 := embed (rays i)

def contractedLabels : Set (Fin 13) := {1, 3, 5}

def quotientMap : Ambient 8 →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun p := ![-p 3, p 4, p 6, p 5, p 7]
  map_add' p q := by ext j; fin_cases j <;> simp [add_comm]
  map_smul' t p := by ext j; fin_cases j <;> simp

theorem quotientMap_kernel :
    LinearMap.ker quotientMap = Submodule.span ℝ (embeddedRays '' contractedLabels) := by
  apply le_antisymm
  · intro p hp
    have h := LinearMap.mem_ker.mp hp
    have h3 := congrFun h (0 : Fin 5)
    have h4 := congrFun h (1 : Fin 5)
    have h6 := congrFun h (2 : Fin 5)
    have h5 := congrFun h (3 : Fin 5)
    have h7 := congrFun h (4 : Fin 5)
    change -p 3 = 0 at h3
    change p 4 = 0 at h4
    change p 6 = 0 at h6
    change p 5 = 0 at h5
    change p 7 = 0 at h7
    have hrep : p = p 0 • embeddedRays 1 + p 1 • embeddedRays 3 +
        p 2 • embeddedRays 5 := by
      ext j
      fin_cases j <;> simp [embeddedRays, embed, rays, h4, h5, h6, h7] <;> linarith
    rw [hrep]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨1, by simp [contractedLabels], rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨3, by simp [contractedLabels], rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨5, by simp [contractedLabels], rfl⟩)
  · apply Submodule.span_le.2
    rintro x ⟨i, hi, rfl⟩
    simp only [contractedLabels, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl <;>
      apply LinearMap.mem_ker.mpr <;> ext j <;> fin_cases j <;>
      norm_num [quotientMap, embeddedRays, embed, rays]

def minorLabels : Fin 10 → Fin 13 := ![8,9,11,10,12,2,6,0,4,7]

theorem minorLabels_injective : Function.Injective minorLabels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [minorLabels] at *

def minorEmbedding : Fin 10 ↪ Fin 13 := ⟨minorLabels, minorLabels_injective⟩

theorem minorEmbedding_outside :
    Set.range minorEmbedding ⊆ Set.univ \ contractedLabels := by
  rintro j ⟨i, rfl⟩
  refine ⟨Set.mem_univ _, ?_⟩
  fin_cases i <;> norm_num [minorEmbedding, minorLabels, contractedLabels]

def orientation : Fin 10 → ℝˣ := ![-1,1,1,1,1,1,-1,1,-1,1]

def signedCanonical (i : Fin 10) : Fin 5 → ℝ :=
  orientation i • R10Maximality.realRays i

theorem quotientMap_images (i : Fin 10) :
    quotientMap (embeddedRays (minorEmbedding i)) = signedCanonical i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [quotientMap, embeddedRays, embed, rays, minorEmbedding, minorLabels,
      signedCanonical, orientation, Units.smul_def,
      R10Maximality.realRays, R10Maximality.rays]

theorem signedCanonical_matroid :
    VectorMatroid.ofFamily (K := ℝ) signedCanonical = R10Maximality.r10Matroid := by
  apply (VectorMatroid.ofFamily_eq_iff (K := ℝ) signedCanonical R10Maximality.realRays).2
  intro I
  change LinearIndependent ℝ (fun i : I => orientation i.val •
      R10Maximality.realRays i.val) ↔
    LinearIndependent ℝ (fun i : I => R10Maximality.realRays i.val)
  exact LinearIndependent.units_smul_iff (fun i : I => R10Maximality.realRays i.val)
    (fun i : I => orientation i.val)

/-- First, the minor statement with the explicit thirteen labels. -/
theorem r10_minor_labelled :
    R10Maximality.r10Matroid.mapEmbedding minorEmbedding ≤m
      VectorMatroid.ofFamily (K := ℝ) embeddedRays := by
  have h := VectorMatroid.mapEmbedding_isMinor_of_kernel_image
    embeddedRays signedCanonical (E := Set.univ) (C := contractedLabels)
    (Set.subset_univ _) minorEmbedding minorEmbedding_outside quotientMap
    quotientMap_kernel quotientMap_images
  rw [signedCanonical_matroid] at h
  exact h

/-- The labels are actual distinct vertices, not a family with extra repetitions. -/
def rayLabel : Fin 13 ↪ (normalSet : Set (Lattice 8)) where
  toFun i := ⟨rays i, (mem_normalSet _).2 ⟨i, rfl⟩⟩
  inj' := fun i j hij => rays_injective (congrArg Subtype.val hij)

theorem rayLabel_surjective : Function.Surjective rayLabel := by
  intro u
  obtain ⟨i, hi⟩ := (mem_normalSet u.val).1 u.property
  exact ⟨i, Subtype.ext hi⟩

def canonicalVertexEmbedding : Fin 10 ↪ (normalSet : Set (Lattice 8)) :=
  minorEmbedding.trans rayLabel

def vertexFamily (u : (normalSet : Set (Lattice 8))) : Ambient 8 := embed u.val

def vertexMatroid : Matroid (normalSet : Set (Lattice 8)) :=
  VectorMatroid.ofFamily (K := ℝ) vertexFamily

/-- Proposition 5.1's minor assertion for the matroid on the actual vertex set. -/
theorem r10_minor_vertices :
    R10Maximality.r10Matroid.mapEmbedding canonicalVertexEmbedding ≤m vertexMatroid := by
  let C : Set (normalSet : Set (Lattice 8)) := rayLabel '' contractedLabels
  have hR : Set.range canonicalVertexEmbedding ⊆ Set.univ \ C := by
    rintro u ⟨i, rfl⟩
    refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨j, hj, hji⟩
    have heq : j = minorEmbedding i := rayLabel.injective hji
    exact (minorEmbedding_outside ⟨i, rfl⟩).2 (heq ▸ hj)
  have hker : LinearMap.ker quotientMap = Submodule.span ℝ (vertexFamily '' C) := by
    have hset : vertexFamily '' C = embeddedRays '' contractedLabels := by
      dsimp only [C]
      rw [Set.image_image]
      rfl
    rw [hset]
    exact quotientMap_kernel
  have himage : ∀ i, quotientMap (vertexFamily (canonicalVertexEmbedding i)) =
      signedCanonical i := quotientMap_images
  have h := VectorMatroid.mapEmbedding_isMinor_of_kernel_image
    vertexFamily signedCanonical (E := Set.univ) (C := C)
    (Set.subset_univ _) canonicalVertexEmbedding hR quotientMap hker himage
  rw [signedCanonical_matroid] at h
  exact h

#print axioms r10_minor_vertices
end Unimodular.ExplicitR10
