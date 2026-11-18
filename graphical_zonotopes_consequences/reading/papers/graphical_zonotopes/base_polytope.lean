module

public import Papers.GraphicalZonotopes.SetFunction
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

def orderedSequence {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x (e ⟨j, h⟩) else 0

theorem sum_orderPrefix {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) (hj : j ≤ n) :
    subsetSum x (orderPrefix e j) = ∑ i ∈ range j, orderedSequence e x i := by
  classical
  apply sum_bij (fun v _ => (e.symm v).val)
  · intro v hv
    exact mem_range.mpr (mem_filter.mp hv).2
  · intro v hv w hw he
    exact e.symm.injective (Fin.ext he)
  · intro i hi
    have hin : i < n := (mem_range.mp hi).trans_le hj
    refine ⟨e ⟨i, hin⟩, ?_, ?_⟩
    · simp [orderPrefix, mem_range.mp hi]
    · simp
  · intro v hv
    simp [orderedSequence, (e.symm v).isLt]

theorem sum_ordered_product {n : ℕ} (e : Fin n ≃ V) (x w : V → ℝ) :
    (∑ i ∈ range n, orderedSequence e x i * orderedSequence e w i) =
      ∑ v, x v * w v := by
  have he : ∀ i, orderedSequence e x i * orderedSequence e w i =
      orderedSequence e (fun v => x v * w v) i := by
    intro i
    by_cases hi : i < n <;> simp [orderedSequence, hi]
  simp_rw [he]
  rw [← sum_orderPrefix e _ n le_rfl, orderPrefix_full]
  rfl

theorem weighted_le_of_prefix {n : ℕ} (e : Fin n ≃ V) (x y w : V → ℝ)
    (hw : Antitone (fun i => w (e i)))
    (hp : ∀ j ≤ n, subsetSum x (orderPrefix e j) ≤ subsetSum y (orderPrefix e j))
    (ht : subsetSum x univ = subsetSum y univ) :
    (∑ v, x v * w v) ≤ ∑ v, y v * w v := by
  let f : ℕ → ℝ := fun i => orderedSequence e y i - orderedSequence e x i
  let g : ℕ → ℝ := orderedSequence e w
  have hsum : ∀ j ≤ n, 0 ≤ ∑ i ∈ range j, f i := by
    intro j hj
    have h := hp j hj
    rw [sum_orderPrefix e x j hj, sum_orderPrefix e y j hj] at h
    simpa only [f, sum_sub_distrib, sub_nonneg] using h
  have htotal : ∑ i ∈ range n, f i = 0 := by
    rw [show f = (fun i => orderedSequence e y i - orderedSequence e x i) from rfl,
      sum_sub_distrib, ← sum_orderPrefix e y n le_rfl,
      ← sum_orderPrefix e x n le_rfl, orderPrefix_full, ht, sub_self]
  have hnonneg : 0 ≤ ∑ i ∈ range n, f i * g i := by
    simp_rw [← smul_eq_mul]
    rw [sum_range_by_parts', smul_eq_mul, htotal, zero_mul, zero_sub]
    apply neg_nonneg.mpr
    apply sum_nonpos
    intro i hi
    have hin : i < n - 1 := mem_range.mp hi
    have h1 := hsum (i + 1) (by omega)
    have h2 : g (i + 1) - g i ≤ 0 := by
      have hi0 : i < n := by omega
      have hi1 : i + 1 < n := by omega
      have hw' := hw (show (⟨i, hi0⟩ : Fin n) ≤ ⟨i+1, hi1⟩ by
        change i ≤ i + 1
        omega)
      simpa [g, orderedSequence, hi0, hi1, sub_nonpos] using hw'
    simpa only [smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos h1 h2
  simp only [f, g, sub_mul, sum_sub_distrib, sub_nonneg] at hnonneg
  rwa [sum_ordered_product, sum_ordered_product] at hnonneg

theorem exists_antitone_enumeration (w : V → ℝ) :
    ∃ e : Fin (Fintype.card V) ≃ V, Antitone (fun i => w (e i)) := by
  let f : Fin (Fintype.card V) → OrderDual ℝ := fun i => w ((Fintype.equivFin V).symm i)
  let e := (Tuple.sort f).trans (Fintype.equivFin V).symm
  exact ⟨e, Tuple.monotone_sort f⟩

theorem linearFunctional_eq_weighted_sum (f : (V → ℝ) →L[ℝ] ℝ) (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  classical
  have he : x = ∑ v, x v • Pi.single v (1 : ℝ) := by
    funext v
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp


theorem greedyPoint_minimizes {z : SetFunction V} (hz : Normalized z)
    (w : V → ℝ) : ∃ e : Fin (Fintype.card V) ≃ V,
    ∀ x ∈ basePolytope z,
      (∑ v, greedyPoint z e v * w v) ≤ ∑ v, x v * w v := by
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  refine ⟨e, ?_⟩
  intro x hx
  apply weighted_le_of_prefix e (greedyPoint z e) x w he
  · intro j hj
    rw [greedyPoint_prefix z hz e j hj]
    exact hx.2 _
  · have h := greedyPoint_prefix z hz e (Fintype.card V) le_rfl
    simpa [hx.1] using h

def greedyPoints (z : SetFunction V) : Set (V → ℝ) :=
  Set.range (fun e : Fin (Fintype.card V) ≃ V => greedyPoint z e)

theorem greedyPoints_finite (z : SetFunction V) : (greedyPoints z).Finite :=
  Set.finite_range _

theorem basePolytope_eq_convexHull {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : basePolytope z = convexHull ℝ (greedyPoints z) := by
  symm
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ (basePolytope_convex z)
    rintro x ⟨e, rfl⟩
    exact greedyPoint_mem_basePolytope hz hs e
  · intro x hx
    by_contra hout
    obtain ⟨f, c, hxc, hcf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _) ((greedyPoints_finite z).isClosed_convexHull ℝ) hout
    obtain ⟨e, he⟩ := greedyPoint_minimizes hz (fun v => f (Pi.single v 1))
    have hm := he x hx
    rw [← linearFunctional_eq_weighted_sum, ← linearFunctional_eq_weighted_sum] at hm
    have hc := hcf (greedyPoint z e) (subset_convexHull ℝ _ ⟨e, rfl⟩)
    linarith

theorem basePolytope_compact {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) : IsCompact (basePolytope z) := by
  rw [basePolytope_eq_convexHull hz hs]
  exact (greedyPoints_finite z).isCompact_convexHull ℝ

@[simp] theorem greedyPoint_add {n : ℕ} (z w : SetFunction V) (e : Fin n ≃ V) :
    greedyPoint (z + w) e = greedyPoint z e + greedyPoint w e := by
  funext v
  simp only [greedyPoint, Pi.add_apply]
  ring

@[simp] theorem greedyPoint_smul {n : ℕ} (a : ℝ) (z : SetFunction V) (e : Fin n ≃ V) :
    greedyPoint (a • z) e = a • greedyPoint z e := by
  funext v
  simp only [greedyPoint, Pi.smul_apply, smul_eq_mul]
  ring

theorem Supermodular.add {z w : SetFunction V} (hz : Supermodular z)
    (hw : Supermodular w) : Supermodular (z + w) := by
  intro A B
  have h1 := hz A B
  have h2 := hw A B
  simp only [Pi.add_apply]
  linarith

theorem Supermodular.smul {z : SetFunction V} (hz : Supermodular z)
    {a : ℝ} (ha : 0 ≤ a) : Supermodular (a • z) := by
  intro A B
  simpa [mul_add] using mul_le_mul_of_nonneg_left (hz A B) ha

theorem basePolytope_add {z w : SetFunction V} (hz : Normalized z)
    (hw : Normalized w) (hsz : Supermodular z) (hsw : Supermodular w) :
    basePolytope (z + w) = basePolytope z + basePolytope w := by
  apply Set.Subset.antisymm
  · rw [basePolytope_eq_convexHull (show Normalized (z + w) by
      change z ∅ + w ∅ = 0; rw [hz, hw, add_zero])
      (hsz.add hsw)]
    apply convexHull_min ?_ ((basePolytope_convex z).add (basePolytope_convex w))
    rintro x ⟨e, rfl⟩
    dsimp only
    rw [greedyPoint_add]
    exact Set.add_mem_add (greedyPoint_mem_basePolytope hz hsz e)
      (greedyPoint_mem_basePolytope hw hsw e)
  · rintro x ⟨a, ha, b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [subsetSum_add, ha.1, hb.1]; rfl
    · intro S
      rw [subsetSum_add]
      exact add_le_add (ha.2 S) (hb.2 S)

theorem basePolytope_smul {z : SetFunction V} (hz : Normalized z)
    (hs : Supermodular z) {a : ℝ} (ha : 0 ≤ a) :
    basePolytope (a • z) = a • basePolytope z := by
  rw [basePolytope_eq_convexHull (show Normalized (a • z) by
    change a * z ∅ = 0; rw [hz, mul_zero])
    (hs.smul ha), basePolytope_eq_convexHull hz hs]
  rw [← convexHull_smul]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨greedyPoint z e, ⟨e, rfl⟩, (greedyPoint_smul a z e).symm⟩
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩
    exact ⟨e, greedyPoint_smul a z e⟩

end GraphicalZonotopes
