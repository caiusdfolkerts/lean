import Characterizations.GreedyChain
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-! # The exact real convex hull forced by local equigeneration -/

noncomputable section
namespace Characterizations
open CommAlg.Polymatroid Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def realExponent (a : Exponent V) : V → ℝ := fun i => a i

def realSubsetSum (x : V → ℝ) (U : Finset V) : ℝ := ∑ i ∈ U, x i

@[simp] theorem realSubsetSum_exponent (a : Exponent V) (U : Finset V) :
    realSubsetSum (realExponent a) U = (subsetSum a U : ℝ) := by
  simp [realSubsetSum, realExponent, subsetSum]

def lowerRankPolytope (B : Family V) (d : ℕ) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ realSubsetSum x univ = d ∧
    ∀ U, (lowerRank B U : ℝ) ≤ realSubsetSum x U}

theorem lowerRankPolytope_convex (B : Family V) (d : ℕ) :
    Convex ℝ (lowerRankPolytope B d) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) = (d : ℝ)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    change a * realSubsetSum x univ + b * realSubsetSum y univ = _
    rw [hx.2.1, hy.2.1, ← add_mul, hab, one_mul]
  · intro U
    change (lowerRank B U : ℝ) ≤ ∑ i ∈ U, (a * x i + b * y i)
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx.2.2 U) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2.2 U) hb
    have he : a * (lowerRank B U : ℝ) + b * (lowerRank B U : ℝ) = lowerRank B U := by
      rw [← add_mul, hab, one_mul]
    exact he ▸ add_le_add h1 h2

theorem exponent_mem_lowerRankPolytope {B : Family V} {d : ℕ}
    (hd : Equigenerated B d) {a : Exponent V} (ha : a ∈ B) :
    realExponent a ∈ lowerRankPolytope B d := by
  refine ⟨fun i => Nat.cast_nonneg _, ?_, ?_⟩
  · rw [realSubsetSum_exponent, subsetSum_univ, hd a ha]
  · intro U
    rw [realSubsetSum_exponent]
    exact_mod_cast lowerRank_le ha U

def orderPrefix {n : ℕ} (e : Fin n ≃ V) (j : ℕ) : Finset V :=
  univ.filter (fun v => (e.symm v).val < j)

theorem orderPrefix_mono {n : ℕ} (e : Fin n ≃ V) : Monotone (orderPrefix e) := by
  intro j k hjk v hv
  exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (mem_filter.mp hv).2 hjk⟩

@[simp] theorem orderPrefix_full {n : ℕ} (e : Fin n ≃ V) : orderPrefix e n = univ := by
  ext v
  simp [orderPrefix, (e.symm v).isLt]

def orderedSequence {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x (e ⟨j, h⟩) else 0

theorem sum_orderPrefix {n : ℕ} (e : Fin n ≃ V) (x : V → ℝ) (j : ℕ) (hj : j ≤ n) :
    realSubsetSum x (orderPrefix e j) = ∑ i ∈ range j, orderedSequence e x i := by
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
    (hp : ∀ j ≤ n, realSubsetSum x (orderPrefix e j) ≤ realSubsetSum y (orderPrefix e j))
    (ht : realSubsetSum x univ = realSubsetSum y univ) :
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

theorem generator_minimizes_every_functional {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d)
    (w : V → ℝ) :
    ∃ b ∈ B, ∀ x ∈ lowerRankPolytope B d,
      (∑ v, realExponent b v * w v) ≤ ∑ v, x v * w v := by
  obtain ⟨e, he⟩ := exists_antitone_enumeration w
  obtain ⟨b, hb, hmin⟩ := generator_chain_minimum hB hanti hl
    (orderPrefix e) (orderPrefix_mono e) (Fintype.card V) (orderPrefix_full e)
  refine ⟨b, hb, ?_⟩
  intro x hx
  apply weighted_le_of_prefix e (realExponent b) x w he
  · intro j hj
    rw [realSubsetSum_exponent, hmin j hj]
    exact hx.2.2 _
  · rw [realSubsetSum_exponent, subsetSum_univ, hd b hb, hx.2.1]

theorem linearFunctional_eq_weighted_sum (f : (V → ℝ) →L[ℝ] ℝ) (x : V → ℝ) :
    f x = ∑ v, x v * f (Pi.single v 1) := by
  classical
  have he : x = ∑ v, x v • Pi.single v (1 : ℝ) := by
    funext v
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp

/-- Equation (2.3) of Theorem 2.11: equality of actual real convex sets. -/
theorem convexHull_generators_eq_lowerRankPolytope {B : Family V} (hB : B.Nonempty)
    (hanti : Antichain B) (hl : LocallyEquigenerated B) {d : ℕ} (hd : Equigenerated B d) :
    convexHull ℝ (realExponent '' (B : Set (Exponent V))) = lowerRankPolytope B d := by
  apply Set.Subset.antisymm
  · apply convexHull_min ?_ (lowerRankPolytope_convex B d)
    rintro x ⟨a, ha, rfl⟩
    exact exponent_mem_lowerRankPolytope hd ha
  · intro x hx
    by_contra hout
    have hfin : (realExponent '' (B : Set (Exponent V))).Finite := B.finite_toSet.image _
    obtain ⟨f, c, hxc, hcf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _) (hfin.isClosed_convexHull ℝ) hout
    obtain ⟨b, hb, hmin⟩ := generator_minimizes_every_functional hB hanti hl hd
      (fun v => f (Pi.single v 1))
    have hm := hmin x hx
    rw [← linearFunctional_eq_weighted_sum, ← linearFunctional_eq_weighted_sum] at hm
    have hc := hcf (realExponent b) (subset_convexHull ℝ _ ⟨b, hb, rfl⟩)
    linarith

end Characterizations
