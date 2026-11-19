module
public import rational_polyhedra
public import Mathlib.Data.Rat.Lemmas

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Natural exponent certificates for an integral polytope

A real convex combination of integer vertices lying below an integer point
has a rational such combination.  Clearing a common denominator yields the
literal natural-number multiplicities used in the power-root argument for
integral dependence of determinantal products.
-/

noncomputable section
namespace FourPapers.Symmetric.RationalPolyhedra
open scoped BigOperators Pointwise

/-- The feasible-solution theorem with an arbitrary finite variable alphabet. -/
theorem rational_solution_finite {ι ν : Type*} [Fintype ι] [Fintype ν]
    (A : ι → ν → ℚ) (b : ι → ℚ)
    (h : ∃ x : ν → ℝ, ∀ i, ∑ j, (A i j : ℝ) * x j ≤ b i) :
    ∃ x : ν → ℚ, ∀ i, ∑ j, A i j * x j ≤ b i := by
  classical
  let e := Fintype.equivFin ν
  obtain ⟨x, hx⟩ := h
  have h' : ∃ y : Fin (Fintype.card ν) → ℝ,
      ∀ i, ∑ j, (A i (e.symm j) : ℝ) * y j ≤ b i := by
    refine ⟨fun j => x (e.symm j), ?_⟩
    intro i
    rw [Equiv.sum_comp e.symm (fun j => (A i j : ℝ) * x j)]
    exact hx i
  obtain ⟨y, hy⟩ := rational_solution (fun i j => A i (e.symm j)) b h'
  refine ⟨fun j => y (e j), ?_⟩
  intro i
  have hh := hy i
  simpa only [← Equiv.sum_comp e, Equiv.symm_apply_apply] using hh

/-- The upward closed Minkowski sum of a convex hull with the positive orthant. -/
def upperHull {ι ν : Type*} (v : ι → ν → ℝ) : Set (ν → ℝ) :=
  {x | ∃ y ∈ convexHull ℝ (Set.range v), y ≤ x}

theorem upperHull_eq_minkowski {ι ν : Type*} (v : ι → ν → ℝ) :
    upperHull v = convexHull ℝ (Set.range v) + {z : ν → ℝ | 0 ≤ z} := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine Set.mem_add.mpr ⟨y, hy, x - y, ?_, ?_⟩
    · exact sub_nonneg.mpr hxy
    · abel
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
    exact ⟨y, hy, le_add_of_nonneg_right hz⟩

theorem mem_upperHull_iff_combination {ι ν : Type*} [Fintype ι]
    (v : ι → ν → ℝ) (x : ν → ℝ) :
    x ∈ upperHull v ↔ ∃ w : ι → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ j, ∑ i, w i * v i j ≤ x j) := by
  classical
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [convexHull_range_eq_exists_affineCombination] at hy
    obtain ⟨s, w, hw, hs, hsum⟩ := hy
    let W : ι → ℝ := fun i => if i ∈ s then w i else 0
    refine ⟨W, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ s <;> simp [W, hi, hw i]
    · simpa only [W, Finset.sum_ite_mem, Finset.univ_inter] using hs
    · intro j
      have hsj := congrFun hsum j
      rw [Finset.affineCombination_eq_linear_combination s v w hs] at hsj
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hsj
      calc
        (∑ i, W i * v i j) = ∑ i ∈ s, w i * v i j := by
          simp [W, ite_mul]
        _ = y j := hsj
        _ ≤ x j := hxy j
  · rintro ⟨w, hw, hs, hwx⟩
    let y : ν → ℝ := ∑ i, w i • v i
    refine ⟨y, ?_, ?_⟩
    · exact mem_convexHull_of_exists_fintype w v hw hs (fun i => ⟨i,rfl⟩) rfl
    · intro j
      simpa only [y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hwx j

/-- Integer data and real barycentric feasibility give exact rational
barycentric feasibility, including points on every boundary face. -/
theorem rational_dominated_combination {ι ν : Type*} [Fintype ι] [Fintype ν]
    (v : ι → ν → ℕ) (x : ν → ℕ)
    (h : ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ j, ∑ i, w i * (v i j : ℝ) ≤ x j) :
    ∃ w : ι → ℚ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      ∀ j, ∑ i, w i * (v i j : ℚ) ≤ x j := by
  classical
  let J := ι ⊕ (Unit ⊕ (Unit ⊕ ν))
  let A : J → ι → ℚ := fun q i => match q with
    | Sum.inl k => if i = k then -1 else 0
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr (Sum.inl _)) => -1
    | Sum.inr (Sum.inr (Sum.inr j)) => v i j
  let b : J → ℚ := fun q => match q with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr (Sum.inl _)) => -1
    | Sum.inr (Sum.inr (Sum.inr j)) => x j
  have hh : ∃ w : ι → ℝ, ∀ q, ∑ i, (A q i : ℝ) * w i ≤ b q := by
    obtain ⟨w, hw, hs, hv⟩ := h
    refine ⟨w, ?_⟩
    intro q
    rcases q with i | (u | (u | j))
    · simpa [A,b,apply_ite,ite_mul] using neg_nonpos.mpr (hw i)
    · simpa [A,b,hs]
    · simp [A,b, Finset.sum_neg_distrib,hs]
    · simpa [A,b,mul_comm] using hv j
  obtain ⟨w, hw⟩ := rational_solution_finite A b hh
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i
    have hh := hw (Sum.inl i)
    simpa [A,b] using hh
  · have hlo := hw (Sum.inr (Sum.inr (Sum.inl ())))
    have hhi := hw (Sum.inr (Sum.inl ()))
    simp only [A,b, one_mul, neg_one_mul, Finset.sum_neg_distrib] at hlo hhi
    linarith
  · intro j
    simpa only [A,b,mul_comm] using hw (Sum.inr (Sum.inr (Sum.inr j)))

/-- Clear one positive common denominator for a finite nonnegative family. -/
theorem common_natural_denominator {ι : Type*} [Fintype ι]
    (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) :
    ∃ q : ℕ, 0 < q ∧ ∃ p : ι → ℕ, ∀ i, (p i : ℚ) = (q : ℚ) * w i := by
  classical
  let q : ℕ := ∏ i, (w i).den
  have hq : 0 < q := Finset.prod_pos (fun i _ => (w i).den_pos)
  let p : ι → ℕ := fun i => (q / (w i).den) * (w i).num.toNat
  refine ⟨q,hq,p,?_⟩
  intro i
  have hdvd : (w i).den ∣ q := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hd : q / (w i).den * (w i).den = q := Nat.div_mul_cancel hdvd
  have hdq : ((q / (w i).den : ℕ) : ℚ) * (w i).den = q := by exact_mod_cast hd
  have hn : (((w i).num.toNat : ℕ) : ℚ) = (w i).num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hw i))
  dsimp only [p]
  rw [Nat.cast_mul, hn]
  calc
    ((q / (w i).den : ℕ) : ℚ) * (w i).num =
        (((q / (w i).den : ℕ) : ℚ) * (w i).den) *
          ((w i).num / (w i).den) := by
      field_simp
    _ = (q : ℚ) * w i := by rw [hdq, (w i).num_div_den]

/-- The natural certificate retains the barycentric equation and every
coordinate inequality exactly, so it can be read as multiplicities of factors. -/
theorem natural_certificate {ι ν : Type*} [Fintype ι] [Fintype ν]
    (v : ι → ν → ℕ) (x : ν → ℕ)
    (h : (fun j => (x j : ℝ)) ∈ upperHull (fun i j => (v i j : ℝ))) :
    ∃ q : ℕ, 0 < q ∧ ∃ p : ι → ℕ,
      (∑ i, p i) = q ∧ (∀ j, ∑ i, p i * v i j ≤ q * x j) := by
  obtain ⟨w, hw, hs, hv⟩ := rational_dominated_combination v x
    ((mem_upperHull_iff_combination _ _).mp h)
  obtain ⟨q, hq, p, hp⟩ := common_natural_denominator w hw
  refine ⟨q,hq,p,?_,?_⟩
  · have he : (∑ i, (p i : ℚ)) = q := by
      simp_rw [hp]
      rw [← Finset.mul_sum, hs, mul_one]
    exact_mod_cast he
  · intro j
    have hh := mul_le_mul_of_nonneg_left (hv j) (show (0 : ℚ) ≤ q from Nat.cast_nonneg q)
    have he : (∑ i, (p i : ℚ) * (v i j : ℚ)) ≤ (q : ℚ) * (x j : ℚ) := by
      simpa only [Finset.mul_sum, hp, mul_assoc] using hh
    exact_mod_cast he

end FourPapers.Symmetric.RationalPolyhedra
end
