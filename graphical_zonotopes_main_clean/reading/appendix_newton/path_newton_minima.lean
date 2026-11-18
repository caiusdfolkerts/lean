module

public import Papers.GraphicalZonotopes.TropicalContinuant
public import Papers.GraphicalZonotopes.PathPolytope
public import Papers.GraphicalZonotopes.Zonotope

/-!
# Every real linear minimum of the path polytope

The path set function is the sum of its triple and gap-triple unanimity functions
minus its quadruple unanimity functions. Minkowski addition of genuine base
polytopes turns this identity into an equality of linear minima. The resulting
formula is exactly the minimum-plus positive-continuant formula.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes.PathNewtonMinima

open Finset TropicalContinuant

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary linear functional specified by a vector of real weights. -/
def weightMap (w : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ v, w v * x v
  map_add' x y := by simp [mul_add, sum_add_distrib]
  map_smul' a x := by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- An attained minimum of the actual linear functional on the actual set. -/
def HasMinimum (w : V → ℝ) (Q : Set (V → ℝ)) (a : ℝ) : Prop :=
  IsLeast (weightMap w '' Q) a

@[simp] theorem weightMap_apply (w x : V → ℝ) : weightMap w x = ∑ v, w v * x v := rfl

@[simp] theorem weightMap_basisVector (w : V → ℝ) (v : V) :
    weightMap w (basisVector v) = w v := by
  simp [weightMap, basisVector, Pi.single_apply, mul_ite, eq_comm]

/-- Attained linear minima add under actual Minkowski addition. -/
theorem minimum_add {w : V → ℝ} {Q R : Set (V → ℝ)} {a b : ℝ}
    (hQ : HasMinimum w Q a) (hR : HasMinimum w R b) :
    HasMinimum w (Q + R) (a + b) := by
  rcases hQ.1 with ⟨x, hx, hxa⟩
  rcases hR.1 with ⟨y, hy, hyb⟩
  refine ⟨⟨x + y, Set.add_mem_add hx hy, by rw [map_add, hxa, hyb]⟩, ?_⟩
  rintro t ⟨z, ⟨u, hu, v, hv, rfl⟩, rfl⟩
  rw [map_add]
  exact add_le_add (hQ.2 ⟨u, hu, rfl⟩) (hR.2 ⟨v, hv, rfl⟩)

/-- Cancellation of an attained linear minimum from a Minkowski sum. -/
theorem minimum_of_add {w : V → ℝ} {Q R : Set (V → ℝ)} {a b : ℝ}
    (hQR : HasMinimum w (Q + R) a) (hR : HasMinimum w R b) :
    HasMinimum w Q (a - b) := by
  rcases hR.1 with ⟨y, hy, hyb⟩
  have lower : ∀ x ∈ Q, a - b ≤ weightMap w x := by
    intro x hx
    have h := hQR.2 ⟨x + y, Set.add_mem_add hx hy, rfl⟩
    rw [map_add, hyb] at h
    linarith
  rcases hQR.1 with ⟨z, ⟨x, hx, u, hu, rfl⟩, hza⟩
  have huLower := hR.2 ⟨u, hu, rfl⟩
  have hxLower := lower x hx
  have hxEq : weightMap w x = a - b := by
    rw [map_add] at hza
    linarith
  refine ⟨⟨x, hx, hxEq⟩, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  exact lower x hx

/-- A unanimity base polytope has the expected minimum over its supported basis
vectors. The argument allows every nonempty support, including a singleton. -/
theorem minimum_setMonomial (C : Finset V) (w : V → ℝ) (a : ℝ)
    (ha : IsLeast (w '' (C : Set V)) a) :
    HasMinimum w (basePolytope (setMonomial C)) a := by
  rcases ha.1 with ⟨v, hv, hva⟩
  have hvBase : basisVector v ∈ basePolytope (setMonomial C) := by
    refine ⟨by simp [setMonomial], ?_⟩
    intro S
    rw [subsetSum_basisVector]
    by_cases hCS : C ⊆ S
    · simp [setMonomial, hCS, hCS hv]
    · simp only [setMonomial, if_neg hCS]
      split_ifs <;> norm_num
  refine ⟨⟨basisVector v, hvBase, (weightMap_basisVector w v).trans hva⟩, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  have htotal : subsetSum x univ = 1 := by simpa [setMonomial] using hx.1
  have hnonnegative : ∀ j, 0 ≤ x j := by
    intro j
    have hzero : 0 ≤ setMonomial C {j} := by
      unfold setMonomial
      split_ifs <;> norm_num
    have h := hx.2 {j}
    simpa [subsetSum] using hzero.trans h
  have houtside : ∀ j, j ∉ C → x j = 0 := by
    intro j hj
    have hCS : C ⊆ univ.erase j := by
      intro k hk
      exact mem_erase.mpr ⟨fun h => hj (h ▸ hk), mem_univ k⟩
    have hmin : 1 ≤ subsetSum x (univ.erase j) := by
      simpa [setMonomial, hCS] using hx.2 (univ.erase j)
    have hsum : subsetSum x (univ.erase j) + x j = 1 := by
      rw [subsetSum, sum_erase_add _ _ (mem_univ j)]
      exact htotal
    linarith [hnonnegative j]
  have hsum : (∑ j ∈ C, x j) = 1 := by
    calc
      (∑ j ∈ C, x j) = ∑ j ∈ univ, x j :=
        sum_subset (subset_univ _) (fun j _ hj => houtside j hj)
      _ = 1 := htotal
  have hweight : (∑ j ∈ C, w j * x j) = weightMap w x := by
    change (∑ j ∈ C, w j * x j) = ∑ j ∈ univ, w j * x j
    apply sum_subset (subset_univ _)
    intro j _ hj
    simp [houtside j hj]
  calc
    a = a * (∑ j ∈ C, x j) := by rw [hsum, mul_one]
    _ = ∑ j ∈ C, a * x j := by rw [mul_sum]
    _ ≤ ∑ j ∈ C, w j * x j := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (ha.2 ⟨j, hj, rfl⟩) (hnonnegative j)
    _ = weightMap w x := hweight

private theorem image_three_minimum (w : V → ℝ) (a b c : V) :
    IsLeast (w '' (({a, b, c} : Finset V) : Set V))
      (min (w a) (min (w b) (w c))) := by
  simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, Set.singleton_union] using
    (isLeast_singleton : IsLeast ({w a} : Set ℝ) (w a)).union
      ((isLeast_singleton : IsLeast ({w b} : Set ℝ) (w b)).union (isLeast_singleton : IsLeast ({w c} : Set ℝ) (w c)))

private theorem image_four_minimum (w : V → ℝ) (a b c d : V) :
    IsLeast (w '' (({a, b, c, d} : Finset V) : Set V))
      (min (w a) (min (w b) (min (w c) (w d)))) := by
  simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, Set.singleton_union] using
    (isLeast_singleton : IsLeast ({w a} : Set ℝ) (w a)).union
      ((isLeast_singleton : IsLeast ({w b} : Set ℝ) (w b)).union
        ((isLeast_singleton : IsLeast ({w c} : Set ℝ) (w c)).union (isLeast_singleton : IsLeast ({w d} : Set ℝ) (w d))))

/-- Linear minima of a finite sum of normalized supermodular functions. -/
theorem minimum_basePolytope_sum {I : Type*} (s : Finset I)
    (f : I → SetFunction V) (w : V → ℝ) (a : I → ℝ)
    (hn : ∀ i ∈ s, Normalized (f i))
    (hs : ∀ i ∈ s, Supermodular (f i))
    (hm : ∀ i ∈ s, HasMinimum w (basePolytope (f i)) (a i)) :
    HasMinimum w (basePolytope (∑ i ∈ s, f i)) (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa [HasMinimum, basePolytope_zero] using (isLeast_singleton : IsLeast ({0} : Set ℝ) 0)
  | @insert i s hi ih =>
      have hns : Normalized (∑ j ∈ s, f j) := by
        simp only [Normalized, Finset.sum_apply]
        exact sum_eq_zero (fun j hj => hn j (mem_insert_of_mem hj))
      have hss : Supermodular (∑ j ∈ s, f j) :=
        Supermodular.finset_sum s f (fun j hj => hs j (mem_insert_of_mem hj))
      simp only [sum_insert hi]
      rw [basePolytope_add (hn i (mem_insert_self _ _)) hns
        (hs i (mem_insert_self _ _)) hss]
      exact minimum_add (hm i (mem_insert_self _ _))
        (ih (fun j hj => hn j (mem_insert_of_mem hj))
          (fun j hj => hs j (mem_insert_of_mem hj))
          (fun j hj => hm j (mem_insert_of_mem hj)))

private theorem window_nonempty {n p : ℕ} (i : Fin (n - p))
    (C : Finset ℕ) (hC : 0 ∈ C) : (Path.window n i.val C).Nonempty := by
  have hi : i.val < n := i.isLt.trans_le (Nat.sub_le n p)
  refine ⟨⟨i.val, hi⟩, ?_⟩
  simp [Path.mem_window, hC]

private theorem minimum_triple {n : ℕ} (w : ℕ → ℝ) (i : Fin (n - 2)) :
    HasMinimum (fun v : Fin n => w v.val)
      (basePolytope (setMonomial (Path.window n i.val {0, 1, 2})))
      (tripleMinimum w i.val) := by
  apply minimum_setMonomial
  rw [Path.window_triple_eq
    (Path.window_index_bound i (by decide : 0 ≤ 2))
    (Path.window_index_bound i (by decide : 1 ≤ 2))
    (Path.window_index_bound i (by decide : 2 ≤ 2))]
  simpa [tripleMinimum, Path.vertex] using
    image_three_minimum (fun v : Fin n => w v.val)
      (Path.vertex n i.val 0 (Path.window_index_bound i (by decide : 0 ≤ 2)))
      (Path.vertex n i.val 1 (Path.window_index_bound i (by decide : 1 ≤ 2)))
      (Path.vertex n i.val 2 (Path.window_index_bound i (by decide : 2 ≤ 2)))

private theorem minimum_gap {n : ℕ} (w : ℕ → ℝ) (i : Fin (n - 3)) :
    HasMinimum (fun v : Fin n => w v.val)
      (basePolytope (setMonomial (Path.window n i.val {0, 2, 3})))
      (gapMinimum w i.val) := by
  apply minimum_setMonomial
  rw [Path.window_triple_eq
    (Path.window_index_bound i (by decide : 0 ≤ 3))
    (Path.window_index_bound i (by decide : 2 ≤ 3))
    (Path.window_index_bound i (by decide : 3 ≤ 3))]
  simpa [gapMinimum, Path.vertex] using
    image_three_minimum (fun v : Fin n => w v.val)
      (Path.vertex n i.val 0 (Path.window_index_bound i (by decide : 0 ≤ 3)))
      (Path.vertex n i.val 2 (Path.window_index_bound i (by decide : 2 ≤ 3)))
      (Path.vertex n i.val 3 (Path.window_index_bound i (by decide : 3 ≤ 3)))

private theorem minimum_quadruple {n : ℕ} (w : ℕ → ℝ) (i : Fin (n - 3)) :
    HasMinimum (fun v : Fin n => w v.val)
      (basePolytope (setMonomial (Path.window n i.val {0, 1, 2, 3})))
      (quadrupleMinimum w i.val) := by
  apply minimum_setMonomial
  rw [Path.window_quad_eq
    (Path.window_index_bound i (by decide : 0 ≤ 3))
    (Path.window_index_bound i (by decide : 1 ≤ 3))
    (Path.window_index_bound i (by decide : 2 ≤ 3))
    (Path.window_index_bound i (by decide : 3 ≤ 3))]
  simpa [quadrupleMinimum, Path.vertex] using
    image_four_minimum (fun v : Fin n => w v.val)
      (Path.vertex n i.val 0 (Path.window_index_bound i (by decide : 0 ≤ 3)))
      (Path.vertex n i.val 1 (Path.window_index_bound i (by decide : 1 ≤ 3)))
      (Path.vertex n i.val 2 (Path.window_index_bound i (by decide : 2 ≤ 3)))
      (Path.vertex n i.val 3 (Path.window_index_bound i (by decide : 3 ≤ 3)))

/-- The exact local support formula for every real linear functional on the path
base polytope, including attainment of the minimum. -/
theorem path_polytope_minimum_formula (n : ℕ) (w : ℕ → ℝ) :
    HasMinimum (fun v : Fin n => w v.val) (Path.polytope n)
      ((∑ i : Fin (n - 2), tripleMinimum w i.val) +
        (∑ i : Fin (n - 3), gapMinimum w i.val) -
        (∑ i : Fin (n - 3), quadrupleMinimum w i.val)) := by
  let f : Fin (n - 2) → SetFunction (Fin n) := fun i =>
    setMonomial (Path.window n i.val {0, 1, 2})
  let g : Fin (n - 3) → SetFunction (Fin n) := fun i =>
    setMonomial (Path.window n i.val {0, 2, 3})
  let h : Fin (n - 3) → SetFunction (Fin n) := fun i =>
    setMonomial (Path.window n i.val {0, 1, 2, 3})
  have hfn : ∀ i, Normalized (f i) := fun i =>
    setMonomial_normalized (window_nonempty i _ (by simp))
  have hgn : ∀ i, Normalized (g i) := fun i =>
    setMonomial_normalized (window_nonempty i _ (by simp))
  have hhn : ∀ i, Normalized (h i) := fun i =>
    setMonomial_normalized (window_nonempty i _ (by simp))
  have hfs : ∀ i, Supermodular (f i) := fun i => setMonomial_supermodular _
  have hgs : ∀ i, Supermodular (g i) := fun i => setMonomial_supermodular _
  have hhs : ∀ i, Supermodular (h i) := fun i => setMonomial_supermodular _
  have hfmin := minimum_basePolytope_sum univ f (fun v : Fin n => w v.val)
    (fun i => tripleMinimum w i.val) (fun i _ => hfn i) (fun i _ => hfs i)
    (fun i _ => minimum_triple w i)
  have hgmin := minimum_basePolytope_sum univ g (fun v : Fin n => w v.val)
    (fun i => gapMinimum w i.val) (fun i _ => hgn i) (fun i _ => hgs i)
    (fun i _ => minimum_gap w i)
  have hhmin := minimum_basePolytope_sum univ h (fun v : Fin n => w v.val)
    (fun i => quadrupleMinimum w i.val) (fun i _ => hhn i) (fun i _ => hhs i)
    (fun i _ => minimum_quadruple w i)
  have hsumNorm (I : Type) [Fintype I] (q : I → SetFunction (Fin n))
      (hq : ∀ i, Normalized (q i)) : Normalized (∑ i, q i) := by
    simp only [Normalized, Finset.sum_apply]
    exact sum_eq_zero (fun i _ => hq i)
  have hsumSuper (I : Type) [Fintype I] (q : I → SetFunction (Fin n))
      (hq : ∀ i, Supermodular (q i)) : Supermodular (∑ i, q i) :=
    Supermodular.finset_sum univ q (fun i _ => hq i)
  have hidentity : Path.setFunction n + ∑ i, h i = (∑ i, f i) + ∑ i, g i := by
    rw [Path.setFunction_expansion]
    change ((∑ i, f i) + (∑ i, g i) - (∑ i, h i)) + (∑ i, h i) = _
    abel
  have hpoly : Path.polytope n + basePolytope (∑ i, h i) =
      basePolytope (∑ i, f i) + basePolytope (∑ i, g i) := by
    rw [Path.polytope, ← basePolytope_add
      (z := Path.setFunction n) (w := ∑ i, h i)
      (Path.setFunction_normalized n).1 (hsumNorm (Fin (n - 3)) h hhn)
      (Path.setFunction_supermodular n) (hsumSuper (Fin (n - 3)) h hhs),
      hidentity, basePolytope_add (z := ∑ i, f i) (w := ∑ i, g i)
        (hsumNorm (Fin (n - 2)) f hfn) (hsumNorm (Fin (n - 3)) g hgn)
        (hsumSuper (Fin (n - 2)) f hfs) (hsumSuper (Fin (n - 3)) g hgs)]
  have hminimum := minimum_add hfmin hgmin
  rw [← hpoly] at hminimum
  exact minimum_of_add hminimum hhmin

/-- The minimum of any real linear functional on the actual path polytope is the
first minimum-plus continuant coordinate. There is no hypothesis on the weights. -/
theorem path_polytope_minimum (m : ℕ) (w : ℕ → ℝ) :
    IsLeast ((fun x : Fin (m + 2) → ℝ => ∑ i, w i.val * x i) ''
      Path.polytope (m + 2)) (TropicalContinuant.first w m) := by
  change HasMinimum (fun v : Fin (m + 2) => w v.val) (Path.polytope (m + 2))
    (TropicalContinuant.first w m)
  have h := path_polytope_minimum_formula (m + 2) w
  rw [TropicalContinuant.first_eq_closedFormula]
  simpa only [TropicalContinuant.closedFormula, Nat.add_sub_cancel,
    show m + 2 - 3 = m - 1 by omega, Fin.sum_univ_eq_sum_range] using h

/-- Every continuous linear functional on the finite coordinate space is the
ordinary weighted sum of its values on the standard basis. -/
theorem weightMap_of_functional (f : (V → ℝ) →L[ℝ] ℝ) (x : V → ℝ) :
    weightMap (fun v => f (Pi.single v 1)) x = f x := by
  change (∑ v, f (Pi.single v 1) * x v) = f x
  rw [linearFunctional_eq_weighted_sum f x]
  exact sum_congr rfl (fun v _ => mul_comm _ _)

/-- A closed convex set is determined by the attained minima of all real linear
functionals. The comparison set need not itself be convex for this inclusion. -/
theorem subset_of_same_linear_minima {Q R : Set (V → ℝ)}
    (hRconvex : Convex ℝ R) (hRclosed : IsClosed R)
    (hmin : ∀ w : V → ℝ, ∃ a, HasMinimum w Q a ∧ HasMinimum w R a) : Q ⊆ R := by
  intro x hx
  by_contra hout
  obtain ⟨f, c, hxc, hcf⟩ := geometric_hahn_banach_point_closed hRconvex hRclosed hout
  obtain ⟨a, hQmin, hRmin⟩ := hmin (fun v => f (Pi.single v 1))
  have hxa : a ≤ f x := by
    simpa only [weightMap_of_functional] using hQmin.2 ⟨x, hx, rfl⟩
  rcases hRmin.1 with ⟨y, hy, hya⟩
  have hya' : f y = a := by simpa only [weightMap_of_functional] using hya
  have hcy := hcf y hy
  linarith

/-- Equality of actual closed convex sets from their full real linear minima. -/
theorem eq_of_same_linear_minima {Q R : Set (V → ℝ)}
    (hQconvex : Convex ℝ Q) (hQclosed : IsClosed Q)
    (hRconvex : Convex ℝ R) (hRclosed : IsClosed R)
    (hmin : ∀ w : V → ℝ, ∃ a, HasMinimum w Q a ∧ HasMinimum w R a) : Q = R := by
  apply Set.Subset.antisymm (subset_of_same_linear_minima hRconvex hRclosed hmin)
  apply subset_of_same_linear_minima hQconvex hQclosed
  intro w
  obtain ⟨a, hQmin, hRmin⟩ := hmin w
  exact ⟨a, hRmin, hQmin⟩

end GraphicalZonotopes.PathNewtonMinima
