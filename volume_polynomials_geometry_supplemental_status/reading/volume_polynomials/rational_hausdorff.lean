module

public import VolumePolynomials.RationalGridBodies

@[expose] public section
set_option autoImplicit false

/-!
# Exact rational Hausdorff tests

A rational point is within sup-norm distance `r` of a rational convex hull
exactly when a finite rational linear system is feasible. Elimination checks
this system exactly. Testing only the listed vertices then suffices for both
Hausdorff inclusions, because convex hulls and norm balls are convex.
-/

open Set Metric
open scoped BigOperators Pointwise

namespace VolumePolynomials.RationalHulls

open RationalElimination

def feasibleTest {d : ℕ} (S : List (Inequality d)) : Prop :=
  ∀ p ∈ eliminateAll S, 0 ≤ p.bound

instance feasibleTest_decidable {d : ℕ} (S : List (Inequality d)) :
    Decidable (feasibleTest S) := by unfold feasibleTest; infer_instance

theorem feasibleTest_correct {d : ℕ} (S : List (Inequality d)) :
    feasibleTest S ↔ ∃ x : Space d, Satisfies S x := by
  first
  | rw [← eliminateAll_correct]
    unfold feasibleTest Satisfies Inequality.Holds Inequality.value
    simp

def coordinateConstraint {d : ℕ} (i : Fin d) (b : ℚ) : Inequality d :=
  ⟨fun j => if j = i then 1 else 0, b⟩

theorem coordinateConstraint_holds {d : ℕ} (i : Fin d) (b : ℚ) (x : Space d) :
    (coordinateConstraint i b).Holds x ↔ x i ≤ (b : ℝ) := by
  first
  | simp [Inequality.Holds, Inequality.value, coordinateConstraint, apply_ite, ite_mul]

def boxConstraints {d : ℕ} (q : RationalPoint d) (r : ℚ) : List (Inequality d) :=
  List.ofFn (fun i => coordinateConstraint i (q i + r)) ++
    List.ofFn (fun i => negative (coordinateConstraint i (q i - r)))

theorem boxConstraints_correct {d : ℕ} (q : RationalPoint d) (r : ℚ) (x : Space d) :
    Satisfies (boxConstraints q r) x ↔ ∀ i, |x i - (q i : ℝ)| ≤ (r : ℝ) := by
  first
  | simp only [boxConstraints, satisfies_append, satisfies_ofFn, coordinateConstraint_holds]
    have hneg : ∀ i, (negative (coordinateConstraint i (q i - r))).Holds x ↔
        (q i : ℝ) - (r : ℝ) ≤ x i := by
      intro i
      simp [Inequality.Holds, negative_value, coordinateConstraint, Inequality.value,
        negative, Rat.cast_sub, apply_ite, ite_mul, add_comm]
    simp only [hneg, Rat.cast_add]
    constructor
    · rintro ⟨hu, hl⟩ i
      exact abs_le.mpr ⟨by linarith [hl i], by linarith [hu i]⟩
    · intro h
      constructor <;> intro i <;> have hi := abs_le.mp (h i) <;> linarith

def pointNearTest {d : ℕ} (L : List (RationalPoint d)) (q : RationalPoint d) (r : ℚ) : Prop :=
  feasibleTest (hullHalfspaces L.get ++ boxConstraints q r)

instance pointNearTest_decidable {d : ℕ} (L : List (RationalPoint d))
    (q : RationalPoint d) (r : ℚ) : Decidable (pointNearTest L q r) := by
  first
  | unfold pointNearTest
    infer_instance

theorem pointNearTest_correct {d : ℕ} (L : List (RationalPoint d))
    (q : RationalPoint d) (r : ℚ) (hr : 0 ≤ r) :
    pointNearTest L q r ↔ ∃ x ∈ hull L, dist (realPoint q) x ≤ (r : ℝ) := by
  first
  | rw [pointNearTest, feasibleTest_correct]
    simp only [satisfies_append, boxConstraints_correct]
    have hh : ∀ x, Satisfies (hullHalfspaces L.get) x ↔ x ∈ hull L := by
      intro x
      change x ∈ solutionSet _ ↔ _
      rw [halfspaces_solution_eq_hull]
    simp only [hh]
    constructor
    · rintro ⟨x, hx, hdist⟩
      refine ⟨x, hx, (dist_pi_le_iff (by exact_mod_cast hr)).mpr ?_⟩
      intro i
      simpa only [realPoint, Real.dist_eq, abs_sub_comm] using hdist i
    · rintro ⟨x, hx, hdist⟩
      refine ⟨x, hx, ?_⟩
      intro i
      simpa only [realPoint, Real.dist_eq, abs_sub_comm] using
        (dist_pi_le_iff (by exact_mod_cast hr)).mp hdist i

def hausdorffTest {d : ℕ} (L M : List (RationalPoint d)) (r : ℚ) : Prop :=
  (∀ p ∈ L, pointNearTest M p r) ∧ ∀ q ∈ M, pointNearTest L q r

instance hausdorffTest_decidable {d : ℕ} (L M : List (RationalPoint d)) (r : ℚ) :
    Decidable (hausdorffTest L M r) := by unfold hausdorffTest; infer_instance

theorem hull_subset_add_closedBall {d : ℕ} (L M : List (RationalPoint d))
    (r : ℚ) (hr : 0 ≤ r) (h : ∀ p ∈ L, pointNearTest M p r) :
    hull L ⊆ hull M + closedBall 0 (r : ℝ) := by
  first
  | apply convexHull_min _ ((convex_convexHull ℝ _).add (convex_closedBall _ _))
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨y, hy, hdist⟩ := Iff.mp (pointNearTest_correct M p r hr) (h p hp)
    exact ⟨y, hy, realPoint p - y,
      by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hdist, by abel⟩

/-- The test is exactly the Hausdorff bound between the actual convex bodies. -/
theorem hausdorffTest_correct {d : ℕ} (L M : List (RationalPoint d))
    (hL : 0 ∈ L) (hM : 0 ∈ M) (r : ℚ) (hr : 0 ≤ r) :
    hausdorffTest L M r ↔ dist (body L hL) (body M hM) ≤ (r : ℝ) := by
  first
  | constructor
    · rintro ⟨hLM, hML⟩
      change hausdorffDist (hull L) (hull M) ≤ (r : ℝ)
      apply hausdorffDist_le_of_mem_dist (by exact_mod_cast hr)
      · intro x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := hull_subset_add_closedBall L M r hr hLM hx
        exact ⟨y, hy, by simpa only [mem_closedBall, dist_eq_norm, sub_zero,
          add_sub_cancel_left] using hz⟩
      · intro y hy
        obtain ⟨x, hx, z, hz, rfl⟩ := hull_subset_add_closedBall M L r hr hML hy
        exact ⟨x, hx, by simpa only [mem_closedBall, dist_eq_norm, sub_zero,
          add_sub_cancel_left] using hz⟩
    · intro hdist
      have hdir (A B : List (RationalPoint d)) (hA : 0 ∈ A) (hB : 0 ∈ B)
          (hdist : dist (body A hA) (body B hB) ≤ (r : ℝ)) :
          ∀ p ∈ A, pointNearTest B p r := by
        intro p hp
        have hpa : realPoint p ∈ body A hA := subset_convexHull ℝ _ ⟨p, hp, rfl⟩
        obtain ⟨x, hx, hdx⟩ := (body B hB).isCompact.exists_infDist_eq_dist
          (body B hB).nonempty (realPoint p)
        apply Iff.mpr (pointNearTest_correct B p r hr)
        refine ⟨x, hx, ?_⟩
        rw [← hdx]
        exact (infDist_le_hausdorffDist_of_mem hpa ConvexBody.hausdorffEDist_ne_top).trans hdist
      exact ⟨hdir L M hL hM hdist, hdir M L hM hL (by rwa [dist_comm])⟩

def tupleHausdorffTest {n d : ℕ}
    (L M : Fin n → List (RationalPoint d)) (r : ℚ) : Prop :=
  ∀ i, hausdorffTest (L i) (M i) r

instance tupleHausdorffTest_decidable {n d : ℕ}
    (L M : Fin n → List (RationalPoint d)) (r : ℚ) :
    Decidable (tupleHausdorffTest L M r) := by unfold tupleHausdorffTest; infer_instance

theorem tupleHausdorffTest_correct {n d : ℕ}
    (L M : Fin n → List (RationalPoint d)) (hL : ∀ i, 0 ∈ L i) (hM : ∀ i, 0 ∈ M i)
    (r : ℚ) (hr : 0 ≤ r) :
    tupleHausdorffTest L M r ↔
      dist (fun i => body (L i) (hL i)) (fun i => body (M i) (hM i)) ≤ (r : ℝ) := by
  first
  | rw [dist_pi_le_iff (by exact_mod_cast hr)]
    exact forall_congr' (fun i => hausdorffTest_correct (L i) (M i) (hL i) (hM i) r hr)

end VolumePolynomials.RationalHulls
