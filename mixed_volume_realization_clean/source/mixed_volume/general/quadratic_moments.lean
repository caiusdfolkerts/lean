module

public import mixed_volume.general.moment_geometry

/-! A finite rational system for every pairwise mixed area of the automaton
zonoids.  The same-letter terms are the only recursive terms. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.QuadraticMoments

open VolumePolynomials AutomatonWords AutomatonZonoids AutomatonMoments AutomatonRecurrence
open MomentGeometry VolumePolynomials.PlanarMixedForm BodyContraction Matrix Set MeasureTheory
open scoped Pointwise BigOperators

variable {s m : ℕ}

def twiceMixed (K L : ConvexBody Plane) : ℝ := 2 * mixedArea volume K L

theorem twiceMixed_symm (K L : ConvexBody Plane) : twiceMixed K L = twiceMixed L K := by
  rw [twiceMixed, mixedArea_symm]
  rfl

theorem twiceMixed_add_left (K L M : ConvexBody Plane) :
    twiceMixed (K + L) M = twiceMixed K M + twiceMixed L M := by
  simp only [twiceMixed, mixedArea_add_left]
  ring

theorem twiceMixed_add_right (K L M : ConvexBody Plane) :
    twiceMixed K (L + M) = twiceMixed K L + twiceMixed K M := by
  simp only [twiceMixed, mixedArea_add_right]
  ring

theorem twiceMixed_smul_left (K L : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    twiceMixed (r • K) L = r * twiceMixed K L := by
  simp only [twiceMixed, mixedArea_smul_left volume _ _ hr]
  ring

theorem twiceMixed_smul_right (K L : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    twiceMixed K (r • L) = r * twiceMixed K L := by
  simp only [twiceMixed, mixedArea_smul_right volume _ _ hr]
  ring

theorem twiceMixed_sum_left {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) (L : ConvexBody Plane) :
    twiceMixed (∑ i, K i) L = ∑ i, twiceMixed (K i) L := by
  simp only [twiceMixed, mixedArea_sum_left, Finset.mul_sum]

theorem twiceMixed_sum_right {ι : Type*} [Fintype ι] (K : ι → ConvexBody Plane) (L : ConvexBody Plane) :
    twiceMixed L (∑ i, K i) = ∑ i, twiceMixed L (K i) := by
  simp only [twiceMixed, mixedArea_sum_right, Finset.mul_sum]

theorem twiceMixed_unitY_left (K : ConvexBody Plane) :
    twiceMixed PlanarCorner.unitY K = PlanarCorner.width K := by
  rw [twiceMixed_symm]
  exact PlanarCorner.twice_mixedArea_unitY K

theorem twiceMixed_unitY_right (K : ConvexBody Plane) :
    twiceMixed K PlanarCorner.unitY = PlanarCorner.width K :=
  PlanarCorner.twice_mixedArea_unitY K

def pairMoment (A : Data s m) (hs : 0 < s) (p : Fin m × Fin m) : ℝ :=
  twiceMixed (stateBody A hs p.1) (stateBody A hs p.2)

def crossMoment (A : Data s m) (a b : Fin s) (j k : Fin m) : ℝ :=
  if a < b then imageFactor s * (((b.val : ℝ) - (a.val : ℝ)) * mass A j * mass A k +
    mass A j * first A k - first A j * mass A k)
  else if b < a then imageFactor s * (((a.val : ℝ) - (b.val : ℝ)) * mass A k * mass A j +
    mass A k * first A j - first A k * mass A j)
  else 0

theorem image_mixed (A : Data s m) (hs : 0 < s) (a b : Fin s) (j k : Fin m) :
    twiceMixed (mapBody (transition a) (stateBody A hs j))
      (mapBody (transition b) (stateBody A hs k)) =
      (if a = b then imageFactor s * pairMoment A hs (j,k) else 0) + crossMoment A a b j k := by
  rcases lt_trichotomy a b with hab | hab | hab
  · simp only [ne_of_lt hab, if_false, crossMoment, hab, if_true, zero_add]
    exact mixed_distinct_images_lt A hs a b hab j k
  · subst b
    simp only [if_true, crossMoment, lt_self_iff_false, if_false, add_zero]
    exact mixed_same_image A hs a j k
  · simp only [ne_of_gt hab, if_false, crossMoment, not_lt_of_gt hab, hab, if_true, zero_add]
    rw [twiceMixed_symm]
    exact mixed_distinct_images_lt A hs b a hab k j

theorem state_left_expansion (A : Data s m) (hs : 0 < s) (j : Fin m) (L : ConvexBody Plane) :
    twiceMixed (stateBody A hs j) L = (1 + A.f j) * PlanarCorner.width L +
      ∑ a, ∑ k, A.P a j k * twiceMixed (mapBody (transition a) (stateBody A hs k)) L := by
  have hb : 0 ≤ 1 + A.f j := by linarith [A.f_nonneg j]
  rw [state_equation A hs j]
  simp only [bodyOperator, twiceMixed_add_left]
  rw [twiceMixed_smul_left _ _ hb, twiceMixed_unitY_left]
  simp only [twiceMixed_sum_left, twiceMixed_smul_left _ _ (A.P_nonneg _ _ _)]

theorem state_right_expansion (A : Data s m) (hs : 0 < s) (k : Fin m) (L : ConvexBody Plane) :
    twiceMixed L (stateBody A hs k) = (1 + A.f k) * PlanarCorner.width L +
      ∑ a, ∑ j, A.P a k j * twiceMixed L (mapBody (transition a) (stateBody A hs j)) := by
  rw [twiceMixed_symm, state_left_expansion]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  rw [twiceMixed_symm]

def areaSource (A : Data s m) (j k : Fin m) : ℝ :=
  (1 + A.f j) * first A k + ∑ a, ∑ l, A.P a j l *
    ((1 + A.f k) * (rho s / base s * (first A l + ((a.val : ℝ) + 1) * mass A l)) +
      ∑ b, ∑ r, A.P b k r * crossMoment A a b l r)

def areaMatrixReal (A : Data s m) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  fun p q => imageFactor s * ∑ a, A.P a p.1 q.1 * A.P a p.2 q.2

theorem pair_recurrence (A : Data s m) (hs : 0 < s) (j k : Fin m) :
    pairMoment A hs (j,k) = areaSource A j k +
      ∑ a, ∑ l, ∑ r, imageFactor s * A.P a j l * A.P a k r * pairMoment A hs (l,r) := by
  rw [pairMoment, state_left_expansion, state_width]
  simp_rw [state_right_expansion, image_width, image_mixed]
  simp only [mul_add, Finset.sum_add_distrib]
  have hsplit (a : Fin s) (l : Fin m) :
      (∑ b, ∑ r, A.P b k r * (if a = b then imageFactor s * pairMoment A hs (l,r) else 0)) =
        ∑ r, A.P a k r * (imageFactor s * pairMoment A hs (l,r)) := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    simp
  simp_rw [hsplit]
  dsimp [areaSource]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show (∑ a, ∑ l, A.P a j l * ∑ r, A.P a k r *
      (imageFactor s * pairMoment A hs (l,r))) =
      ∑ a, ∑ l, ∑ r, imageFactor s * A.P a j l * A.P a k r * pairMoment A hs (l,r) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring]
  ring

theorem pair_matrix_equation (A : Data s m) (hs : 0 < s) :
    pairMoment A hs = (fun p => areaSource A p.1 p.2) + areaMatrixReal A *ᵥ pairMoment A hs := by
  funext p
  rcases p with ⟨j,k⟩
  rw [pair_recurrence]
  change _ = areaSource A j k + ∑ q, areaMatrixReal A (j,k) q * pairMoment A hs q
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [areaMatrixReal, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  ring


def imageFactorQ (s : ℕ) : ℚ := rhoQ s ^ 2 / baseQ s

@[simp] theorem cast_imageFactorQ (s : ℕ) : (imageFactorQ s : ℝ) = imageFactor s := by
  simp [imageFactorQ,imageFactor]

def crossMomentQ (A : RationalData s m) (a b : Fin s) (j k : Fin m) : ℚ :=
  if a < b then imageFactorQ s * (((b.val : ℚ) - (a.val : ℚ)) * massQ A j * massQ A k +
    massQ A j * firstQ A k - firstQ A j * massQ A k)
  else if b < a then imageFactorQ s * (((a.val : ℚ) - (b.val : ℚ)) * massQ A k * massQ A j +
    massQ A k * firstQ A j - firstQ A k * massQ A j)
  else 0

def areaSourceQ (A : RationalData s m) (p : Fin m × Fin m) : ℚ :=
  (1 + A.f p.1) * firstQ A p.2 + ∑ a, ∑ l, A.P a p.1 l *
    ((1 + A.f p.2) * (rhoQ s / baseQ s * (firstQ A l + ((a.val : ℚ) + 1) * massQ A l)) +
      ∑ b, ∑ r, A.P b p.2 r * crossMomentQ A a b l r)

def areaMatrix (A : RationalData s m) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℚ :=
  fun p q => imageFactorQ s * ∑ a, A.P a p.1 q.1 * A.P a p.2 q.2

def pairMomentQ (A : RationalData s m) : (Fin m × Fin m) → ℚ :=
  RationalSystems.rationalSolution (areaMatrix A) (areaSourceQ A)

theorem cast_crossMomentQ (A : RationalData s m) (hs : 0 < s)
    (a b : Fin s) (j k : Fin m) :
    (crossMomentQ A a b j k : ℝ) = crossMoment A.toReal a b j k := by
  have hm (j : Fin m) : mass A.toReal j = (massQ A j : ℝ) := congrFun (mass_eq_rational A hs) j
  have hx (j : Fin m) : first A.toReal j = (firstQ A j : ℝ) := congrFun (first_eq_rational A hs) j
  simp only [crossMomentQ,crossMoment,hm,hx]
  split_ifs <;> simp only [Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_natCast,
    Rat.cast_zero,cast_imageFactorQ]

theorem cast_areaSourceQ (A : RationalData s m) (hs : 0 < s) (p : Fin m × Fin m) :
    (areaSourceQ A p : ℝ) = areaSource A.toReal p.1 p.2 := by
  have hm (j : Fin m) : mass A.toReal j = (massQ A j : ℝ) := congrFun (mass_eq_rational A hs) j
  have hx (j : Fin m) : first A.toReal j = (firstQ A j : ℝ) := congrFun (first_eq_rational A hs) j
  simp only [areaSourceQ,areaSource,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sum,
    Rat.cast_one,Rat.cast_natCast,cast_rhoQ,cast_baseQ,cast_crossMomentQ A hs,hm,hx]
  rfl

@[simp] theorem cast_areaMatrix (A : RationalData s m) :
    RationalSystems.castMatrix (areaMatrix A) = areaMatrixReal A.toReal := by
  ext p q
  simp only [RationalSystems.castMatrix,areaMatrix,areaMatrixReal,Rat.cast_mul,Rat.cast_sum,
    cast_imageFactorQ,RationalData.toReal]

theorem areaMatrix_row (A : RationalData s m) (hs : 0 < s) (p : Fin m × Fin m) :
    (∑ q, |(areaMatrix A p q : ℝ)|) ≤ 1 / 4 := by
  have hnonneg (q : Fin m × Fin m) : 0 ≤ (areaMatrix A p q : ℝ) := by
    simp only [areaMatrix,Rat.cast_mul,Rat.cast_sum,cast_imageFactorQ]
    apply mul_nonneg (imageFactor_nonneg hs)
    exact Finset.sum_nonneg fun a _ => mul_nonneg
      (by exact_mod_cast A.P_nonneg a p.1 q.1) (by exact_mod_cast A.P_nonneg a p.2 q.2)
  simp_rw [abs_of_nonneg (hnonneg _)]
  have heq : (∑ q, (areaMatrix A p q : ℝ)) = imageFactor s * (s : ℝ) := by
    simp only [areaMatrix,Rat.cast_mul,Rat.cast_sum,cast_imageFactorQ]
    rw [← Finset.mul_sum,Finset.sum_comm]
    have hrow (a : Fin s) :
        (∑ q : Fin m × Fin m, (A.P a p.1 q.1 : ℝ) * (A.P a p.2 q.2 : ℝ)) = 1 := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum]
      have hp2 : ∑ r, (A.P a p.2 r : ℝ) = 1 := by exact_mod_cast A.P_sum a p.2
      have hp1 : ∑ l, (A.P a p.1 l : ℝ) = 1 := by exact_mod_cast A.P_sum a p.1
      rw [hp2]
      simp only [mul_one]
      exact hp1
    simp_rw [hrow]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [heq]
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hrho : rho s ≤ 1 := by
    dsimp [rho]
    apply (div_le_one (by positivity : (0 : ℝ) < 4 * s)).2
    linarith
  have hbase : 1 ≤ base s := by dsimp [base]; linarith
  have hquot : rho s / base s ≤ 1 := (div_le_one (base_pos s)).2 (hrho.trans hbase)
  calc
    imageFactor s * (s : ℝ) = ((s : ℝ) * rho s) * (rho s / base s) := by dsimp [imageFactor]; ring
    _ = (1 / 4 : ℝ) * (rho s / base s) := by rw [card_mul_rho hs]
    _ ≤ 1 / 4 := by nlinarith

/-- Every pairwise mixed area of the canonical stochastic bodies is the cast
of an explicitly specified rational number. -/
theorem pairMoment_eq_rational (A : RationalData s m) (hs : 0 < s) :
    pairMoment A.toReal hs = RationalSystems.castVector (pairMomentQ A) := by
  apply RationalSystems.real_solution_is_rational (areaMatrix A) (areaSourceQ A)
    (1 / 4) (by norm_num) (by norm_num) (areaMatrix_row A hs)
  rw [cast_areaMatrix]
  have hb : RationalSystems.castVector (areaSourceQ A) =
      fun p => areaSource A.toReal p.1 p.2 := by
    funext p
    exact cast_areaSourceQ A hs p
  rw [hb]
  exact pair_matrix_equation A.toReal hs

end MixedVolume.QuadraticMoments

end
