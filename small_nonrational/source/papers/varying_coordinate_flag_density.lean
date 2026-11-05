module
public import Papers.FixedCoordinateFlagDensity

@[expose] public section
noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.FixedCoordinateFlagDensity

open ChirotopeDensity PlaneRationalization

/-- Scaling uses the zero pattern of the original normal, so it is continuous
in the perturbed normal even at an originally zero coordinate. -/
def coordinateScale {n : ℕ} (a a' : Fin n → ℝ) (i : Fin n) : ℝ :=
  if a i = 0 then 1 else a' i

def normalPattern {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  if a i = 0 then 0 else 1

def normalizeSecond {n : ℕ} (a b : Fin n → ℝ) (i : Fin n) : ℝ :=
  b i / coordinateScale a a i

def restoreSecond {n : ℕ} (a a' z : Fin n → ℝ) (i : Fin n) : ℝ :=
  coordinateScale a a' i * z i

theorem coordinateScale_self_ne_zero {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    coordinateScale a a i ≠ 0 := by
  by_cases hi : a i = 0
  · simp [coordinateScale, hi]
  · simpa [coordinateScale, hi] using hi

theorem normalPattern_rational {n : ℕ} (a : Fin n → ℝ) :
    ∀ i, RatScalar (normalPattern a i) := by
  intro i
  by_cases hi : a i = 0
  · exact ⟨0, by simp [normalPattern, hi]⟩
  · exact ⟨1, by simp [normalPattern, hi]⟩

theorem restore_normalize {n : ℕ} (a b : Fin n → ℝ) :
    restoreSecond a a (normalizeSecond a b) = b := by
  ext i
  dsimp only [restoreSecond, normalizeSecond]
  rw [div_eq_mul_inv, mul_left_comm,
    mul_inv_cancel₀ (coordinateScale_self_ne_zero a i), mul_one]

theorem restoreSecond_rational {n : ℕ} (a a' z : Fin n → ℝ)
    (ha' : ∀ i, RatScalar (a' i)) (hz : ∀ i, RatScalar (z i)) :
    ∀ i, RatScalar (restoreSecond a a' z i) := by
  intro i
  apply RatScalar.mul _ (hz i)
  by_cases hi : a i = 0
  · exact ⟨1, by simp [coordinateScale, hi]⟩
  · simpa only [coordinateScale, if_neg hi] using ha' i

theorem pair_restore {n : ℕ} (a a' z : Fin n → ℝ)
    (hzero : ∀ i, a i = 0 → a' i = 0) :
    pair a' (restoreSecond a a' z) =
      fun i j => coordinateScale a a' i * pair (normalPattern a) z i j := by
  ext i j
  fin_cases j
  · by_cases hi : a i = 0
    · simp [pair, normalPattern, coordinateScale, hi, hzero i hi]
    · simp [pair, normalPattern, coordinateScale, hi]
  · rfl

theorem minor_rowScale {n : ℕ} (p : Fin n → Fin 2 → ℝ)
    (d : Fin n → ℝ) (s : Fin 2 → Fin n) :
    minor (fun i j => d i * p i j) s = d (s 0) * d (s 1) * minor p s := by
  simp only [minor, Matrix.det_fin_two, Matrix.of_apply, mul_sub]
  congr 1 <;> ac_rfl

theorem minor_restore {n : ℕ} (a a' z : Fin n → ℝ)
    (hzero : ∀ i, a i = 0 → a' i = 0) (s : Fin 2 → Fin n) :
    minor (pair a' (restoreSecond a a' z)) s =
      coordinateScale a a' (s 0) * coordinateScale a a' (s 1) *
        minor (pair (normalPattern a) z) s := by
  rw [pair_restore a a' z hzero]
  exact minor_rowScale _ _ _

theorem normalize_zero_minor {n : ℕ} (a b : Fin n → ℝ) (s : Fin 2 → Fin n)
    (h : minor (pair a b) s = 0) :
    minor (pair (normalPattern a) (normalizeSecond a b)) s = 0 := by
  have heq := minor_restore a a (normalizeSecond a b) (fun _ h => h) s
  rw [restore_normalize] at heq
  have hz : coordinateScale a a (s 0) * coordinateScale a a (s 1) *
      minor (pair (normalPattern a) (normalizeSecond a b)) s = 0 := heq.symm.trans h
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (coordinateScale_self_ne_zero a _) (coordinateScale_self_ne_zero a _))

/-- Relative zero-minor approximation over an arbitrary external dense
parameter set. The first normal may vary with that parameter; every required
zero of that normal is retained. No independence or genericity is assumed. -/
theorem varying_first_zero_minor_density {X : Type*} [TopologicalSpace X]
    {n : ℕ} (a : X → Fin n → ℝ) (x : X) (ha : ContinuousAt a x)
    (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, ∀ i, RatScalar (a y i))
    (hzero : ∀ y ∈ S, ∀ i, a x i = 0 → a y i = 0)
    (b : Fin n → ℝ) :
    (x, b) ∈ closure {z : X × (Fin n → ℝ) | z.1 ∈ S ∧
      (∀ i, RatScalar (z.2 i)) ∧ PreservesZeroMinors (pair (a x) b) (pair (a z.1) z.2)} := by
  let w := normalizeSecond (a x) b
  let T : Set (Fin n → ℝ) := {w' | (∀ i, RatScalar (w' i)) ∧
    PreservesZeroMinors (pair (normalPattern (a x)) w)
      (pair (normalPattern (a x)) w')}
  have hw : w ∈ closure T :=
    fixed_first_zero_minor_density _ _ (normalPattern_rational _)
  let F : X × (Fin n → ℝ) → X × (Fin n → ℝ) :=
    fun z => (z.1, restoreSecond (a x) (a z.1) z.2)
  have hF : ContinuousAt F (x, w) := by
    apply continuous_fst.continuousAt.prodMk
    apply continuousAt_pi.mpr
    intro i
    by_cases hi : a x i = 0
    · simpa only [restoreSecond, coordinateScale, if_pos hi, one_mul, Function.comp_def] using
        ((continuous_apply i).comp continuous_snd).continuousAt (x := (x, w))
    · simp only [restoreSecond, coordinateScale, if_neg hi]
      exact continuous_mul.continuousAt.comp
        (((continuous_apply i).continuousAt.comp
          (ha.comp continuous_fst.continuousAt)).prodMk
            ((continuous_apply i).continuousAt.comp continuous_snd.continuousAt))
  have hbase : F (x, w) = (x, b) := by
    exact congrArg (fun z => (x, z)) (restore_normalize (a x) b)
  have hprod : (x, w) ∈ closure (S ×ˢ T) := by
    rw [closure_prod_eq]
    exact ⟨hx, hw⟩
  have himage := mem_closure_image hF hprod
  rw [hbase] at himage
  apply closure_mono (s := F '' (S ×ˢ T)) ?_ himage
  rintro _ ⟨⟨y, w'⟩, ⟨hy, hw'⟩, rfl⟩
  refine ⟨hy, restoreSecond_rational _ _ _ (hRat y hy) hw'.1, ?_⟩
  intro s hs
  have hz := hw'.2 s (normalize_zero_minor (a x) b s hs)
  change minor (pair (a y) (restoreSecond (a x) (a y) w')) s = 0
  rw [minor_restore _ _ _ (hzero y hy) s, hz, mul_zero]

/-- Relative approximation of a pair of normals with all labelled
maximal-minor signs, retaining any independently approximated external
parameters. This is the varying-hyperplane flag lemma's algebraic core. -/
theorem varying_first_chirotope_density {X : Type*} [TopologicalSpace X]
    {n : ℕ} (a : X → Fin n → ℝ) (x : X) (ha : ContinuousAt a x)
    (S : Set X) (hx : x ∈ closure S)
    (hRat : ∀ y ∈ S, ∀ i, RatScalar (a y i))
    (hzero : ∀ y ∈ S, ∀ i, a x i = 0 → a y i = 0)
    (b : Fin n → ℝ) :
    (x, b) ∈ closure {z : X × (Fin n → ℝ) | z.1 ∈ S ∧
      (∀ i, RatScalar (z.2 i)) ∧ SameChirotope (pair (a x) b) (pair (a z.1) z.2)} := by
  have hcl := varying_first_zero_minor_density a x ha S hx hRat hzero b
  have hp : ContinuousAt (fun z : X × (Fin n → ℝ) => pair (a z.1) z.2) (x, b) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fin_cases j
    · exact (continuous_apply i).continuousAt.comp (ha.comp continuous_fst.continuousAt)
    · exact (continuous_apply i).continuousAt.comp continuous_snd.continuousAt
  have hopen := hp.tendsto.eventually (eventually_nonzero_minor_signs (pair (a x) b))
  have hi := mem_closure_inter_of_eventually hcl hopen
  apply closure_mono (s :=
    {z : X × (Fin n → ℝ) | z.1 ∈ S ∧ (∀ i, RatScalar (z.2 i)) ∧
      PreservesZeroMinors (pair (a x) b) (pair (a z.1) z.2)} ∩
    {z | ∀ s, minor (pair (a x) b) s ≠ 0 →
      SignType.sign (minor (pair (a z.1) z.2) s) = SignType.sign (minor (pair (a x) b) s)}) ?_ hi
  intro z hz
  refine ⟨hz.1.1, hz.1.2.1, ?_⟩
  intro s
  by_cases hs : minor (pair (a x) b) s = 0
  · rw [hz.1.2.2 s hs, hs]
  · exact hz.2 s hs

#print axioms varying_first_chirotope_density

end Papers.RationalityTen.FixedCoordinateFlagDensity
