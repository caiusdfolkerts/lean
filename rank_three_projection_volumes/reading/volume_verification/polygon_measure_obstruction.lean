module
public import VolumeVerification.EdgeMoments
@[expose] public section
set_option autoImplicit false

/-!
# The polygonal positive-measure obstruction

This is the exact measure-and-linear-algebra conclusion of Proposition 4.2.
Every endpoint weight and moment matrix is defined by an actual integral.
The hypotheses on the measures are the identities obtained from mixed volumes,
the finite cone decomposition, and equality rigidity.
-/
namespace VolumeVerification.PolygonMeasureObstruction
open scoped BigOperators ENNReal Matrix
open MeasureTheory Set
open EdgeMoments
variable {n : ℕ}
variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

private theorem sum_two (f : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b)
    (hzero : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i, f i = f a + f b := by
  classical
  have he : ∀ i, f i =
      (if i = a then f a else 0) + (if i = b then f b else 0) := by
    intro i
    by_cases ha : i = a
    · subst i; simp [hab]
    by_cases hb : i = b
    · subst i; simp [Ne.symm hab]
    · simp [ha,hb,hzero i ha hb]
  calc
    (∑ i, f i) =
        ∑ i, ((if i = a then f a else 0) + (if i = b then f b else 0)) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = f a + f b := by simp [Finset.sum_add_distrib]

theorem linear_relation_coordinate
    (Z : Matrix (Fin n) (Fin n) ℝ) (φ : Ω → Fin n → ℝ)
    (w : Fin n → ℝ) (hw : Zᵀ *ᵥ w = 0) (x : Ω) :
    ∑ i, w i * coordinate Z φ i x = 0 := by
  change w ⬝ᵥ (Z *ᵥ φ x) = 0
  rw [← Matrix.dotProduct_transpose_mulVec Z (φ x) w, hw]
  simp

noncomputable def moments (ν : Fin n → Measure Ω) (φ : Ω → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i e => ∫ x, φ x i ∂ν e

noncomputable def alpha (ν : Fin n → Measure Ω)
    (Z : Matrix (Fin n) (Fin n) ℝ) (φ : Ω → Fin n → ℝ) (e : Fin n) : ℝ :=
  ∫ x, |coordinate Z φ e x| ∂ν e

noncomputable def beta (ν : Fin n → Measure Ω)
    (Z : Matrix (Fin n) (Fin n) ℝ) (φ : Ω → Fin n → ℝ) (e : Fin n) : ℝ :=
  ∫ x, |coordinate Z φ (next e) x| ∂ν e

variable (hn : 5 ≤ n)
  (μ ν : Fin n → Measure Ω)
  [∀ i, IsFiniteMeasure (μ i)] [∀ e, IsFiniteMeasure (ν e)]
  (r : Fin n → Fin n → ℝ) (hr : RayPattern r)
  (hdecomp : ∀ i, μ i = ∑ e, ENNReal.ofReal (r e i) • ν e)
  (P Z : Matrix (Fin n) (Fin n) ℝ)
  (φ : Ω → Fin n → ℝ) (hφ : Continuous φ)
  (hdiag : ∀ i, P i i = 0)
  (hpos : ∀ i j, i ≠ j → 0 < P i j)
  (hpair : ∀ i j, P i j = ∫ x, |coordinate Z φ j x| ∂μ i)
  (hcenter : ∀ i j, ∫ x, φ x j ∂μ i = 0)

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem endpoint_alpha_positive : ∀ e, 0 < alpha ν Z φ e := by
  intro e
  exact (outgoing_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
    (by omega) hr hdecomp e).2

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem endpoint_beta_positive : ∀ e, 0 < beta ν Z φ e := by
  intro e
  simpa [beta] using
    (incoming_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
      (by omega) hr hdecomp (next e)).2

include hr hdecomp hφ hdiag hpair in
theorem coordinate_zero_ae_all (e : Fin n) :
    ∀ᵐ x ∂ν e, ∀ i, i ≠ e → i ≠ next e → coordinate Z φ i x = 0 := by
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i = e
  · exact Filter.Eventually.of_forall fun x h => False.elim (h hi)
  by_cases hin : i = next e
  · exact Filter.Eventually.of_forall fun x _ h => False.elim (h hin)
  exact (coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp e i hi hin).mono
    (fun x hx _ _ => hx)

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem relation_zero_propagation :
    ∀ w, Zᵀ *ᵥ w = 0 → ∀ e, w e = 0 → w (finRotate n e) = 0 := by
  intro w hw e he
  by_contra hne
  have hz : coordinate Z φ (next e) =ᵐ[ν e] 0 := by
    filter_upwards [coordinate_zero_ae_all μ ν r hr hdecomp P Z φ hφ hdiag hpair e]
      with x hx
    have hsum : (∑ i, w i * coordinate Z φ i x) =
        w (next e) * coordinate Z φ (next e) x := by
      apply Finset.sum_eq_single (next e)
      · intro i _ hin
        by_cases hie : i = e
        · subst i; rw [he,zero_mul]
        · rw [hx i hie hin,mul_zero]
      · simp
    have hmul : w (next e) * coordinate Z φ (next e) x = 0 := by
      rw [← hsum]
      exact linear_relation_coordinate Z φ w hw x
    exact (mul_eq_zero.mp hmul).resolve_left hne
  have hβ : beta ν Z φ e = 0 := by
    apply integral_eq_zero_of_ae
    exact hz.mono fun x hx => by simp [hx]
  have hposβ := endpoint_beta_positive hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter e
  linarith

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
theorem moment_matrix_kernel : Z * moments ν φ = 0 := by
  ext i e
  change (∑ j, Z i j * ∫ x, φ x j ∂ν e) = 0
  rw [← integral_coordinate (ν e) Z φ hφ i]
  by_cases hi : i = e
  · subst i
    exact (outgoing_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
      (by omega) hr hdecomp e).1
  by_cases hin : i = next e
  · rw [hin]
    simpa using (incoming_moments μ ν r P Z φ hφ hdiag hpos hpair hcenter
      (by omega) hr hdecomp (next e)).1
  exact integral_eq_zero_of_ae
    (coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair hr hdecomp e i hi hin)

theorem cycleIncidence_mul_apply (W : Matrix (Fin (n-3)) (Fin n) ℝ)
    (a b : Fin n → ℝ) (k : Fin (n-3)) (e : Fin n) :
    (W * CycleObstruction.cycleIncidence a b) k e =
      W k e * a e + W k (next e) * b e := by
  simp [Matrix.mul_apply, CycleObstruction.cycleIncidence, next,
    mul_add, mul_ite, Finset.sum_add_distrib]

include hn hr hdecomp hφ hdiag hpair in
theorem moment_factorization
    (W L : Matrix (Fin (n-3)) (Fin n) ℝ)
    (hrigidity : ∀ i, ∀ᵐ x ∂μ i,
      W *ᵥ (fun j => |coordinate Z φ j x|) = L *ᵥ φ x) :
    W * CycleObstruction.cycleIncidence (alpha ν Z φ) (beta ν Z φ) =
      L * moments ν φ := by
  ext k e
  have hc : prev e ≠ e := prev_ne (by omega) e
  have hcn : prev e ≠ next e := prev_ne_next (by omega) e
  have hrig : ∀ᵐ x ∂ν e,
      W *ᵥ (fun j => |coordinate Z φ j x|) = L *ᵥ φ x :=
    transfer_ae μ ν r hr hdecomp e (prev e) hc hcn (hrigidity (prev e))
  have hint := integral_congr_ae (hrig.mono fun x hx => congrFun hx k)
  have hleft :
      (∫ x, (W *ᵥ (fun j => |coordinate Z φ j x|)) k ∂ν e) =
        W k e * alpha ν Z φ e + W k (next e) * beta ν Z φ e := by
    have hi : ∀ i, Integrable (fun x => W k i * |coordinate Z φ i x|) (ν e) := by
      intro i
      exact (continuous_integrable (ν e) _
        (coordinate_continuous Z φ hφ i).abs).const_mul _
    simp only [Matrix.mulVec, dotProduct]
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    simp only [integral_const_mul]
    apply sum_two _ e (next e) (Ne.symm (next_ne (by omega) e))
    intro i hi hin
    have hz := coordinate_zero_off_edge μ ν r P Z φ hφ hdiag hpair
      hr hdecomp e i hi hin
    have hi0 : (∫ x, |coordinate Z φ i x| ∂ν e) = 0 :=
      integral_eq_zero_of_ae (hz.mono fun x hx => by simp [hx])
    rw [hi0,mul_zero]
  have hright :
      (∫ x, (L *ᵥ φ x) k ∂ν e) = (L * moments ν φ) k e := by
    exact integral_matrix_row (ν e) L φ hφ k
  rw [hleft,hright] at hint
  rw [cycleIncidence_mul_apply]
  exact hint

include hn hr hdecomp hφ hdiag hpos hpair hcenter in
/-- No data satisfying the original measure identities and the polygonal
ray pattern can exist in any dimension n >= 5. -/
theorem impossible_positive_polygon_measure_data
    (W : Matrix (Fin (n-3)) (Fin n) ℝ) (hW : W.rank = n-3)
    (L : Matrix (Fin (n-3)) (Fin n) ℝ)
    (hrigidity : ∀ i, ∀ᵐ x ∂μ i,
      W *ᵥ (fun j => |coordinate Z φ j x|) = L *ᵥ φ x) :
    False := by
  letI : NeZero n := ⟨by omega⟩
  exact CycleObstruction.no_cycle_factorization hn W hW Z
    (relation_zero_propagation hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    (alpha ν Z φ) (beta ν Z φ)
    (endpoint_alpha_positive hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    (endpoint_beta_positive hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    L (moments ν φ)
    (moment_matrix_kernel hn μ ν r hr hdecomp P Z φ hφ hdiag hpos hpair hcenter)
    (moment_factorization hn μ ν r hr hdecomp P Z φ hφ hdiag hpair W L hrigidity)

end VolumeVerification.PolygonMeasureObstruction

