module
public import Papers.PlaneRationalDensity
public import Papers.ProjectiveRepresentatives
public import Mathlib.Basic.Sign.Defs

@[expose] public section

noncomputable section

open Matrix Set Filter Topology

namespace Papers.RationalityTen.PlaneRationalization

theorem rational_coefficients_dense :
    Dense {c : Fin 8 → ℝ | ∀ i, RatScalar (c i)} := by
  have h : DenseRange (fun c : Fin 8 → ℚ => fun i => (c i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  apply h.mono
  rintro _ ⟨c,rfl⟩ i
  exact ⟨c i,rfl⟩

noncomputable def expandRepresentatives {p : Fin 8 → V}
    (R : ProjectiveRepresentatives p) (q : Fin 8 → V) (c : Fin 8 → ℝ) :
    Fin 8 → V := fun i => if p i = 0 then 0 else c i • q (R.index i)

theorem expandRepresentatives_base {p : Fin 8 → V}
    (R : ProjectiveRepresentatives p) :
    expandRepresentatives R p R.coefficient = p := by
  classical
  ext i j
  by_cases hi : p i = 0
  · simp [expandRepresentatives,hi]
  · simpa [expandRepresentatives,hi] using congrFun (R.eq_smul i hi) j

theorem continuous_expandRepresentatives {p : Fin 8 → V}
    (R : ProjectiveRepresentatives p) :
    Continuous (fun z : (Fin 8 → V) × (Fin 8 → ℝ) =>
      expandRepresentatives R z.1 z.2) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : p i = 0
  · simp only [expandRepresentatives,if_pos hi]
    exact continuous_const
  · simp only [expandRepresentatives,if_neg hi]
    exact ((continuous_apply i).comp continuous_snd).smul
      ((continuous_apply (R.index i)).comp continuous_fst)

theorem triple_det_smul (a b c : ℝ) (x y z : V) :
    (Matrix.of ![a • x,b • y,c • z]).det =
      (a*b*c) * (Matrix.of ![x,y,z]).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,Pi.smul_apply,smul_eq_mul]
  ring

theorem expandRepresentatives_rational {p q : Fin 8 → V}
    (R : ProjectiveRepresentatives p) {c : Fin 8 → ℝ}
    (hq : RatConfiguration q) (hc : ∀ i, RatScalar (c i)) :
    RatConfiguration (expandRepresentatives R q c) := by
  classical
  intro i
  by_cases hi : p i = 0
  · simpa [expandRepresentatives,hi] using
      (show RatVector (0 : V) from fun _ => RatScalar.zero)
  · simpa [expandRepresentatives,hi] using RatVector.smul (hc i) (hq (R.index i))

theorem expandRepresentatives_tripleZeros {p q : Fin 8 → V}
    (R : ProjectiveRepresentatives p) (c : Fin 8 → ℝ)
    (hq : TripleZeros R.support p q) :
    TripleZeros Finset.univ p (expandRepresentatives R q c) := by
  classical
  intro i hi j hj k hk hdet
  by_cases hpi : p i = 0
  · simp [expandRepresentatives,hpi,Matrix.det_fin_three]
  by_cases hpj : p j = 0
  · simp [expandRepresentatives,hpj,Matrix.det_fin_three]
  by_cases hpk : p k = 0
  · simp [expandRepresentatives,hpk,Matrix.det_fin_three]
  have hrepdet : (Matrix.of ![p (R.index i),p (R.index j),p (R.index k)]).det = 0 := by
    rw [← R.eq_smul i hpi,← R.eq_smul j hpj,← R.eq_smul k hpk,
      triple_det_smul] at hdet
    exact (mul_eq_zero.mp hdet).resolve_left
      (mul_ne_zero (mul_ne_zero (R.coefficient_ne_zero i hpi)
        (R.coefficient_ne_zero j hpj)) (R.coefficient_ne_zero k hpk))
  have hqdet := hq (R.index i) (R.index_mem i hpi)
    (R.index j) (R.index_mem j hpj) (R.index k) (R.index_mem k hpk) hrepdet
  simp only [expandRepresentatives,if_neg hpi,if_neg hpj,if_neg hpk]
  rw [triple_det_smul,hqdet,mul_zero]

/-- This includes repeated projective points and zero vectors. -/
theorem rational_triple_zeros_dense (p : Fin 8 → V) :
    p ∈ closure {q | RatConfiguration q ∧ TripleZeros Finset.univ p q} := by
  obtain ⟨R⟩ := exists_projectiveRepresentatives p
  have hp : IndependentProjectivePoints R.support p := ⟨R.nonzero,R.independent⟩
  have hrec := rational_zero_configurations_dense R.support p hp
  have hprod : (p,R.coefficient) ∈ closure
      (RationalZeroConfigurations R.support p ×ˢ
        {c : Fin 8 → ℝ | ∀ i, RatScalar (c i)}) := by
    rw [closure_prod_eq]
    exact ⟨hrec,rational_coefficients_dense R.coefficient⟩
  let F := fun z : (Fin 8 → V) × (Fin 8 → ℝ) =>
    expandRepresentatives R z.1 z.2
  have hcl : p ∈ closure (F '' (RationalZeroConfigurations R.support p ×ˢ
      {c : Fin 8 → ℝ | ∀ i, RatScalar (c i)})) := by
    simpa only [F,expandRepresentatives_base] using
      mem_closure_image (continuous_expandRepresentatives R).continuousAt hprod
  apply closure_mono (s := F '' _) ?_ hcl
  rintro _ ⟨⟨q,c⟩,⟨hq,hc⟩,rfl⟩
  exact ⟨expandRepresentatives_rational R hq.1 hc,
    expandRepresentatives_tripleZeros R c hq.2.1⟩

def SameTripleSigns (p q : Fin 8 → V) : Prop :=
  ∀ i j k, SignType.sign ((Matrix.of ![q i,q j,q k]).det) =
    SignType.sign ((Matrix.of ![p i,p j,p k]).det)

theorem continuous_triple_det (i j k : Fin 8) :
    Continuous (fun q : Fin 8 → V => (Matrix.of ![q i,q j,q k]).det) := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  fun_prop

theorem eventually_sign_eq_of_nonzero {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {a : X} (hf : ContinuousAt f a) (ha : f a ≠ 0) :
    ∀ᶠ x in 𝓝 a, SignType.sign (f x) = SignType.sign (f a) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · filter_upwards [hf.tendsto.eventually (isOpen_Iio.mem_nhds hneg)] with x hx
    rw [sign_neg hx,sign_neg hneg]
  · filter_upwards [hf.tendsto.eventually (isOpen_Ioi.mem_nhds hpos)] with x hx
    rw [sign_pos hx,sign_pos hpos]

theorem eventually_nonzero_triple_signs (p : Fin 8 → V) :
    ∀ᶠ q in 𝓝 p, ∀ i j k, (Matrix.of ![p i,p j,p k]).det ≠ 0 →
      SignType.sign ((Matrix.of ![q i,q j,q k]).det) =
        SignType.sign ((Matrix.of ![p i,p j,p k]).det) := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  apply eventually_all.mpr
  intro k
  by_cases hdet : (Matrix.of ![p i,p j,p k]).det = 0
  · exact Eventually.of_forall fun _ h => (h hdet).elim
  · exact (eventually_sign_eq_of_nonzero (continuous_triple_det i j k).continuousAt hdet).mono
      fun _ h _ => h

/-- Equality of the complete rank-three chirotope, with every label and
every ordered minor retained. No assumption excludes zero or parallel labels. -/
theorem rational_triple_signs_dense (p : Fin 8 → V) :
    p ∈ closure {q | RatConfiguration q ∧ SameTripleSigns p q} := by
  have hcl := mem_closure_inter_of_eventually (rational_triple_zeros_dense p)
    (eventually_nonzero_triple_signs p)
  apply closure_mono (s := {q | RatConfiguration q ∧ TripleZeros Finset.univ p q} ∩
    {q | ∀ i j k, (Matrix.of ![p i,p j,p k]).det ≠ 0 →
      SignType.sign ((Matrix.of ![q i,q j,q k]).det) =
        SignType.sign ((Matrix.of ![p i,p j,p k]).det)}) ?_ hcl
  intro q hq
  refine ⟨hq.1.1,?_⟩
  intro i j k
  by_cases hdet : (Matrix.of ![p i,p j,p k]).det = 0
  · rw [hq.1.2 i (Finset.mem_univ _) j (Finset.mem_univ _)
      k (Finset.mem_univ _) hdet,hdet]
  · exact hq.2 i j k hdet

end Papers.RationalityTen.PlaneRationalization
