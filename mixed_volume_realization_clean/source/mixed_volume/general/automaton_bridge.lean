module

public import mixed_volume.general.automaton_moments
public import mixed_volume.computability.prefix_pfa

/-! Exact transport of the seven-state rational prefix-correspondence compiler
into the automaton data used by the geometric construction. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace MixedVolume.AutomatonBridge

open AutomatonWords AutomatonMoments PrefixPFA Matrix MatrixMortality
open scoped BigOperators
variable {s : ℕ}

def automaton (upper lower : Fin s → List Bool) (u v : List Bool) : RationalData s 7 where
  P a := relabelMatrix (P upper lower u v a)
  P_nonneg a i j := (P_positive upper lower u v a (stateEquiv i) (stateEquiv j)).le
  P_sum a i := by
    rw [show (∑ j, relabelMatrix (P upper lower u v a) i j) =
      ∑ j, P upper lower u v a (stateEquiv i) j from stateEquiv.sum_comp (fun j => P upper lower u v a (stateEquiv i) j)]
    exact P_row_sum _ _ _ _ _ _
  f j := if j = 0 then 1 else 0
  f_nonneg j := by split_ifs <;> norm_num
  f_le_one j := by split_ifs <;> norm_num
  stationary _ := 1 / 7
  stationary_nonneg _ := by norm_num
  stationary_sum := by norm_num
  stationary_fixed a := by
    ext j
    change (∑ i, (1/7 : ℚ) * relabelMatrix (P upper lower u v a) i j) = 1/7
    rw [← Finset.mul_sum]
    have h : (∑ i, relabelMatrix (P upper lower u v a) i j) = 1 := by
      rw [show (∑ i, relabelMatrix (P upper lower u v a) i j) =
        ∑ i, P upper lower u v a i (stateEquiv j) from stateEquiv.sum_comp (fun i => P upper lower u v a i (stateEquiv j))]
      exact P_column_sum _ _ _ _ _ _
    rw [h,mul_one]

def initialQ (upper lower : Fin s → List Bool) (u v : List Bool) : Fin 7 → ℚ :=
  relabelRow (initial upper lower u v)

def initialReal (upper lower : Fin s → List Bool) (u v : List Bool) (j : Fin 7) : ℝ :=
  initialQ upper lower u v j

theorem initialReal_probability (upper lower : Fin s → List Bool) (u v : List Bool) :
    ProbabilityRow (initialReal upper lower u v) := by
  constructor
  · intro j
    change 0 ≤ (initial upper lower u v (stateEquiv j) : ℝ)
    exact_mod_cast initial_nonneg upper lower u v (stateEquiv j)
  · have h : (∑ j, initialQ upper lower u v j) = 1 := by
      rw [show (∑ j, initialQ upper lower u v j) = ∑ j, initial upper lower u v j from stateEquiv.sum_comp _]
      exact initial_sum _ _ _ _
    change (∑ j, (initialQ upper lower u v j : ℝ)) = 1
    exact_mod_cast h

theorem wordMatrix_cast (A : RationalData s 7) (w : Word s) (i j : Fin 7) :
    A.toReal.wordMatrix w i j = (wordProduct A.P w i j : ℚ) := by
  induction w generalizing i with
  | nil => simp only [Data.wordMatrix_nil,wordProduct_nil,Matrix.one_apply]; split <;> norm_num
  | cons a w ih =>
    rw [Data.wordMatrix_cons,wordProduct_cons,Matrix.mul_apply,Matrix.mul_apply]
    simp only [Rat.cast_sum,Rat.cast_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih]
    rfl

theorem acceptance_cast (upper lower : Fin s → List Bool) (u v : List Bool) (w : Word s) :
    (automaton upper lower u v).toReal.acceptance (initialReal upper lower u v) w =
      ((initial upper lower u v ᵥ* wordProduct (P upper lower u v) w) (some 0) : ℚ) := by
  rw [← relabel_acceptance upper lower u v w]
  unfold Data.acceptance Data.value
  rw [Matrix.dotProduct_mulVec]
  have hf : (automaton upper lower u v).toReal.f = Pi.single 0 (1 : ℝ) := by
    ext j
    simp only [automaton,RationalData.toReal,Pi.single_apply]
    split_ifs <;> norm_num
  rw [hf]
  simp only [dotProduct,Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  change (∑ j, initialReal upper lower u v j * (automaton upper lower u v).toReal.wordMatrix w j 0) =
    ((∑ j, initialQ upper lower u v j * wordProduct (fun a => relabelMatrix (P upper lower u v a)) w j 0 : ℚ) : ℝ)
  simp only [Rat.cast_sum,Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [wordMatrix_cast]
  rfl

theorem universal_iff_no_prefix_solution (upper lower : Fin s → List Bool) (u v : List Bool) :
    (automaton upper lower u v).toReal.UniversalCutpoint (initialReal upper lower u v) (1/7) ↔
      ¬ ∃ w : Word s, u ++ spell upper w = v ++ spell lower w := by
  change (∀ w : Word s, _ ≤ (1/7 : ℝ)) ↔ _
  simp only [not_exists,← acceptance_gt_cutpoint_iff upper lower u v,not_lt]
  apply forall_congr'
  intro w
  rw [acceptance_cast]
  have hcast : ((1/7 : ℚ) : ℝ) = 1/7 := by norm_num
  rw [← hcast,Rat.cast_le]

theorem prefix_halting_equivalence (index : Nat.Partrec.Code) :
    let q := MixedVolume.Computability.prefixReduction.emit index
    (automaton q.upper q.lower q.upperLeft q.lowerLeft).toReal.UniversalCutpoint
      (initialReal q.upper q.lower q.upperLeft q.lowerLeft) (1/7) ↔
      ¬ MatrixMortality.Undecidability.CodeHalts index := by
  dsimp
  rw [universal_iff_no_prefix_solution]
  have h := (MixedVolume.Computability.prefixReduction.target_iff_source index)
  obtain ⟨hu,hl,_⟩ := MixedVolume.Computability.prefixReduction_suffixes index
  change (∃ w, _ ++ spell _ w ++ _ = _ ++ spell _ w ++ _) ↔ _ at h
  simp only [hu,hl,List.append_nil] at h
  exact not_congr h

end MixedVolume.AutomatonBridge

end
