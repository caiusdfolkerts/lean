module

public import Papers.GraphicalZonotopes.PairRelabelling
public import Papers.GraphicalZonotopes.FloorPhase
public import Papers.GraphicalZonotopes.CompleteBooleanPhase

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset BooleanFourier
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem character_univ_parity (s : Cube I) :
    character univ s=QuadraticSign.parity (trueSet s).card := by
  rw [character_univ]
  have hf : ∀ i : I,spin (s i)=if i∈trueSet s then (-1 : ℝ) else 1 := by
    intro i
    cases hs : s i <;> simp [spin,trueSet,hs]
  simp_rw [hf]
  rw [prod_ite_mem_eq]
  simp [QuadraticSign.parity]

theorem trueSet_xor (s t : Cube I) :
    trueSet (fun i => Bool.xor (s i) (t i))=trueSet s∆trueSet t := by
  ext i
  cases hs : s i <;> cases ht : t i <;> simp [trueSet,Finset.mem_symmDiff,hs,ht]

@[simp] theorem firstSet_subsetOfBits (s : Cube I × Cube I) :
    firstSet (subsetOfBits s)=trueSet s.1 := by
  ext i
  simp [trueSet]

@[simp] theorem secondSet_subsetOfBits (s : Cube I × Cube I) :
    secondSet (subsetOfBits s)=trueSet s.2 := by
  ext i
  simp [trueSet]

theorem transformed_firstSet (uv : Cube I × Cube I) :
    firstSet (subsetOfBits (coordinateChange.symm uv))=trueSet uv.1 := by
  rw [firstSet_subsetOfBits]
  rfl

theorem transformed_secondSet (uv : Cube I × Cube I) :
    secondSet (subsetOfBits (coordinateChange.symm uv))=trueSet uv.1∆trueSet uv.2 := by
  rw [secondSet_subsetOfBits]
  exact trueSet_xor uv.1 uv.2

theorem integerData_transformed_phase (uv : Cube I × Cube I) :
    (-1 : ℝ)^integerData (subsetOfBits (coordinateChange.symm uv))=
      phase (completePhase 1 ∅) uv := by
  rw [integerData_phase,transformed_firstSet,transformed_secondSet,
    symmDiff_symmDiff_cancel_left,← character_univ_parity]
  simp [phase,completePhase,QuadraticSign.complete,QuadraticSign.triangle,
    QuadraticSign.parity]

theorem transformed_card_phase (uv : Cube I × Cube I) :
    (-1 : ℝ)^((subsetOfBits (coordinateChange.symm uv)).card)=character univ uv.2 := by
  change QuadraticSign.parity _=_
  rw [card_eq_first_add_second,transformed_firstSet,transformed_secondSet,
    QuadraticSign.parity_add,QuadraticSign.parity_card_symmDiff,
    ← mul_assoc,QuadraticSign.parity_square,one_mul,character_univ_parity]

/-- The complete quadratic phase occurring in an original edge row. Its
linear part depends only on whether the endpoint sides agree. -/
def rowPhase (u v : I×Fin 2) : Cube (Remaining u v) → ℝ :=
  completePhase (if u.2=1 ∧ v.2=1 then -1 else 1)
    (if u.2=v.2 then univ else ∅)

theorem rowPhase_isSign (u v : I×Fin 2) (x : Cube (Remaining u v)) :
    rowPhase u v x=1 ∨ rowPhase u v x= -1 := by
  apply completePhase_isSign
  split_ifs <;> simp

theorem rowPhase_nonseparable (u v : I×Fin 2) : Nonseparable (rowPhase u v) := by
  apply completePhase_nonseparable
  split_ifs <;> norm_num

theorem setFunction_edgeContext_rounded {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (s : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta setFunction u v (edgeContext u v s)=
      (1+(if firstWeight u=firstWeight v then
          if firstWeight u=1 then
            (-1 : ℝ)^(integerData (edgeContext u v s)+(edgeContext u v s).card)
          else -(-1 : ℝ)^(integerData (edgeContext u v s)+(edgeContext u v s).card)
        else (-1 : ℝ)^integerData (edgeContext u v s)))/2 := by
  let S := edgeContext u v s
  have hmu := integerData_insert_common u S (left_not_mem_edgeContext _ _ _)
    (fun w hw => (edgeContext_all_adj u v s w hw).1)
  have hmv := integerData_insert_common v S (right_not_mem_edgeContext _ _ _)
    (fun w hw => (edgeContext_all_adj u v s w hw).2)
  have hd := integerData_mixed ((graph I).ne_of_adj huv)
    (left_not_mem_edgeContext u v s) (right_not_mem_edgeContext u v s)
  rw [if_pos huv] at hd
  have hmuv : integerData (insert u (insert v S))=
      integerData S+2*(S.card : ℤ)+firstWeight u+firstWeight v+1 := by
    change integerData (insert u (insert v S))+integerData S-
      integerData (insert u S)-integerData (insert v S)=1 at hd
    omega
  rw [delta_setFunction]
  change ((integerData (insert u (insert v S))/2+integerData S/2-
    integerData (insert u S)/2-integerData (insert v S)/2 : ℤ) : ℝ)=_
  rw [hmuv,hmu,hmv]
  push_cast
  exact FloorHalf.rounded_edge_phase _ _ _ _ (firstWeight_isBit u) (firstWeight_isBit v)

/-- The original elemental difference is exactly the Boolean tensor face
function after an explicitly invertible change of all remaining bits. -/
theorem setFunction_edgeProfile {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (uv : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta setFunction u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction (rowPhase u v) uv := by
  rw [setFunction_edgeContext_rounded huv,integerData_edgeContext,edgeContext_card,
    zpow_add₀ (by norm_num),zpow_natCast,integerData_transformed_phase,transformed_card_phase]
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  fin_cases a <;> fin_cases b <;>
    simp [firstWeight,rowPhase,faceFunction,phase,completePhase] <;> ring

theorem complementFunction_edgeProfile {u v : I×Fin 2} (huv : (graph I).Adj u v)
    (uv : Cube (Remaining u v) × Cube (Remaining u v)) :
    delta complementFunction u v (edgeContext u v (coordinateChange.symm uv))=
      faceFunction (-rowPhase u v) uv := by
  rw [complementFunction,delta_sub,graphFunction_delta _ ((graph I).ne_of_adj huv)
    (left_not_mem_edgeContext _ _ _) (right_not_mem_edgeContext _ _ _),if_pos huv,
    setFunction_edgeProfile huv]
  simp only [faceFunction,phase,Pi.neg_apply]
  ring

end DoubledParts
end GraphicalZonotopes
