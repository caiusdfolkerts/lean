module

public import PaperVerification.AlternatingFormsOrbitDifference

/-!
# The mixed block of the odd pencil differential

The reconstruction solves every mixed output by the surjective diagonal-difference
map and then writes the large diagonal block row by row.
-/

@[expose] public section
noncomputable section

namespace PaperVerification.AlternatingForms

open Matrix

variable {K : Type*} [Field K]

/-- Mixed blocks of (HᵀF+FH,HᵀG+GH) for the two rectangular incidence matrices. -/
def orbitCrossMap (t : ℕ)
    (PS : Matrix (Fin (t + 1)) (Fin (t + 1)) K ×
      Matrix (Fin (t + 2)) (Fin (t + 2)) K) :
    Matrix (Fin (t + 1)) (Fin (t + 2)) K ×
      Matrix (Fin (t + 1)) (Fin (t + 2)) K :=
  (fun i j ↦ orbitSquarePad PS.1 j.val i.val + PS.2 i.succ j,
   fun i j ↦ orbitSquarePad PS.1 (j.val + 1) i.val + PS.2 i.castSucc j)

theorem orbitCrossMap_surjective (t : ℕ) :
    Function.Surjective (orbitCrossMap (K := K) t) := by
  rintro ⟨C, D⟩
  let B : Matrix (Fin t) (Fin (t + 2)) K :=
    fun i j ↦ D i.succ j - C i.castSucc j
  obtain ⟨P, hP⟩ := orbitDifference_surjective (K := K) t B
  let S : Matrix (Fin (t + 2)) (Fin (t + 2)) K :=
    fun i j ↦ Fin.cases
      (D 0 j - orbitSquarePad P (j.val + 1) 0)
      (fun a ↦ C a j - orbitSquarePad P j.val a.val) i
  refine ⟨(P, S), ?_⟩
  apply Prod.ext
  · ext i j
    simp only [orbitCrossMap, S, Fin.cases_succ]
    ring
  · ext i j
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · simp only [orbitCrossMap, S, Fin.castSucc_zero, Fin.cases_zero, Fin.val_zero]
      ring
    · have h := congrFun (congrFun hP a) j
      change orbitSquarePad P (j.val + 1) (a.val + 1) -
          orbitSquarePad P j.val a.val = D a.succ j - C a.castSucc j at h
      change orbitSquarePad P (j.val + 1) (a.val + 1) +
        S a.succ.castSucc j = D a.succ j
      have hs : S a.succ.castSucc j = C a.castSucc j -
          orbitSquarePad P j.val a.val := by
        have hi : a.succ.castSucc = a.castSucc.succ := by
          apply Fin.ext
          rfl
        simp only [S, hi, Fin.cases_succ, Fin.val_castSucc]
      rw [hs]
      calc
        orbitSquarePad P (j.val + 1) (a.val + 1) +
            (C a.castSucc j - orbitSquarePad P j.val a.val) =
          (orbitSquarePad P (j.val + 1) (a.val + 1) -
            orbitSquarePad P j.val a.val) + C a.castSucc j := by ring
        _ = D a.succ j := by rw [h, sub_add_cancel]

end PaperVerification.AlternatingForms
