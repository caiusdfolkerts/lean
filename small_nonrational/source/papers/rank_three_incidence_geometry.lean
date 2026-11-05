module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Configuration
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

/-!
# Real projective incidence geometry for small configurations

Points and lines are represented by actual nonzero three-vectors. Incidence is
the vanishing dot product. The uniqueness of a line through two independent
points is inherited from Mathlib's proved projective-plane construction.
The determinant lemmas below connect finite incidence witnesses to genuine
nonzero frame minors.
-/

namespace Papers.RationalityTen

abbrev PlaneVector := Fin 3 → ℝ

def dotFunctional (l : PlaneVector) : PlaneVector →ₗ[ℝ] ℝ where
  toFun x := dotProduct l x
  map_add' := fun x y => dotProduct_add l x y
  map_smul' := fun c x => dotProduct_smul c l x

/-- Two distinct projective lines cannot contain two distinct projective
points. Both distinctness hypotheses are stated as literal independence. -/
theorem independent_incidence_pair_impossible
    (l m x y : PlaneVector)
    (hlm : LinearIndependent ℝ ![l, m])
    (hxy : LinearIndependent ℝ ![x, y])
    (hlx : dotProduct l x = 0) (hly : dotProduct l y = 0)
    (hmx : dotProduct m x = 0) (hmy : dotProduct m y = 0) : False := by
  have hlm' : crossProduct l m ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hlm
  have hxy' : crossProduct x y ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hxy
  exact (Configuration.ofField.crossProduct_eq_zero_of_dotProduct_eq_zero
    hlx hmx hly hmy).elim hlm' hxy'

/-- Two distinct joining lines certify a noncollinear point triple. This
supplies the nonzero frame minors required by the Fano and MacLane
normalizations; they are not added as genericity assumptions. -/
theorem three_points_independent_of_joining_lines
    (x y z l m : PlaneVector)
    (hxy : LinearIndependent ℝ ![x, y])
    (hxz : LinearIndependent ℝ ![x, z])
    (hlm : LinearIndependent ℝ ![l, m])
    (hlx : dotProduct l x = 0) (hly : dotProduct l y = 0)
    (hmx : dotProduct m x = 0) (hmz : dotProduct m z = 0) :
    LinearIndependent ℝ ![x, y, z] := by
  have hz : z ∉ Submodule.span ℝ (Set.range ![x, y]) := by
    intro hz
    have hspan : Submodule.span ℝ (Set.range ![x, y]) ≤
        (dotFunctional l).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hlx
      · exact hly
    have hlz : dotProduct l z = 0 := hspan hz
    exact independent_incidence_pair_impossible l m x z hlm hxz hlx hlz hmx hmz
  have hsnoc : Fin.snoc ![x, y] z = ![x, y, z] := by
    ext i
    fin_cases i <;> rfl
  simpa only [hsnoc] using hxy.finSnoc hz

theorem triple_det_ne_zero_of_joining_lines
    (x y z l m : PlaneVector)
    (hxy : LinearIndependent ℝ ![x, y])
    (hxz : LinearIndependent ℝ ![x, z])
    (hlm : LinearIndependent ℝ ![l, m])
    (hlx : dotProduct l x = 0) (hly : dotProduct l y = 0)
    (hmx : dotProduct m x = 0) (hmz : dotProduct m z = 0) :
    (Matrix.of ![x, y, z]).det ≠ 0 := by
  have hLI := three_points_independent_of_joining_lines
    x y z l m hxy hxz hlm hlx hly hmx hmz
  have hunit : IsUnit (Matrix.of ![x, y, z]) :=
    Matrix.linearIndependent_row_iff_isUnit.mp hLI
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

theorem determinant_zero_of_annihilator {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℝ) (l : κ → ℝ) (hl : l ≠ 0)
    (hA : A.mulVec l = 0) : A.det = 0 := by
  by_contra hdet
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))
  have heq : l = 0 := hinj (by simpa using hA)
  exact hl heq

/-- Incidence with a genuine nonzero line forces the corresponding actual
three-by-three point determinant to vanish. -/
theorem triple_det_zero_of_incident_line
    (x y z l : PlaneVector) (hl : l ≠ 0)
    (hlx : dotProduct l x = 0) (hly : dotProduct l y = 0)
    (hlz : dotProduct l z = 0) :
    (Matrix.of ![x, y, z]).det = 0 := by
  apply determinant_zero_of_annihilator (Matrix.of ![x, y, z]) l hl
  ext i
  fin_cases i
  · simpa [Matrix.mulVec, dotProduct_comm] using hlx
  · simpa [Matrix.mulVec, dotProduct_comm] using hly
  · simpa [Matrix.mulVec, dotProduct_comm] using hlz

theorem triple_det_cycle (x y z : PlaneVector) :
    (Matrix.of ![x,y,z]).det = (Matrix.of ![y,z,x]).det := by
  simp [Matrix.det_fin_three] <;> ring


end Papers.RationalityTen
