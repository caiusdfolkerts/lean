module

public import PaperVerification.AlternatingFormsAmbientSectionFrames

/-!
# The actual ambient section equations in the structure-sheaf chart rings

The equations below are defined by evaluating the genuine sheaf morphism
on wedges of the genuine tautological frame.  Their ideal is identified
with the image of the original polynomial chart ideal under the actual
structure-sheaf chart isomorphism.  Thus the independent zero scheme's
local equations retain their intrinsic section-theoretic interpretation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory Opposite
open scoped Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

local instance (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) :
    CommRing ((Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf.obj.obj
      (op U)) :=
  inferInstanceAs (CommRing Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))

local instance (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens) :
    CommRing ((SheafOfModules.unit
      (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf).val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(Proj (isotropicProjectiveGrading (t := t) forms), U))

/-- The local frame as an actual basis of sections, on every subopen. -/
def tautologicalRowBasis (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) :
    Module.Basis (Fin (t + 2)) Γ(Proj (isotropicProjectiveGrading (t := t) forms), U)
      ((tautologicalKernel (t := t) forms).val.obj (op U)) :=
  (Pi.basisFun _ _).map (tautologicalFrameCoordinates p forms U hU).symm

@[simp] theorem tautologicalRowBasis_apply (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K)
    (U : (Proj (isotropicProjectiveGrading (t := t) forms)).Opens)
    (hU : U ≤ tautologicalChartOpen p forms) (i : Fin (t + 2)) :
    tautologicalRowBasis p forms U hU i = tautologicalRowSection p forms U hU i := by
  simp [tautologicalRowBasis, tautologicalRowSection, Pi.basisFun_apply]

/-- Evaluation of the original alternating form on two actual frame sections. -/
def ambientFrameWedgeValue (p : PluckerIndex (t + 2) n)
    (f : StrictPairs n → K) (i j : Fin (t + 2)) :
    Γ(Proj (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n))),
      tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :=
  (tautologicalAlternatingFunctional emptyAlternatingTuple f).val.app
    (op (tautologicalChartOpen p emptyAlternatingTuple))
      (((PresheafOfModules.sheafificationAdjunction
        (R := (Proj (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n)))).ringCatSheaf)
        (𝟙 _)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower 2).obj
            (tautologicalKernel (t := t) emptyAlternatingTuple).val)).app
              (op (tautologicalChartOpen p emptyAlternatingTuple))
                (ModuleCat.exteriorPower.mk
                  ![tautologicalRowSection p emptyAlternatingTuple _ le_rfl i,
                    tautologicalRowSection p emptyAlternatingTuple _ le_rfl j]))

/-- The intrinsic local equations are the actual frame-wedge evaluations. -/
def ambientIntrinsicChartIdeal (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal Γ(Proj (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n))),
      tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :=
  Ideal.span (Set.range fun a : Fin m × Fin (t + 2) × Fin (t + 2) ↦
    ambientFrameWedgeValue p (forms a.1) a.2.1 a.2.2)

theorem ambientFrameWedgeValue_eq (p : PluckerIndex (t + 2) n)
    (f : StrictPairs n → K) (i j : Fin (t + 2)) :
    ambientFrameWedgeValue p f i j =
      tautologicalChartPolynomialHom p emptyAlternatingTuple
        (alternatingRowPair f (pluckerChartMatrix p) i j) := by
  refine (tautologicalAlternatingFunctional_row_wedge p emptyAlternatingTuple f
    (tautologicalChartOpen p emptyAlternatingTuple) le_rfl i j).trans ?_
  change (Proj (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n)))).presheaf.map (𝟙 _)
    (tautologicalChartPolynomialHom p emptyAlternatingTuple
      (alternatingRowPair f (pluckerChartMatrix p) i j)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The actual local alternating functional, with the structure-sheaf
ring made explicit.  This is the same functional as the global section
restricted to the chart; no presentation or coefficient extension occurs. -/
def ambientFrameAlternatingForm (p : PluckerIndex (t + 2) n)
    (f : StrictPairs n → K) :
    AlternatingMap
      Γ(Proj (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n))),
        tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n)))
      ((tautologicalKernel (t := t)
        (emptyAlternatingTuple (K := K) (n := n))).val.obj
          (op (tautologicalChartOpen p emptyAlternatingTuple)))
      Γ(Proj (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n))),
        tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n)))
      (Fin 2) :=
  tautologicalLocalAlternatingForm emptyAlternatingTuple f
    (tautologicalChartOpen p emptyAlternatingTuple)

/-- The sheaf functional and the local exterior-power functional give the
same value on the actual frame. -/
theorem ambientFrameWedgeValue_eq_localForm (p : PluckerIndex (t + 2) n)
    (f : StrictPairs n → K) (i j : Fin (t + 2)) :
    ambientFrameWedgeValue p f i j =
      ambientFrameAlternatingForm p f
        ![tautologicalRowSection p emptyAlternatingTuple _ le_rfl i,
          tautologicalRowSection p emptyAlternatingTuple _ le_rfl j] := by
  exact (tautologicalAlternatingFunctional_wedge emptyAlternatingTuple f
    (tautologicalChartOpen p emptyAlternatingTuple)
    ![tautologicalRowSection p emptyAlternatingTuple _ le_rfl i,
      tautologicalRowSection p emptyAlternatingTuple _ le_rfl j]).trans
    (AlternatingSectionPresheaf.localForm_apply
      (R := (Proj (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n)))).sheaf.obj)
      (fun q : StrictPairs n ↦ q.val.1) (fun q : StrictPairs n ↦ q.val.2)
      (fun a ↦ (tautologicalCoordinateFunctional emptyAlternatingTuple a).val)
      (fun q ↦ tautologicalCoefficientSection emptyAlternatingTuple (f q))
      (op (tautologicalChartOpen p emptyAlternatingTuple))
      ![tautologicalRowSection p emptyAlternatingTuple _ le_rfl i,
        tautologicalRowSection p emptyAlternatingTuple _ le_rfl j]).symm

/-- Full images of the actual alternating functionals on the exterior
squares of the actual tautological sections of this affine chart. -/
def ambientLocalExteriorImageIdeal (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal Γ(Proj (isotropicProjectiveGrading (t := t)
        (emptyAlternatingTuple (K := K) (n := n))),
      tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :=
  ⨆ l : Fin m, LinearMap.range (exteriorPower.alternatingMapLinearEquiv
    (ambientFrameAlternatingForm p (forms l)))

/-- Basis evaluations generate the full image ideals of the actual local
exterior-square functionals, not merely their values at geometric points. -/
theorem ambientLocalExteriorImageIdeal_eq (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    ambientLocalExteriorImageIdeal p forms = ambientIntrinsicChartIdeal p forms := by
  have h (l : Fin m) : LinearMap.range (exteriorPower.alternatingMapLinearEquiv
      (ambientFrameAlternatingForm p (forms l))) =
      Ideal.span (Set.range fun ij : Fin (t + 2) × Fin (t + 2) ↦
        ambientFrameWedgeValue p (forms l) ij.1 ij.2) := by
    simpa only [tautologicalRowBasis_apply, ambientFrameWedgeValue_eq_localForm] using
      AlternatingSectionImageIdeal.range_exteriorFunctional_eq_basis_ideal
        (tautologicalRowBasis p emptyAlternatingTuple _ le_rfl)
        (ambientFrameAlternatingForm p (forms l))
  unfold ambientLocalExteriorImageIdeal
  simp only [h]
  apply le_antisymm
  · apply iSup_le
    intro l
    apply Ideal.span_le.mpr
    rintro z ⟨⟨i, j⟩, rfl⟩
    exact Ideal.subset_span ⟨(l, i, j), rfl⟩
  · apply Ideal.span_le.mpr
    rintro z ⟨⟨l, i, j⟩, rfl⟩
    exact Ideal.mem_iSup_of_mem l (Ideal.subset_span ⟨(i, j), rfl⟩)

/-- Equality of ideals in the actual structure-sheaf ring of each chart. -/
theorem ambientIntrinsicChartIdeal_eq_map (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    ambientIntrinsicChartIdeal p forms =
      (isotropicChartIdeal p forms).map
        (tautologicalChartPolynomialHom p emptyAlternatingTuple) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro z ⟨⟨l, i, j⟩, rfl⟩
    change ambientFrameWedgeValue p (forms l) i j ∈ _
    rw [ambientFrameWedgeValue_eq]
    exact Ideal.mem_map_of_mem _ (alternatingRowPair_mem_chartIdeal p forms l i j)
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro z ⟨⟨l, ij⟩, rfl⟩
    change tautologicalChartPolynomialHom p emptyAlternatingTuple
      (alternatingRowPair (forms l) (pluckerChartMatrix p) ij.val.1 ij.val.2) ∈
        ambientIntrinsicChartIdeal p forms
    rw [← ambientFrameWedgeValue_eq]
    exact Ideal.subset_span ⟨(l, ij.val.1, ij.val.2), rfl⟩

end PaperVerification.AlternatingForms
