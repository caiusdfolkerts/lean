module

public import PaperVerification.AlternatingFormsOnePlaneSectionZero
public import PaperVerification.AlternatingFormsOddCharacteristicBoundary

/-!
# The genuine Richardson rank scheme in the one-plane boundary

For `s = 1`, the two opposite rank conditions have minor size one.  Their
actual equations are the ambient coordinates strictly before the lower
flag bound or strictly after the upper bound.  The printed odd-pencil
bounds make both collections empty, as proved below.  The resulting
scheme is the whole original one-row Plücker scheme in every
characteristic, with every integer twist preserved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K]

/-- The literal one-by-one rank equations prescribed by the two flags. -/
def onePlaneFlagEquationIndex (k : ℕ) :=
  Σ j : Fin 1, {c : Fin (2 * k + 1) //
    c < oddIntervalLower k 1 (by omega) j ∨ oddIntervalUpper k 1 (by omega) j < c}

instance onePlaneFlagEquationIndex_isEmpty (k : ℕ) :
    IsEmpty (onePlaneFlagEquationIndex k) := by
  constructor
  rintro ⟨j, c, hc⟩
  have hj := j.isLt
  have hc' := c.isLt
  rcases hc with hc | hc
  · change c.val < 2 * j.val at hc
    omega
  · change 2 * (k + 1 - 1 + j.val) < c.val at hc
    omega

local instance (k : ℕ) (U : (onePlaneAmbient (K := K) (2 * k + 1)).Opens) :
    CommRing ((onePlaneAmbient (K := K) (2 * k + 1)).ringCatSheaf.obj.obj (op U)) :=
  inferInstanceAs (CommRing Γ(onePlaneAmbient (K := K) (2 * k + 1), U))

local instance (k : ℕ) (U : (onePlaneAmbient (K := K) (2 * k + 1)).Opens) :
    CommRing ((SheafOfModules.unit
      (onePlaneAmbient (K := K) (2 * k + 1)).ringCatSheaf).val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(onePlaneAmbient (K := K) (2 * k + 1), U))

/-- The affine image ideals of the actual rank-one coordinate maps. -/
def onePlaneRichardsonAffineIdeal (k : ℕ)
    (U : (onePlaneAmbient (K := K) (2 * k + 1)).affineOpens) :
    Ideal Γ(onePlaneAmbient (K := K) (2 * k + 1), U) :=
  ⨆ i : onePlaneFlagEquationIndex k,
    LinearMap.range ((onePlaneTautologicalCoordinate (2 * k + 1) i.2.val).val.app
      (op U.1)).hom

theorem onePlaneRichardsonAffineIdeal_eq_bot (k : ℕ)
    (U : (onePlaneAmbient (K := K) (2 * k + 1)).affineOpens) :
    onePlaneRichardsonAffineIdeal k U = ⊥ := by
  simp [onePlaneRichardsonAffineIdeal]

/-- The independent ideal sheaf from the actual one-plane flag projections. -/
def onePlaneRichardsonZeroIdeal (k : ℕ) :
    (onePlaneAmbient (K := K) (2 * k + 1)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (onePlaneRichardsonAffineIdeal k)

theorem onePlaneRichardsonZeroIdeal_eq_bot (k : ℕ) :
    onePlaneRichardsonZeroIdeal (K := K) k = ⊥ := by
  apply le_antisymm _ bot_le
  intro U
  exact (Scheme.IdealSheafData.ideal_ofIdeals_le (onePlaneRichardsonAffineIdeal k) U).trans
    (le_of_eq (onePlaneRichardsonAffineIdeal_eq_bot k U))

theorem onePlaneRichardsonZeroIdeal_ideal (k : ℕ)
    (U : (onePlaneAmbient (K := K) (2 * k + 1)).affineOpens) :
    (onePlaneRichardsonZeroIdeal k).ideal U = onePlaneRichardsonAffineIdeal k U := by
  rw [onePlaneRichardsonZeroIdeal_eq_bot, onePlaneRichardsonAffineIdeal_eq_bot]
  rfl

/-- The actual rank-condition scheme is the original projective scheme. -/
def onePlaneRichardsonZeroIso (k : ℕ) :
    (onePlaneRichardsonZeroIdeal (K := K) k).subscheme ≅
      onePlaneAmbient (K := K) (2 * k + 1) := by
  letI : IsIso (onePlaneRichardsonZeroIdeal (K := K) k).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).mpr (onePlaneRichardsonZeroIdeal_eq_bot k)
  exact asIso (onePlaneRichardsonZeroIdeal (K := K) k).subschemeι

/-- The interval-coordinate quotient identifies with the actual original
one-row Plücker ring using the proved equality of the literal ideals. -/
def onePlaneRichardsonRingEquiv (k : ℕ) :
    (MvPolynomial (PluckerIndex 1 (2 * k + 1)) K ⧸
      intervalPluckerIdeal (oddIntervalLower k 1 (by omega))
        (oddIntervalUpper k 1 (by omega))) ≃ₐ[K]
      (MvPolynomial (PluckerIndex 1 (2 * k + 1)) K ⧸ matrixPluckerIdeal) :=
  Ideal.quotientEquivAlgOfEq K (odd_onePlane_interval_eq_matrix k)

/-- The comparison retains every original polynomial, hence every
homogeneous degree and every original Plücker coordinate. -/
theorem onePlaneRichardsonRingEquiv_mk (k : ℕ)
    (a : MvPolynomial (PluckerIndex 1 (2 * k + 1)) K) :
    onePlaneRichardsonRingEquiv k (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk matrixPluckerIdeal a :=
  Ideal.quotientEquivAlgOfEq_mk K (odd_onePlane_interval_eq_matrix k) a

/-- Every integer Plücker twist on the independent rank-condition scheme. -/
def onePlaneRichardsonTwist (k : ℕ) (r : ℤ) :
    (onePlaneRichardsonZeroIdeal (K := K) k).subscheme.Modules :=
  (Scheme.Modules.pullback (onePlaneRichardsonZeroIdeal k).subschemeι).obj
    (Proj.twistingSheaf (onePlaneAmbientGrading (K := K) (2 * k + 1)) r)

/-- The boundary comparison preserves the polarization and all its twists. -/
def onePlaneRichardsonTwistingIso (k : ℕ) (r : ℤ) :
    (Scheme.Modules.pullback (onePlaneRichardsonZeroIso (K := K) k).inv).obj
        (onePlaneRichardsonTwist k r) ≅
      Proj.twistingSheaf (onePlaneAmbientGrading (K := K) (2 * k + 1)) r :=
  (Scheme.Modules.pullbackComp (onePlaneRichardsonZeroIso k).inv
    (onePlaneRichardsonZeroIdeal k).subschemeι).app _ ≪≫
    eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
      (Proj.twistingSheaf (onePlaneAmbientGrading (K := K) (2 * k + 1)) r))
      (onePlaneRichardsonZeroIso k).inv_hom_id) ≪≫
    (Scheme.Modules.pullbackId (onePlaneAmbient (K := K) (2 * k + 1))).app _

end PaperVerification.AlternatingForms
