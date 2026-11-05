module

public import paper_verification.ambient_intrinsic5
import all paper_verification.ambient_intrinsic5
public import paper_verification.ambient_polarization2
import all paper_verification.ambient_polarization2
public import paper_verification.richardson_chart6
import all paper_verification.richardson_chart6
public import paper_verification.schubert_rank3
import all paper_verification.schubert_rank3
public import paper_verification.literal000
import all paper_verification.literal000
public import paper_verification.ambient_zero6
import all paper_verification.ambient_zero6
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

section ComponentSource_0
/- Original module: PaperVerification.AlternatingFormsIntrinsicChartIdeal -/


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
end
end
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsIntrinsicChartIdeal"

section ComponentSource_1
/- Original module: PaperVerification.AlternatingFormsIntrinsicZeroScheme -/


/-!
# The intrinsic tautological zero scheme with every Plücker twist

This definition starts from the full image ideals of the alternating
functionals on the actual tautological sections of every ambient chart.
Only after constructing that zero scheme do we compare its ideals with
the original homogeneous quotient and prove the polarized isomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

/-- The full actual local image ideal, expressed in polynomial chart coordinates. -/
def ambientIntrinsicPolynomialIdeal (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  (ambientLocalExteriorImageIdeal p forms).comap
    (tautologicalChartPolynomialHom p emptyAlternatingTuple)

theorem ambientIntrinsicPolynomialIdeal_eq (p : PluckerIndex (t + 2) n)
    (forms : Fin m → StrictPairs n → K) :
    ambientIntrinsicPolynomialIdeal p forms = isotropicChartIdeal p forms := by
  rw [ambientIntrinsicPolynomialIdeal, ambientLocalExteriorImageIdeal_eq,
    ambientIntrinsicChartIdeal_eq_map,
    Ideal.comap_map_of_surjective _ (ambientChartPolynomialHom_bijective (K := K) p).surjective,
    ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (ambientChartPolynomialHom_bijective (K := K) p).injective,
    sup_bot_eq]

def intrinsicChartImageIdeal (p : PluckerIndex (t + 2) n)
    (I : Ideal (MvPolynomial (PluckerChartVariable p) K)) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ ambientAffineChartι p).ker

/-- The zero ideal obtained solely from the actual tautological section images. -/
def ambientIntrinsicZeroIdeal (forms : Fin m → StrictPairs n → K) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  ⨅ p : PluckerIndex (t + 2) n,
    intrinsicChartImageIdeal p (ambientIntrinsicPolynomialIdeal p forms)

/-- The intrinsic section images give exactly the independently constructed
polynomial zero scheme, with no change on overlaps. -/
theorem ambientIntrinsicZeroIdeal_eq (forms : Fin m → StrictPairs n → K) :
    ambientIntrinsicZeroIdeal (t := t) forms = ambientSectionZeroIdeal forms := by
  apply iInf_congr
  intro p
  change intrinsicChartImageIdeal p (ambientIntrinsicPolynomialIdeal p forms) =
    intrinsicChartImageIdeal p (isotropicChartSectionFunctional p forms).range
  rw [ambientIntrinsicPolynomialIdeal_eq, isotropicChartSectionFunctional_range]

/-- Identification with the original homogeneous-coordinate closed immersion. -/
theorem ambientIntrinsicZeroIdeal_eq_kernel (forms : Fin m → StrictPairs n → K) :
    ambientIntrinsicZeroIdeal (t := t) forms = (isotropicAmbientImmersion forms).ker :=
  (ambientIntrinsicZeroIdeal_eq forms).trans (ambientSectionZeroIdeal_eq_kernel forms)

abbrev ambientIntrinsicZeroScheme (forms : Fin m → StrictPairs n → K) : Scheme :=
  (ambientIntrinsicZeroIdeal (t := t) forms).subscheme

def isotropicToIntrinsicZero (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ⟶ ambientIntrinsicZeroScheme (t := t) forms :=
  IsClosedImmersion.lift (ambientIntrinsicZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientIntrinsicZeroIdeal_eq_kernel])

instance isotropicToIntrinsicZero_isIso (forms : Fin m → StrictPairs n → K) :
    IsIso (isotropicToIntrinsicZero (t := t) forms) :=
  IsClosedImmersion.isIso_lift (ambientIntrinsicZeroIdeal forms).subschemeι
    (isotropicAmbientImmersion forms) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, ambientIntrinsicZeroIdeal_eq_kernel])

/-- The original Proj is the zero scheme of the actual ambient tautological section. -/
def isotropicIntrinsicZeroIso (forms : Fin m → StrictPairs n → K) :
    Proj (isotropicProjectiveGrading (t := t) forms) ≅ ambientIntrinsicZeroScheme (t := t) forms :=
  asIso (isotropicToIntrinsicZero forms)

theorem isotropicIntrinsicZeroIso_over_ambient (forms : Fin m → StrictPairs n → K) :
    (isotropicIntrinsicZeroIso (t := t) forms).hom ≫
      (ambientIntrinsicZeroIdeal forms).subschemeι = isotropicAmbientImmersion forms :=
  IsClosedImmersion.lift_fac _ _ _

/-- The actual restricted Plücker twist of any integer degree. -/
def ambientIntrinsicZeroTwist (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (ambientIntrinsicZeroScheme (t := t) forms).Modules :=
  (Scheme.Modules.pullback (ambientIntrinsicZeroIdeal forms).subschemeι).obj
    (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n))) r)

/-- The intrinsic zero-scheme comparison preserves the original Plücker polarization
and every positive, zero, and negative integer twist. -/
def isotropicIntrinsicZeroTwistingIso (forms : Fin m → StrictPairs n → K) (r : ℤ) :
    (Scheme.Modules.pullback (isotropicIntrinsicZeroIso (t := t) forms).hom).obj
        (ambientIntrinsicZeroTwist forms r) ≅
      Proj.twistingSheaf (isotropicProjectiveGrading (t := t) forms) r :=
  (Scheme.Modules.pullbackComp (isotropicIntrinsicZeroIso forms).hom
    (ambientIntrinsicZeroIdeal forms).subschemeι).app _ ≪≫
      eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r))
          (isotropicIntrinsicZeroIso_over_ambient forms)) ≪≫
      isotropicAmbientTwistingPullbackIso forms r

end PaperVerification.AlternatingForms
end
end
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.AlternatingFormsIntrinsicZeroScheme"

section ComponentSource_2
/- Original module: PaperVerification.SchubertRankMeaning -/


/-!
# Determinantal flag equations and actual ranks over fields

For a coordinate projection, its image on the span of the matrix rows is
the span of the projected rows.  The dimension of that actual vector space
is below q exactly when the q-minor ideal vanishes.  The scheme-level
comparison uses the full ideals and therefore retains the nonreduced data.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.SchubertRankIdeals

variable {K : Type*} [Field K] {s n : ℕ}

/-- Dimension of the actual span of the coordinate-projected rows. -/
def coordinateProjectionRank (A : Matrix (Fin s) (Fin n) K)
    (C : Set (Fin n)) : ℕ :=
  Module.finrank K (Submodule.span K
    (Set.range fun i : Fin s ↦ fun c : C ↦ A i c.val))

/-- Restricted minors express precisely the ordinary projection-rank bound
on field-valued planes, for every minor size, including the boundary sizes. -/
theorem restrictedMinorIdeal_eq_bot_iff_projection_rank_lt
    (A : Matrix (Fin s) (Fin n) K) (q : ℕ) (C : Set (Fin n)) :
    restrictedMinorIdeal A q C = ⊥ ↔ coordinateProjectionRank A C < q := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  let B : Matrix (Fin s) C K := A.submatrix id Subtype.val
  have hr : B.rank = coordinateProjectionRank A C := by
    exact Matrix.rank_eq_finrank_span_row B
  rw [← hr]
  constructor
  · intro hbot
    apply lt_of_not_ge
    intro hq
    obtain ⟨rows, cols, hdet⟩ := Matrix.le_rank_iff_exists_det_submatrix_ne_zero.mp hq
    have hz : (A.submatrix rows (fun i ↦ (cols i).val)).det ∈
        restrictedMinorIdeal A q C :=
      Ideal.subset_span ⟨rows, (fun i ↦ (cols i).val), (fun i ↦ (cols i).property), rfl⟩
    rw [hbot] at hz
    exact hdet (show (B.submatrix rows cols).det = 0 from hz)
  · intro hq
    apply bot_unique
    apply Ideal.span_le.mpr
    rintro z ⟨rows, cols, hcols, rfl⟩
    change (A.submatrix rows cols).det = 0
    by_contra hdet
    let c : Fin q → C := fun i ↦ ⟨cols i, hcols i⟩
    have hd : (B.submatrix rows c).det ≠ 0 := hdet
    have hle : q ≤ B.rank := by
      simpa [Matrix.rank_of_det_ne_zero hd] using Matrix.rank_submatrix_le B rows c
    exact (not_le_of_gt hq) hle

end PaperVerification.SchubertRankIdeals
end
end
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.SchubertRankMeaning"

section ComponentSource_3
/- Original module: PaperVerification.RichardsonRingComparison -/


/-!
# The original interval ring and the independent opposite-flag ring

The flag ideal is defined by the actual projection-column conditions.
Its maximal-minor generators agree with the restricted rank minors on
every normalized Grassmannian chart.  The finite counting comparison
identifies this entire homogeneous ideal with the printed interval ideal,
so the ring comparison retains all polynomials and all homogeneous pieces.
It does not infer equality of graded rings merely from equality of Proj.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n : ℕ}

/-- Homogeneous equations for the two opposite coordinate-flag projections. -/
def flagRankPluckerIdeal (α β : Fin s → Fin n) :
    Ideal (MvPolynomial (PluckerIndex s n) K) :=
  matrixPluckerIdeal ⊔ ⨆ j : Fin s,
    selectedPluckerIdeal (K := K) (s := s) (s - j.val) {c | β j < c} ⊔
      selectedPluckerIdeal (K := K) (s := s) (j.val + 1) {c | c < α j}

/-- Equality of the entire ideals, before forming any projective spectrum. -/
theorem intervalPluckerIdeal_eq_flagRankPluckerIdeal (α β : Fin s → Fin n) :
    intervalPluckerIdeal (K := K) α β = flagRankPluckerIdeal α β :=
  intervalPluckerIdeal_eq_flag_coordinates α β

/-- The flag-rank homogeneous coordinate ring with the original Plücker variables. -/
abbrev FlagRankPluckerRing (α β : Fin s → Fin n) :=
  MvPolynomial (PluckerIndex s n) K ⧸ flagRankPluckerIdeal α β

/-- The original interval quotient is the independently defined opposite-flag ring. -/
def richardsonFlagRingEquiv (α β : Fin s → Fin n) :
    (MvPolynomial (PluckerIndex s n) K ⧸ intervalPluckerIdeal α β) ≃ₐ[K]
      FlagRankPluckerRing (K := K) α β :=
  Ideal.quotientEquivAlgOfEq K (intervalPluckerIdeal_eq_flagRankPluckerIdeal α β)

/-- Every original polynomial is retained by the comparison. -/
theorem richardsonFlagRingEquiv_mk (α β : Fin s → Fin n)
    (a : MvPolynomial (PluckerIndex s n) K) :
    richardsonFlagRingEquiv α β (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
  Ideal.quotientEquivAlgOfEq_mk K (intervalPluckerIdeal_eq_flagRankPluckerIdeal α β) a

/-- Exact preservation of every homogeneous piece, not merely of degree one. -/
theorem richardsonFlagRingEquiv_piece (α β : Fin s → Fin n) (d : ℕ) :
    (HomogeneousIdealPieces.piece (intervalPluckerIdeal (K := K) α β) d).map
        (richardsonFlagRingEquiv α β).toLinearMap =
      HomogeneousIdealPieces.piece (flagRankPluckerIdeal (K := K) α β) d := by
  apply le_antisymm
  · rintro y ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (richardsonFlagRingEquiv_mk α β a).symm⟩
  · rintro y ⟨a, ha, rfl⟩
    exact ⟨Ideal.Quotient.mk _ a, ⟨a, ha, rfl⟩, richardsonFlagRingEquiv_mk α β a⟩

end PaperVerification.AlternatingForms
end
end
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RichardsonRingComparison"

section ComponentSource_4
/- Original module: PaperVerification.RichardsonSchemeComparison -/


/-!
# The actual Richardson rank scheme and its Plücker presentation

The ambient scheme and its polynomial charts are fixed first.  Opposite
flag conditions are imposed by their actual determinantal ideals on these
charts.  The comparison below identifies the resulting closed subscheme
with the Proj of the original interval Plücker ideal, over every field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open _root_.HomogeneousLocalization

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem intervalPluckerIdeal_isHomogeneous
    (α β : Fin (t + 2) → Fin n) :
    (intervalPluckerIdeal (K := K) α β).IsHomogeneous
      (homogeneousSubmodule (PluckerIndex (t + 2) n) K) := by
  apply (matrixPluckerIdeal_isHomogeneous (by omega : 0 < t + 2)).sup
  apply Ideal.homogeneous_span
  rintro q ⟨I, hI, rfl⟩
  exact ⟨1, isHomogeneous_X K I⟩

/-- The literal grading on the paper's interval-coordinate quotient. -/
def richardsonProjectiveGrading (α β : Fin (t + 2) → Fin n) :=
  HomogeneousQuotientProjective.grading (intervalPluckerIdeal (K := K) α β)
    (intervalPluckerIdeal_isHomogeneous α β)

instance richardsonProjectiveGradedAlgebra (α β : Fin (t + 2) → Fin n) :
    GradedAlgebra (richardsonProjectiveGrading (K := K) α β) :=
  HomogeneousQuotientProjective.quotientGradedAlgebra _ _

theorem ambientPluckerIdeal_le_interval (α β : Fin (t + 2) → Fin n) :
    isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)) ≤
      intervalPluckerIdeal α β := by
  rw [isotropicPluckerIdeal_empty]
  exact le_sup_left

/-- The graded quotient retaining the original ambient Plücker coordinates. -/
abbrev richardsonAmbientGradedQuotient (α β : Fin (t + 2) → Fin n) :=
  HomogeneousQuotientProjective.quotientGradedHom
    (isotropicPluckerIdeal (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (intervalPluckerIdeal (K := K) α β)
    (isotropicPluckerIdeal_isHomogeneous emptyAlternatingTuple)
    (intervalPluckerIdeal_isHomogeneous α β) (ambientPluckerIdeal_le_interval α β)

/-- The canonical projective closed immersion into the ambient Grassmannian. -/
def richardsonAmbientImmersion (α β : Fin (t + 2) → Fin n) :
    Proj (richardsonProjectiveGrading (K := K) α β) ⟶
      ambientGrassmannian (K := K) t n :=
  HomogeneousQuotientProjective.quotientProjMap _ _ _ _
    (ambientPluckerIdeal_le_interval α β)

instance richardsonAmbientImmersion_isClosedImmersion
    (α β : Fin (t + 2) → Fin n) :
    IsClosedImmersion (richardsonAmbientImmersion (K := K) α β) :=
  HomogeneousQuotientProjective.quotientProjMap_isClosedImmersion _ _ _ _ _

/-- Independent local equations: actual minors for the two opposite flags. -/
def richardsonChartIdeal (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) : Ideal (MvPolynomial (PluckerChartVariable p) K) :=
  richardsonChartRankIdeal (pluckerChartMatrix p) α β

theorem intervalPluckerIdeal_map_chart_eq
    (p : PluckerIndex (t + 2) n) (α β : Fin (t + 2) → Fin n) :
    (intervalPluckerIdeal (K := K) α β).map
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom =
        richardsonChartIdeal (K := K) p α β :=
  intervalPluckerIdeal_map_eq_richardsonChartRankIdeal (K := K)
    (pluckerChartMatrix (K := K) p) p.val (pluckerChartMatrix_pivot p) α β

abbrev RichardsonChartRing (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :=
  MvPolynomial (PluckerChartVariable p) K ⧸ richardsonChartIdeal p α β

/-- The original polynomial evaluated on the normalized chart, then
reduced by its independent opposite-flag rank equations. -/
def richardsonChartEvaluation (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    MvPolynomial (PluckerIndex (t + 2) n) K →ₐ[K] RichardsonChartRing (K := K) p α β :=
  (Ideal.Quotient.mkₐ K (richardsonChartIdeal p α β)).comp
    (matrixMinorEvaluation (pluckerChartMatrix p))

theorem richardsonChartEvaluation_surjective (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Function.Surjective (richardsonChartEvaluation (K := K) p α β) :=
  (Ideal.Quotient.mkₐ_surjective K _).comp (matrixMinorEvaluation_chart_surjective p)

theorem richardsonChartEvaluation_kernel (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    RingHom.ker (richardsonChartEvaluation (K := K) p α β).toRingHom =
      intervalPluckerIdeal α β ⊔ Ideal.span {X p - 1} := by
  have h := Ideal.comap_map_of_surjective
    (matrixMinorEvaluation (K := K) (pluckerChartMatrix (K := K) p)).toRingHom
    (matrixMinorEvaluation_chart_surjective p) (intervalPluckerIdeal (K := K) α β)
  rw [intervalPluckerIdeal_map_chart_eq p α β, ← RingHom.ker_eq_comap_bot,
    matrixMinorEvaluation_chart_kernel] at h
  have hk : RingHom.ker (richardsonChartEvaluation (K := K) p α β).toRingHom =
      (richardsonChartIdeal (K := K) p α β).comap
        (matrixMinorEvaluation (K := K) (pluckerChartMatrix p)).toRingHom := by
    ext q
    change (Ideal.Quotient.mkₐ K (richardsonChartIdeal p α β))
      (matrixMinorEvaluation (K := K) (pluckerChartMatrix p) q) = 0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  have hgrass : (matrixPluckerIdeal (K := K) (s := t + 2) (n := n)) ≤
      intervalPluckerIdeal α β := le_sup_left
  rw [hk, h, pluckerBigCellIdeal, ← sup_assoc, sup_of_le_left hgrass]

/-- The actual normalized homogeneous quotient is the quotient by the
independently defined opposite flag minors. -/
def richardsonPluckerBigCellEquiv (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (MvPolynomial (PluckerIndex (t + 2) n) K ⧸
      (intervalPluckerIdeal α β ⊔ Ideal.span {X p - 1})) ≃ₐ[K]
        RichardsonChartRing (K := K) p α β :=
  (Ideal.quotientEquivAlgOfEq K (richardsonChartEvaluation_kernel p α β).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (richardsonChartEvaluation_surjective p α β))

def richardsonProjChartRingEquiv (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Away (richardsonProjectiveGrading (K := K) α β)
      (Ideal.Quotient.mk _ (X p)) ≃+* RichardsonChartRing (K := K) p α β :=
  (HomogeneousQuotientCharts.awayQuotientChartEquiv
    (intervalPluckerIdeal α β) (intervalPluckerIdeal_isHomogeneous α β) p).trans
    (richardsonPluckerBigCellEquiv p α β).toRingEquiv

def richardsonHomogeneousClass (α β : Fin (t + 2) → Fin n)
    {d : ℕ} (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    richardsonProjectiveGrading (K := K) α β d :=
  ⟨Ideal.Quotient.mk _ a, by
    change _ ∈ HomogeneousQuotientProjective.grading _ _ d
    rw [HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨a, ha, rfl⟩⟩

theorem richardsonChartRingEquiv_fraction (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) {d : ℕ}
    (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    richardsonProjChartRingEquiv p α β
      (HomogeneousChartDehomogenization.fraction
        (richardsonProjectiveGrading α β)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (richardsonHomogeneousClass α β a ha)) =
      richardsonChartEvaluation p α β a := by
  rw [richardsonProjChartRingEquiv, RingEquiv.trans_apply,
    HomogeneousQuotientCharts.awayQuotientChartEquiv, RingEquiv.trans_apply]
  erw [HomogeneousChartDehomogenization.awayEquivNormalized_fraction]
  change richardsonPluckerBigCellEquiv p α β
    (HomogeneousQuotientCharts.normalizedQuotientEquiv _ p
      (HomogeneousChartDehomogenization.quotientMap _
        (Ideal.Quotient.mk _ a))) = _
  rw [HomogeneousQuotientCharts.normalizedQuotientEquiv_class]
  have h₁ := Ideal.quotientEquivAlgOfEq_mk K
    (richardsonChartEvaluation_kernel p α β).symm a
  have h₂ := Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := richardsonChartEvaluation p α β)
    (richardsonChartEvaluation_surjective p α β) a
  exact (congrArg (Ideal.quotientKerAlgEquivOfSurjective
    (f := richardsonChartEvaluation p α β)
    (richardsonChartEvaluation_surjective p α β)) h₁).trans h₂

theorem richardsonAmbientAwayMap_fraction (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) {d : ℕ}
    (a : MvPolynomial (PluckerIndex (t + 2) n) K) (ha : a.IsHomogeneous d) :
    Away.map (richardsonAmbientGradedQuotient (K := K) α β)
      (Ideal.Quotient.mk _ (X p))
      (HomogeneousChartDehomogenization.fraction
        (isotropicProjectiveGrading (t := t) emptyAlternatingTuple)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (chartHomogeneousClass emptyAlternatingTuple a ha)) =
      HomogeneousChartDehomogenization.fraction (richardsonProjectiveGrading α β)
        (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
        (richardsonHomogeneousClass α β a ha) := by
  simp only [HomogeneousChartDehomogenization.fraction, Away.map_mk]
  rfl

theorem richardsonChartRing_commutes (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (richardsonProjChartRingEquiv (K := K) p α β).toRingHom.comp
        (Away.map (richardsonAmbientGradedQuotient α β) (Ideal.Quotient.mk _ (X p))) =
      (Ideal.Quotient.mk (richardsonChartIdeal p α β)).comp
        (ambientChartRingEquiv p).toRingHom := by
  ext z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective
    (isotropicProjectiveGrading (t := t) (emptyAlternatingTuple (K := K) (n := n)))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) z
  change a ∈ HomogeneousQuotientProjective.grading _ _ (d • 1) at ha
  rw [HomogeneousQuotientProjective.grading_eq_piece] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hbd : b.IsHomogeneous d := by simpa using hb
  change richardsonProjChartRingEquiv p α β
      (Away.map (richardsonAmbientGradedQuotient α β) (Ideal.Quotient.mk _ (X p))
        (HomogeneousChartDehomogenization.fraction _
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
          (chartHomogeneousClass emptyAlternatingTuple b hbd))) = _
  erw [richardsonAmbientAwayMap_fraction, richardsonChartRingEquiv_fraction]
  change richardsonChartEvaluation p α β b =
    Ideal.Quotient.mk _
      (emptyIsotropicChartRingEquiv p
        (isotropicProjChartRingEquiv_arbitraryChar p emptyAlternatingTuple
          (HomogeneousChartDehomogenization.fraction _
            (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) d
            (chartHomogeneousClass emptyAlternatingTuple b hbd))))
  rw [isotropicChartRingEquiv_fraction]
  change Ideal.Quotient.mk _ (matrixMinorEvaluation (pluckerChartMatrix p) b) =
    Ideal.Quotient.mk _
      (emptyIsotropicChartRingEquiv p
        (Ideal.Quotient.mk _ (matrixMinorEvaluation (pluckerChartMatrix p) b)))
  rw [emptyIsotropicChartRingEquiv_mk]

/-- Each literal determinantal chart is an actual open chart of the Proj. -/
def richardsonAffineChartι (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Spec (CommRingCat.of (RichardsonChartRing (K := K) p α β)) ⟶
      Proj (richardsonProjectiveGrading (K := K) α β) :=
  Spec.map (CommRingCat.ofHom (richardsonProjChartRingEquiv p α β).toRingHom) ≫
    Proj.awayι (richardsonProjectiveGrading α β) (Ideal.Quotient.mk _ (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos

instance richardsonAffineChartι_isOpenImmersion (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    IsOpenImmersion (richardsonAffineChartι (K := K) p α β) := by
  letI : IsIso (CommRingCat.ofHom (richardsonProjChartRingEquiv (K := K) p α β).toRingHom) :=
    (richardsonProjChartRingEquiv p α β).toCommRingCatIso.isIso_hom
  unfold richardsonAffineChartι
  infer_instance

theorem richardsonAffineChartι_opensRange (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (richardsonAffineChartι (K := K) p α β).opensRange =
      Proj.basicOpen (richardsonProjectiveGrading α β) (Ideal.Quotient.mk _ (X p)) := by
  letI : IsIso (CommRingCat.ofHom (richardsonProjChartRingEquiv (K := K) p α β).toRingHom) :=
    (richardsonProjChartRingEquiv p α β).toCommRingCatIso.isIso_hom
  unfold richardsonAffineChartι
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

theorem richardsonAffineChart_ambient_commutes (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    richardsonAffineChartι (K := K) p α β ≫ richardsonAmbientImmersion α β =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β))) ≫
        ambientAffineChartι p := by
  have hcomp :
      Proj.awayι (richardsonProjectiveGrading (K := K) α β)
          (Ideal.Quotient.mk _ (X p))
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos ≫
        richardsonAmbientImmersion α β =
      Spec.map (CommRingCat.ofHom
          (Away.map (richardsonAmbientGradedQuotient α β) (Ideal.Quotient.mk _ (X p)))) ≫
        Proj.awayι (isotropicProjectiveGrading (t := t) emptyAlternatingTuple)
          (Ideal.Quotient.mk _ (X p))
          (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) one_pos := by
    exact Proj.awayι_comp_map (richardsonAmbientGradedQuotient α β)
      (irrelevant_le_map_of_gradedSurjective _
        (HomogeneousQuotientProjective.quotientGradedHom_surjective _ _ _ _ _))
      one_pos (Ideal.Quotient.mk _ (X p))
      (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
  have hring :
      CommRingCat.ofHom
          (Away.map (richardsonAmbientGradedQuotient (K := K) α β) (Ideal.Quotient.mk _ (X p))) ≫
        CommRingCat.ofHom (richardsonProjChartRingEquiv p α β).toRingHom =
      CommRingCat.ofHom (ambientChartRingEquiv (K := K) p).toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β)) := by
    apply CommRingCat.hom_ext
    exact richardsonChartRing_commutes p α β
  unfold richardsonAffineChartι ambientAffineChartι
  rw [Category.assoc, hcomp, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp_assoc, hring]

theorem richardsonAffineChart_ambient_isPullback (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal (K := K) p α β))))
      (richardsonAffineChartι p α β) (ambientAffineChartι p)
      (richardsonAmbientImmersion α β) := by
  apply IsOpenImmersion.isPullback
  · exact richardsonAffineChart_ambient_commutes p α β
  · rw [ambientAffineChartι_opensRange, richardsonAffineChartι_opensRange]
    rfl

theorem richardsonProjBasicOpen_cover (α β : Fin (t + 2) → Fin n) :
    (⨆ p : PluckerIndex (t + 2) n, Proj.basicOpen (richardsonProjectiveGrading (K := K) α β)
      (Ideal.Quotient.mk (intervalPluckerIdeal α β) (X p))) = ⊤ :=
  HomogeneousQuotientProjective.presentation_basicOpen_cover _ _
    (Ideal.Quotient.mkₐ K (intervalPluckerIdeal α β)) Ideal.Quotient.mk_surjective
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)

def richardsonAffineChartCover (α β : Fin (t + 2) → Fin n) :
    (Proj (richardsonProjectiveGrading (K := K) α β)).AffineOpenCover where
  I₀ := PluckerIndex (t + 2) n
  X p := CommRingCat.of (RichardsonChartRing (K := K) p α β)
  f p := richardsonAffineChartι p α β
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((richardsonProjBasicOpen_cover α β).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (richardsonAffineChartι _ α β).opensRange
    rw [richardsonAffineChartι_opensRange]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((richardsonProjBasicOpen_cover α β).ge (Set.mem_univ x))).choose_spec

/-- The local opposite-flag zero scheme mapped into the ambient Grassmannian. -/
def richardsonRankChartZeroMap (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    Spec (CommRingCat.of (RichardsonChartRing (K := K) p α β)) ⟶
      ambientGrassmannian (K := K) t n :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β))) ≫
    ambientAffineChartι p

/-- The independent opposite-Schubert rank ideal sheaf. -/
def richardsonRankZeroIdeal (α β : Fin (t + 2) → Fin n) :
    (ambientGrassmannian (K := K) t n).IdealSheafData :=
  ⨅ p : PluckerIndex (t + 2) n, (richardsonRankChartZeroMap (K := K) p α β).ker

abbrev richardsonRankZeroScheme (α β : Fin (t + 2) → Fin n) : Scheme :=
  (richardsonRankZeroIdeal (K := K) α β).subscheme

theorem richardsonRankZeroIdeal_eq_kernel (α β : Fin (t + 2) → Fin n) :
    richardsonRankZeroIdeal (K := K) α β = (richardsonAmbientImmersion α β).ker := by
  calc
    richardsonRankZeroIdeal α β =
        ⨅ p : PluckerIndex (t + 2) n,
          (richardsonAffineChartι p α β ≫ richardsonAmbientImmersion α β).ker := by
      apply iInf_congr
      intro p
      exact congrArg Scheme.Hom.ker (richardsonAffineChart_ambient_commutes p α β).symm
    _ = (richardsonAmbientImmersion α β).ker :=
      (richardsonAmbientImmersion α β).iInf_ker_openCover_map_comp
        (richardsonAffineChartCover α β).openCover

/-- The ideal sheaf restricts to the exact determinantal ideal on every
chart, certifying that the local flag-rank equations glue without alteration. -/
theorem richardsonRankZeroIdeal_chart (p : PluckerIndex (t + 2) n)
    (α β : Fin (t + 2) → Fin n) :
    (richardsonRankZeroIdeal (K := K) α β).comap (ambientAffineChartι p) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β)))).ker := by
  rw [richardsonRankZeroIdeal_eq_kernel]
  ext1
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (richardsonAmbientImmersion α β)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (richardsonChartIdeal p α β))))
    (richardsonAffineChartι p α β) (ambientAffineChartι p)
    (richardsonAffineChart_ambient_isPullback p α β) W).symm

def richardsonToRankZero (α β : Fin (t + 2) → Fin n) :
    Proj (richardsonProjectiveGrading (K := K) α β) ⟶ richardsonRankZeroScheme (K := K) α β :=
  IsClosedImmersion.lift (richardsonRankZeroIdeal α β).subschemeι
    (richardsonAmbientImmersion α β) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, richardsonRankZeroIdeal_eq_kernel])

instance richardsonToRankZero_isIso (α β : Fin (t + 2) → Fin n) :
    IsIso (richardsonToRankZero (K := K) α β) :=
  IsClosedImmersion.isIso_lift (richardsonRankZeroIdeal α β).subschemeι
    (richardsonAmbientImmersion α β) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, richardsonRankZeroIdeal_eq_kernel])

/-- The paper's interval Proj is the actual independently specified
Richardson scheme of opposite flag-rank conditions. -/
def richardsonRankZeroIso (α β : Fin (t + 2) → Fin n) :
    Proj (richardsonProjectiveGrading (K := K) α β) ≅ richardsonRankZeroScheme (K := K) α β :=
  asIso (richardsonToRankZero α β)

theorem richardsonRankZeroIso_over_ambient (α β : Fin (t + 2) → Fin n) :
    (richardsonRankZeroIso (K := K) α β).hom ≫ (richardsonRankZeroIdeal α β).subschemeι =
      richardsonAmbientImmersion α β :=
  IsClosedImmersion.lift_fac _ _ _

end PaperVerification.AlternatingForms
end
end
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RichardsonSchemeComparison"

section ComponentSource_5
/- Original module: PaperVerification.RichardsonPolarization -/


/-!
# Every Plücker twist in the Richardson scheme comparison

The isomorphism of the original interval Proj with the independent
opposite-flag rank scheme is over the ambient Grassmannian and preserves
its actual projective polarization, including all integer twists.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n : ℕ}

def richardsonAmbientTwistingPullbackIso
    (α β : Fin (t + 2) → Fin n) (r : ℤ) :
    (Scheme.Modules.pullback (richardsonAmbientImmersion (K := K) α β)).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r) ≅
      Proj.twistingSheaf (richardsonProjectiveGrading α β) r :=
  TwistingSheafMap.pullbackIso_of_degreeOne_cover (richardsonAmbientGradedQuotient α β)
    (irrelevant_le_map_of_gradedSurjective _
      (HomogeneousQuotientProjective.quotientGradedHom_surjective _ _ _ _ _))
    (fun p : PluckerIndex (t + 2) n ↦ Ideal.Quotient.mk _ (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _)
    (isotropicProjBasicOpen_cover_arbitraryChar emptyAlternatingTuple) r

/-- The actual restricted Plücker twist on the independent rank scheme. -/
def richardsonRankZeroTwist (α β : Fin (t + 2) → Fin n) (r : ℤ) :
    (richardsonRankZeroScheme (K := K) α β).Modules :=
  (Scheme.Modules.pullback (richardsonRankZeroIdeal α β).subschemeι).obj
    (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
      (emptyAlternatingTuple (K := K) (n := n))) r)

/-- Exact preservation of each integer twist under the proved scheme isomorphism. -/
def richardsonRankZeroTwistingIso (α β : Fin (t + 2) → Fin n) (r : ℤ) :
    (Scheme.Modules.pullback (richardsonRankZeroIso (K := K) α β).hom).obj
        (richardsonRankZeroTwist α β r) ≅
      Proj.twistingSheaf (richardsonProjectiveGrading α β) r :=
  (Scheme.Modules.pullbackComp (richardsonRankZeroIso α β).hom
    (richardsonRankZeroIdeal α β).subschemeι).app _ ≪≫
      eqToIso (congrArg (fun f ↦ (Scheme.Modules.pullback f).obj
        (Proj.twistingSheaf (isotropicProjectiveGrading (t := t)
          (emptyAlternatingTuple (K := K) (n := n))) r))
          (richardsonRankZeroIso_over_ambient α β)) ≪≫
      richardsonAmbientTwistingPullbackIso α β r

end PaperVerification.AlternatingForms
end
end
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RichardsonPolarization"

section ComponentSource_6
/- Original module: PaperVerification.RichardsonTautologicalRanks -/


/-!
# The Richardson minors on the actual ambient tautological bundle

The rows in the determinantal equations are actual sections of the
incidence-kernel bundle.  Their ambient coordinate projections give the
literal rank minors used to define the independent Richardson scheme.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Matrix

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n : ℕ}

/-- Projection of the actual ambient tautological bundle to any chosen
coordinate subspace.  The two flags use the prefix and suffix choices. -/
def ambientTautologicalProjection (C : Set (Fin n)) :
    tautologicalKernel (t := t) (emptyAlternatingTuple (K := K) (n := n)) ⟶
      SheafModulePowers.structurePower (ambientGrassmannian (K := K) t n) C :=
  Pi.lift fun c ↦ tautologicalCoordinateFunctional emptyAlternatingTuple c.val

/-- Each component is the literal ambient coordinate of the tautological
inclusion, so this is the usual coordinate-flag projection. -/
theorem ambientTautologicalProjection_coordinate (C : Set (Fin n)) (c : C) :
    ambientTautologicalProjection (K := K) (t := t) C ≫
      Pi.π (fun _ : C ↦ SheafOfModules.unit
        (ambientGrassmannian (K := K) t n).ringCatSheaf) c =
      tautologicalCoordinateFunctional (t := t) emptyAlternatingTuple c.val := by
  unfold ambientTautologicalProjection
  exact Pi.lift_comp_π _ c

/-- A minor of a coordinate projection of the actual local tautological
frame, with arbitrary selected rows and columns. -/
def ambientTautologicalRankMinor (p : PluckerIndex (t + 2) n) (q : ℕ)
    (rows : Fin q → Fin (t + 2)) (cols : Fin q → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    Γ(ambientGrassmannian (K := K) t n, U) :=
  Matrix.det fun i j ↦ tautologicalSectionCoordinates emptyAlternatingTuple U
    (tautologicalRowSection p emptyAlternatingTuple U hU (rows i)) (cols j)

/-- Exact coefficient comparison for every rank minor, on every subopen
of the actual ambient chart.  No passage to reduced schemes or field-valued
points occurs. -/
theorem ambientTautologicalRankMinor_eq (p : PluckerIndex (t + 2) n) (q : ℕ)
    (rows : Fin q → Fin (t + 2)) (cols : Fin q → Fin n)
    (U : (ambientGrassmannian (K := K) t n).Opens)
    (hU : U ≤ tautologicalChartOpen p (emptyAlternatingTuple (K := K) (n := n))) :
    ambientTautologicalRankMinor p q rows cols U hU =
      tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU
        ((pluckerChartMatrix p).submatrix rows cols).det := by
  unfold ambientTautologicalRankMinor
  simp only [tautologicalRowSection_coordinates, tautologicalLocalMatrix]
  exact ((tautologicalLocalPolynomialHom p emptyAlternatingTuple U hU).map_det
    ((pluckerChartMatrix p).submatrix rows cols)).symm

end PaperVerification.AlternatingForms
end
end
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: PaperVerification.RichardsonTautologicalRanks"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`PaperVerification.AlternatingForms.tautologicalRowBasis, "definition"),
    (`PaperVerification.AlternatingForms.tautologicalRowBasis_apply, "theorem"),
    (`PaperVerification.AlternatingForms.ambientFrameWedgeValue_eq, "theorem"),
    (`PaperVerification.AlternatingForms.ambientFrameWedgeValue_eq_localForm, "theorem"),
    (`PaperVerification.AlternatingForms.ambientLocalExteriorImageIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientLocalExteriorImageIdeal_eq, "theorem"),
    (`PaperVerification.AlternatingForms.ambientIntrinsicChartIdeal_eq_map, "theorem"),
    (`PaperVerification.AlternatingForms.ambientIntrinsicPolynomialIdeal_eq, "theorem"),
    (`PaperVerification.AlternatingForms.ambientIntrinsicZeroIdeal, "definition"),
    (`PaperVerification.AlternatingForms.ambientIntrinsicZeroIdeal_eq, "theorem"),
    (`PaperVerification.AlternatingForms.ambientIntrinsicZeroIdeal_eq_kernel, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicIntrinsicZeroIso, "definition"),
    (`PaperVerification.AlternatingForms.isotropicIntrinsicZeroIso_over_ambient, "theorem"),
    (`PaperVerification.AlternatingForms.isotropicIntrinsicZeroTwistingIso, "definition"),
    (`PaperVerification.AlternatingForms.intervalPluckerIdeal_isHomogeneous, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonProjectiveGrading, "definition"),
    (`PaperVerification.AlternatingForms.richardsonAmbientImmersion, "definition"),
    (`PaperVerification.AlternatingForms.intervalPluckerIdeal_map_chart_eq, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonChartEvaluation_kernel, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonProjChartRingEquiv, "definition"),
    (`PaperVerification.AlternatingForms.richardsonAffineChart_ambient_commutes, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonAffineChart_ambient_isPullback, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonProjBasicOpen_cover, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonAffineChartCover, "definition"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroIdeal, "definition"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroScheme, "definition"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroIdeal_eq_kernel, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroIdeal_chart, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroIso, "definition"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroIso_over_ambient, "theorem"),
    (`PaperVerification.AlternatingForms.intervalPluckerIdeal_eq_flagRankPluckerIdeal, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonFlagRingEquiv, "definition"),
    (`PaperVerification.AlternatingForms.richardsonFlagRingEquiv_mk, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonFlagRingEquiv_piece, "theorem"),
    (`PaperVerification.SchubertRankIdeals.restrictedMinorIdeal_eq_bot_iff_projection_rank_lt, "theorem"),
    (`PaperVerification.AlternatingForms.richardsonAmbientTwistingPullbackIso, "definition"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroTwist, "definition"),
    (`PaperVerification.AlternatingForms.richardsonRankZeroTwistingIso, "definition"),
    (`PaperVerification.AlternatingForms.ambientTautologicalRankMinor, "definition"),
    (`PaperVerification.AlternatingForms.ambientTautologicalRankMinor_eq, "theorem"),
    (`PaperVerification.AlternatingForms.ambientTautologicalProjection, "definition"),
    (`PaperVerification.AlternatingForms.ambientTautologicalProjection_coordinate, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "cb56918e0eabb70c0f7bebcb15a7ad73"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:cb56918e0eabb70c0f7bebcb15a7ad73"
