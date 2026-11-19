module

public import PaperVerification.AlternatingFormsTautologicalChartCoordinates

/-!
# Local frames on every subopen of a Plücker chart

The coefficient maps are restrictions of the actual affine-chart functions.
The chart calculation consequently applies to every subopen, as required for
an isomorphism of sheaves rather than only their global section modules.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {t n m : ℕ}

def tautologicalLocalSectionHom (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    IsotropicChartRing p forms →+* Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V) :=
  ((Proj (isotropicProjectiveGrading (t:=t) forms)).presheaf.map
    (homOfLE hV).op).hom.comp (tautologicalChartSectionHom p forms)

def tautologicalLocalPolynomialHom (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    MvPolynomial (PluckerChartVariable p) K →+*
      Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V) :=
  (tautologicalLocalSectionHom p forms V hV).comp
    (Ideal.Quotient.mk (isotropicChartIdeal p forms))

def tautologicalLocalMatrix (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :=
  (pluckerChartMatrix (K:=K) p).map (tautologicalLocalPolynomialHom p forms V hV)

theorem tautologicalLocalMatrix_pivot (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    (tautologicalLocalMatrix p forms V hV).submatrix id p.val=1 :=
  NormalizedTautologicalKernel.pivot_map _ _ _ (pluckerChartMatrix_pivot (K:=K) p)

def tautologicalLocalLineEquiv (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V) ≃ₗ[
      Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V)]
      Γ(tautologicalLine (t:=t) forms,V) :=
  Proj.twistingSheaf.chartSectionsLinearEquiv
    (𝒜:=isotropicProjectiveGrading (t:=t) forms) 1
    (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p) V hV

theorem tautologicalLocal_frame_homogeneous
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1) :
    tautologicalLocalLineEquiv p forms V hV
      (tautologicalLocalSectionHom p forms V hV (isotropicChartEvaluation p forms f)) =
      Proj.toTwistingSheaf (isotropicProjectiveGrading (t:=t) forms) rfl V
        (homogeneousPluckerClass forms f hf) := by
  let i : V ⟶ tautologicalChartOpen p forms := homOfLE hV
  have hnat := Proj.twistingSheaf.res_chartSectionsLinearEquiv
    (𝒜 := isotropicProjectiveGrading (t := t) forms) 1
    (Ideal.Quotient.mk (isotropicPluckerIdeal forms) (X p))
    (HomogeneousQuotientProjective.quotient_X_mem_one _ _ p)
    (tautologicalChartOpen p forms) le_rfl i
    (tautologicalChartSectionHom p forms (isotropicChartEvaluation p forms f))
  calc
    tautologicalLocalLineEquiv p forms V hV
        (tautologicalLocalSectionHom p forms V hV (isotropicChartEvaluation p forms f)) =
      (tautologicalLine (t := t) forms).presheaf.map i.op
        (tautologicalChartLineEquiv p forms
          (tautologicalChartSectionHom p forms (isotropicChartEvaluation p forms f))) := hnat.symm
    _ = (tautologicalLine (t := t) forms).presheaf.map i.op
        (Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl
          (tautologicalChartOpen p forms) (homogeneousPluckerClass forms f hf)) :=
      congrArg (fun z => (tautologicalLine (t := t) forms).presheaf.map i.op z)
        (tautologicalChart_frame_homogeneous p forms f hf)
    _ = Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl V
        (homogeneousPluckerClass forms f hf) := rfl

theorem tautologicalLocal_incidence_coordinates
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (v : Fin n → Γ(Proj (isotropicProjectiveGrading (t:=t) forms),V))
    (J : Fin ((t+2)+1) → Fin n) :
    (∑ i : Fin n, v i * tautologicalLocalSectionHom p forms V hV
      (isotropicChartEvaluation p forms (tautologicalIncidenceCoefficient J i))) =
      NormalizedTautologicalKernel.incidence (tautologicalLocalMatrix p forms V hV) v J :=
  tautologicalIncidenceCoefficient_evaluation_map
    (tautologicalLocalPolynomialHom p forms V hV) (pluckerChartMatrix p) v J

theorem tautologicalIncidenceComponent_local
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (J : Fin ((t+2)+1) → Fin n)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj (op V)) :
    (tautologicalIncidenceComponent (t:=t) forms J).val.app (op V) x =
      tautologicalLocalLineEquiv p forms V hV
        (NormalizedTautologicalKernel.incidence (tautologicalLocalMatrix p forms V hV)
          (SheafModulePowers.sectionsEquiv
            (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
            (Fin n) V x) J) := by
  classical
  refine (SheafCoordinateMorphisms.fromSections_apply
    (tautologicalLine (t := t) forms)
    (fun i : Fin n => tautologicalCoordinateSection forms
      (tautologicalIncidenceCoefficient (K := K) J i)
      (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i))
    V x).trans ?_
  simp only [tautologicalCoordinateSection_eval]
  let v : Fin n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), V) :=
    SheafModulePowers.sectionsEquiv
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) V x
  let a : Fin n → Γ(Proj (isotropicProjectiveGrading (t := t) forms), V) :=
    fun i => tautologicalLocalSectionHom p forms V hV
      (isotropicChartEvaluation p forms (tautologicalIncidenceCoefficient (K := K) J i))
  let z : Fin n → Γ(tautologicalLine (t := t) forms, V) := fun i =>
    Proj.toTwistingSheaf (isotropicProjectiveGrading (t := t) forms) rfl V
      (homogeneousPluckerClass forms (tautologicalIncidenceCoefficient (K := K) J i)
        (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i))
  have hframe (i : Fin n) : (tautologicalLocalLineEquiv p forms V hV) (a i) = z i :=
    tautologicalLocal_frame_homogeneous p forms V hV (tautologicalIncidenceCoefficient (K := K) J i)
      (tautologicalIncidenceCoefficient_isHomogeneous (K := K) J i)
  exact (SheafCoordinateMorphisms.sum_smul_eq_frame
    (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), V))
    (M := Γ(tautologicalLine (t := t) forms, V))
    (tautologicalLocalLineEquiv p forms V hV) v a z hframe).trans
      (congrArg (tautologicalLocalLineEquiv p forms V hV) (tautologicalLocal_incidence_coordinates p forms V hV v J))

theorem tautologicalIncidenceMap_local_zero_iff
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj (op V)) :
    (tautologicalIncidenceMap (t:=t) forms).val.app (op V) x=0 ↔
      ∀ J, NormalizedTautologicalKernel.incidence (tautologicalLocalMatrix p forms V hV)
        (SheafModulePowers.sectionsEquiv
          (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
          (Fin n) V x) J=0 := by
  rw [SheafModulePowers.section_eq_zero_iff
    (tautologicalLine (t:=t) forms) (Fin ((t+2)+1) → Fin n) V]
  apply forall_congr'
  intro J
  have hc := (tautologicalIncidenceMap_component_apply (t := t) forms J
    V x).trans (tautologicalIncidenceComponent_local p forms V hV J x)
  constructor
  · intro h
    apply (tautologicalLocalLineEquiv p forms V hV).injective
    exact hc.symm.trans (h.trans (map_zero (tautologicalLocalLineEquiv p forms V hV)).symm)
  · intro h
    exact hc.trans ((congrArg (tautologicalLocalLineEquiv p forms V hV) h).trans
      (map_zero (tautologicalLocalLineEquiv p forms V hV)))

/-- On every subopen of the pivot chart, the actual pivot morphism is a
bijection on sections. Its inverse is the normalized row embedding. -/
theorem tautologicalPivotMap_bijective
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (V : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (hV : V ≤ tautologicalChartOpen p forms) :
    Function.Bijective ((tautologicalPivotMap p forms).val.app (op V)) := by
  letI : CommRing ((Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf.obj.obj
      (op V)) := inferInstanceAs
    (CommRing Γ(Proj (isotropicProjectiveGrading (t:=t) forms), V))
  let eA := SheafModulePowers.sectionsEquiv
    (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
    (Fin n) V
  let eB := SheafModulePowers.sectionsEquiv
    (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf)
    (Fin (t+2)) V
  let eK := SheafModuleKernels.sectionsEquiv
    (tautologicalIncidenceMap (t:=t) forms) V
  let f :
      (SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n)).val.obj (op V) →ₗ[
          Γ(Proj (isotropicProjectiveGrading (t := t) forms), V)]
      (SheafModulePowers.power (tautologicalLine (t := t) forms)
        (Fin ((t + 2) + 1) → Fin n)).val.obj (op V) :=
    ((SheafOfModules.evaluation
    (Proj (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf (op V)).map
      (tautologicalIncidenceMap (t:=t) forms)).hom
  have hP := NormalizedTautologicalKernel.kernel_pivot_bijective
    (R := Γ(Proj (isotropicProjectiveGrading (t := t) forms), V))
    (M := (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n)).val.obj (op V))
    (N := (SheafModulePowers.power (tautologicalLine (t := t) forms)
      (Fin ((t + 2) + 1) → Fin n)).val.obj (op V)) f eA
    (tautologicalLocalMatrix p forms V hV) p.val
    (tautologicalLocalMatrix_pivot p forms V hV)
    (tautologicalIncidenceMap_local_zero_iff p forms V hV)
  have he (x : (tautologicalKernel (t:=t) forms).val.obj (op V)) :
      eB ((tautologicalPivotMap p forms).val.app (op V) x) =
        fun i => eA (eK x).val (p.val i) := by
    funext i
    have hB := SheafModulePowers.sectionsEquiv_apply
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin (t + 2)) V ((tautologicalPivotMap p forms).val.app (op V) x) i
    have hProjection := congrArg
      (fun g : tautologicalKernel (t := t) forms ⟶
          SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf =>
        g.val.app (op V) x)
      (tautologicalPivotMap_projection p forms i)
    have hA := SheafModulePowers.sectionsEquiv_apply
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) V (eK x).val (p.val i)
    have hK := congrArg
      (fun z : (SheafModulePowers.structurePower
          (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n)).val.obj (op V) =>
        (Pi.π (fun _ : Fin n => SheafOfModules.unit
          (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf) (p.val i)).val.app
            (op V) z)
      (SheafModuleKernels.sectionsEquiv_coe (tautologicalIncidenceMap (t := t) forms) V x)
    exact hB.trans (hProjection.trans (hA.trans hK).symm)
  have hb : Function.Bijective
      (fun x => eB ((tautologicalPivotMap p forms).val.app (op V) x)) := by
    have hh : (fun x => eB ((tautologicalPivotMap p forms).val.app (op V) x)) =
        (fun x => fun i => eA (eK x).val (p.val i)) := funext he
    rw [hh]
    exact hP.comp eK.bijective
  constructor
  · intro x y h
    exact hb.1 (congrArg eB h)
  · intro y
    obtain ⟨x,hx⟩ := hb.2 (eB y)
    exact ⟨x,eB.injective hx⟩

/-- The actual tautological kernel is isomorphic on the whole pivot chart to
`𝒪^s`. The comparison is induced by its actual coordinate projection. -/
def tautologicalFrameIso (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    (tautologicalKernel (t:=t) forms).over (tautologicalChartOpen p forms) ≅
      (SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin (t+2))).over
          (tautologicalChartOpen p forms) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective
        (((tautologicalPivotMap p forms).over (tautologicalChartOpen p forms)).val.app V).hom
        (tautologicalPivotMap_bijective p forms V.unop.left V.unop.hom.le)).toModuleIso)
      (fun _ _ f => ((tautologicalPivotMap p forms).over
        (tautologicalChartOpen p forms)).val.naturality f)

/-- Every standard chart carries a genuine free frame of the indicated rank. -/
theorem tautological_frame_exists (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    Nonempty ((tautologicalKernel (t:=t) forms).over (tautologicalChartOpen p forms) ≅
      (SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin (t+2))).over
          (tautologicalChartOpen p forms)) :=
  ⟨tautologicalFrameIso p forms⟩

end PaperVerification.AlternatingForms
