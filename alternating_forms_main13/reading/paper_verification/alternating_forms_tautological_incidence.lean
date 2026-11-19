module

public import PaperVerification.AlternatingFormsUniversalCharts
public import PaperVerification.NormalizedTautologicalFrame
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import PaperVerification.SheafModuleKernels
public import PaperVerification.SheafCoordinateMorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The universal tautological incidence map

The source is the genuine free structure sheaf on the ambient coordinate
vectors. Its target is a finite product of the genuine Plücker twisting sheaf.
The matrix entries are the signed Plücker coordinates in the exterior-product
formula. Its kernel is defined before any rank or cohomology assertion.

Evaluation on a normalized chart gives the actual augmented determinants;
the preceding integral matrix theorem identifies their common kernel with the
span of the normalized rows, over arbitrary coefficient algebras.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped BigOperators
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite

namespace PaperVerification.AlternatingForms

variable {K : Type} [Field K] {s t n m : ℕ}

/-- The coefficient of the ambient vector coordinate `i` in the exterior
incidence equation indexed by the ordered column word `J`. -/
def tautologicalIncidenceCoefficient (J : Fin (s+1) → Fin n) (i : Fin n) :
    MvPolynomial (PluckerIndex s n) K :=
  ∑ q : Fin (s+1), if J q=i then
    ((-1 : K)^q.val) • orderedPluckerCoordinate (fun z => J (q.succAbove z))
  else 0

theorem tautologicalIncidenceCoefficient_isHomogeneous
    (J : Fin (s+1) → Fin n) (i : Fin n) :
    (tautologicalIncidenceCoefficient (K:=K) J i).IsHomogeneous 1 := by
  classical
  unfold tautologicalIncidenceCoefficient
  apply MvPolynomial.IsHomogeneous.sum
  intro q hq
  split_ifs
  · exact (MvPolynomial.homogeneousSubmodule (PluckerIndex s n) K 1).smul_mem _
      (orderedPluckerCoordinate_isHomogeneous _)
  · exact MvPolynomial.isHomogeneous_zero _ K _

/-- The coefficient expression is literally the determinant with the tested
vector adjoined to the row matrix, by Laplace expansion. -/
theorem tautologicalIncidenceCoefficient_evaluation
    {R : Type*} [CommRing R] [Algebra K R]
    (A : Matrix (Fin s) (Fin n) R) (v : Fin n → R)
    (J : Fin (s+1) → Fin n) :
    (∑ i : Fin n, v i * matrixMinorEvaluation A
      (tautologicalIncidenceCoefficient (K:=K) J i)) =
      NormalizedTautologicalKernel.incidence A v J := by
  classical
  simp only [tautologicalIncidenceCoefficient,map_sum,apply_ite,map_smul,map_zero,
    matrixMinorEvaluation_orderedCoordinate,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true,Algebra.smul_def]
  rw [NormalizedTautologicalKernel.incidence_eq_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [map_pow, map_neg, map_one, Matrix.submatrix, id_eq]
  ring

/-- The same determinant identity after an arbitrary ring homomorphism. This
form does not choose an additional coefficient-field action on the target. -/
theorem tautologicalIncidenceCoefficient_evaluation_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra K R]
    (φ : R →+* S) (A : Matrix (Fin s) (Fin n) R)
    (v : Fin n → S) (J : Fin (s+1) → Fin n) :
    (∑ i : Fin n, v i * φ (matrixMinorEvaluation A
      (tautologicalIncidenceCoefficient (K:=K) J i))) =
      NormalizedTautologicalKernel.incidence (A.map φ) v J := by
  classical
  simp only [tautologicalIncidenceCoefficient, map_sum, apply_ite, map_smul,
    map_zero, matrixMinorEvaluation_orderedCoordinate, Algebra.smul_def,
    map_mul, map_pow, map_neg, map_one, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [NormalizedTautologicalKernel.incidence_eq_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [RingHom.map_det]
  change v (J q) * ((-1 : S)^q.val *
    Matrix.det ((A.map φ).submatrix id (fun z => J (q.succAbove z)))) =
      (-1 : S)^q.val * v (J q) *
        Matrix.det ((A.map φ).submatrix id (fun z => J (q.succAbove z)))
  ring

abbrev tautologicalLine (forms : Fin m → StrictPairs n → K) :=
  Proj.twistingSheaf (isotropicProjectiveGrading (t:=t) forms) (1 : ℤ)

/-- A homogeneous class, with its membership proof in the literal quotient
grading. -/
def homogeneousPluckerClass (forms : Fin m → StrictPairs n → K)
    {d : ℕ} (f : MvPolynomial (PluckerIndex (t+2) n) K)
    (hf : f.IsHomogeneous d) : isotropicProjectiveGrading (t:=t) forms d :=
  ⟨Ideal.Quotient.mk (isotropicPluckerIdeal forms) f, by
    change Ideal.Quotient.mk (isotropicPluckerIdeal forms) f ∈
      HomogeneousQuotientProjective.grading _ _ d
    rw [HomogeneousQuotientProjective.grading_eq_piece]
    exact ⟨f,hf,rfl⟩⟩

/-- The actual compatible family of twisting-sheaf sections associated to a
homogeneous coordinate linear form. -/
def tautologicalCoordinateSection (forms : Fin m → StrictPairs n → K)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1) :
    (tautologicalLine (t:=t) forms).sections := by
  let r : isotropicProjectiveGrading (t:=t) forms 1 :=
    homogeneousPluckerClass forms f hf
  exact PresheafOfModules.sectionsMk
    (fun U => Proj.toTwistingSheaf
      (isotropicProjectiveGrading (t:=t) forms) rfl U.unop r)
    (by intro U V i; rfl)

@[simp] theorem tautologicalCoordinateSection_value
    (forms : Fin m → StrictPairs n → K)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1)
    (U : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens) :
    (tautologicalCoordinateSection forms f hf).val (op U) =
      Proj.toTwistingSheaf (isotropicProjectiveGrading (t:=t) forms) rfl U
        (homogeneousPluckerClass forms f hf) := rfl

@[simp] theorem tautologicalCoordinateSection_eval
    (forms : Fin m → StrictPairs n → K)
    (f : MvPolynomial (PluckerIndex (t+2) n) K) (hf : f.IsHomogeneous 1)
    (U : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens) :
    (tautologicalCoordinateSection forms f hf).eval (op U) =
      Proj.toTwistingSheaf (isotropicProjectiveGrading (t:=t) forms) rfl U
        (homogeneousPluckerClass forms f hf) := rfl

/-- One component of the universal exterior incidence morphism. -/
def tautologicalIncidenceComponent (forms : Fin m → StrictPairs n → K)
    (J : Fin ((t+2)+1) → Fin n) :
    SheafModulePowers.structurePower (Proj
      (isotropicProjectiveGrading (t:=t) forms)) (Fin n) ⟶
        tautologicalLine (t:=t) forms :=
  SheafCoordinateMorphisms.fromSections _
    (fun i : Fin n => tautologicalCoordinateSection forms
      (tautologicalIncidenceCoefficient J i)
      (tautologicalIncidenceCoefficient_isHomogeneous J i))

/-- The global map uses actual free and twisting sheaves; it is independent
of the subsequent chart-rank calculation. -/
def tautologicalIncidenceMap (forms : Fin m → StrictPairs n → K) :
    SheafModulePowers.structurePower (Proj
      (isotropicProjectiveGrading (t:=t) forms)) (Fin n) ⟶
      ∏ᶜ (fun _ : Fin ((t+2)+1) → Fin n => tautologicalLine (t:=t) forms) :=
  Pi.lift (tautologicalIncidenceComponent forms)

@[simp] theorem tautologicalIncidenceMap_component
    (forms : Fin m → StrictPairs n → K) (J : Fin ((t+2)+1) → Fin n) :
    tautologicalIncidenceMap (t:=t) forms ≫
      Pi.π (fun _ : Fin ((t+2)+1) → Fin n => tautologicalLine (t:=t) forms) J =
        tautologicalIncidenceComponent (t:=t) forms J :=
  Pi.lift_comp_π _ _

@[simp] theorem tautologicalIncidenceMap_component_apply
    (forms : Fin m → StrictPairs n → K) (J : Fin ((t+2)+1) → Fin n)
    (U : (Proj (isotropicProjectiveGrading (t:=t) forms)).Opens)
    (x : (SheafModulePowers.structurePower
      (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin n)).val.obj (op U)) :
    (Pi.π (fun _ : Fin ((t+2)+1) → Fin n => tautologicalLine (t:=t) forms) J).val.app
      (op U) ((tautologicalIncidenceMap (t:=t) forms).val.app (op U) x) =
        (tautologicalIncidenceComponent (t:=t) forms J).val.app (op U) x := by
  exact congrArg (fun f => f.val.app (op U) x)
    (tautologicalIncidenceMap_component (t:=t) forms J)

/-- The canonical submodule sheaf cut out by universal Plücker incidence. -/
def tautologicalKernel (forms : Fin m → StrictPairs n → K) :
    (Proj (isotropicProjectiveGrading (t:=t) forms)).Modules :=
  kernel (tautologicalIncidenceMap (t:=t) forms)

/-- Its inclusion is the actual categorical kernel inclusion. -/
def tautologicalKernelInclusion (forms : Fin m → StrictPairs n → K) :
    tautologicalKernel (t:=t) forms ⟶
      SheafModulePowers.structurePower (Proj
        (isotropicProjectiveGrading (t:=t) forms)) (Fin n) :=
  kernel.ι (tautologicalIncidenceMap (t:=t) forms)

theorem tautologicalKernel_incidence (forms : Fin m → StrictPairs n → K) :
    tautologicalKernelInclusion (t:=t) forms ≫
      tautologicalIncidenceMap (t:=t) forms=0 :=
  kernel.condition _

/-- Projection of the actual kernel inclusion onto the selected pivot
coordinates. This is a global sheaf morphism; its restriction to the pivot
chart is the local frame coordinate map. -/
def tautologicalPivotMap (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :
    tautologicalKernel (t:=t) forms ⟶
      SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t:=t) forms)) (Fin (t+2)) :=
  tautologicalKernelInclusion (t := t) forms ≫
    SheafModulePowers.reindex
      (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
      (Fin n) (Fin (t + 2)) p.val

/-- The pivot map is the original coordinate projection after the genuine
kernel inclusion. -/
theorem tautologicalPivotMap_projection
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (i : Fin (t+2)) :
    tautologicalPivotMap p forms ≫
      Pi.π (fun _ : Fin (t+2) => SheafOfModules.unit (Proj
        (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf) i =
      tautologicalKernelInclusion (t:=t) forms ≫
        Pi.π (fun _ : Fin n => SheafOfModules.unit (Proj
          (isotropicProjectiveGrading (t:=t) forms)).ringCatSheaf) (p.val i) := by
  unfold tautologicalPivotMap
  exact (CategoryTheory.Category.assoc _ _ _).trans
    (congrArg
      (fun g : SheafModulePowers.structurePower
        (Proj (isotropicProjectiveGrading (t := t) forms)) (Fin n) ⟶
          SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf ↦
        tautologicalKernelInclusion (t := t) forms ≫ g)
      (SheafModulePowers.reindex_projection
        (SheafOfModules.unit (Proj (isotropicProjectiveGrading (t := t) forms)).ringCatSheaf)
        (Fin n) (Fin (t + 2)) p.val i))

end PaperVerification.AlternatingForms
