module

public import ToricPower.CechProductElements
public import ToricPower.CechPosetCoefficients
public import ToricPower.CechLaurentCoefficients
public import ToricPower.FiniteAffineIntersectionSections
public import ToricPower.CechComparison.HigherFlasqueAcyclicity

/-!
# Tuple projective coefficients and the actual sheaf Čech complex

For an intersection-closed chart poset, evaluation of the ordered-tuple
projective resolution is the ordinary complete Čech complex of actual
sections. The only intersection hypothesis is the explicit equality of
its opens; actual toric charts will discharge it. The comparison retains
all ordered tuples and every cohomological degree.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open BondalThomsen.FiniteAffineCechHigherComparison
open BondalThomsen.FiniteAffineCechFlasqueAcyclicity

namespace ToricPower.FiniteCech

variable {B : Type} [SemilatticeInf B]
  (k : Type) [Field k] (X : Scheme) [X.Over (Spec (.of k))]
  (opens : B ⥤ X.Opens)
  (meetEq : ∀ (q : ℕ) (t : Fin (q+1) → B),
    cechIntersection opens.obj q t = opens.obj (tupleMeet t))
  (M : X.Modules)

/-- The actual chart-section presheaf, with its actual base-field scalars. -/
def meetChartSections : Bᵒᵖ ⥤ ModuleCat k :=
  opens.op ⋙ (FiniteCover.schemeBasePresheaf k X).obj M

/-- The exact additive coordinates of every tuple-projective Hom term. -/
def meetCechDegreeEquiv (q : ℕ) :
    (schemeCechComplex opens.obj M).X q ≃+
      (tupleCoefficientComplex k (meetChartSections k X opens M)).X q :=
  (CechProductElements.productElementsEquiv
      (fun t : Fin (q+1) → B => M.presheaf.obj (op (cechIntersection opens.obj q t)))).trans
    ((AddEquiv.piCongrRight (fun t => toricSectionOpenEquiv X M (meetEq q t))).trans
      (tupleEvaluation k q (meetChartSections k X opens M)).toAddEquiv.symm)

/-- Evaluation is precisely transport of the ordinary tuple section. -/
theorem meetCechDegreeEquiv_apply (q : ℕ)
    (x : (schemeCechComplex opens.obj M).X q) (t : Fin (q+1) → B) :
    tupleEvaluation k q (meetChartSections k X opens M)
        (meetCechDegreeEquiv k X opens meetEq M q x) t =
      toricSectionOpenEquiv X M (meetEq q t)
        (cechCoordinate opens.obj M q x t) := by
  change ((tupleEvaluation k q (meetChartSections k X opens M))
    ((tupleEvaluation k q (meetChartSections k X opens M)).symm _)) t = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (toricSectionOpenEquiv X M (meetEq q t))
    (CechProductElements.productElementsEquiv_apply _ x t)

/-- All actual tuple restrictions agree with the intersection-poset maps. -/
theorem meetCech_restriction {p q : ℕ} (s : Fin (p+1) → Fin (q+1))
    (t : Fin (q+1) → B)
    (x : M.presheaf.obj (op (cechIntersection opens.obj p (t ∘ s)))) :
    toricSectionOpenEquiv X M (meetEq q t)
        (M.presheaf.map (Limits.Pi.lift (fun j : Fin (p+1) =>
          Limits.Pi.π (opens.obj ∘ t) (s j))).op x) =
      (meetChartSections k X opens M).map
        (homOfLE (tupleMeet_le_selection s t)).op
        (toricSectionOpenEquiv X M (meetEq p (t ∘ s)) x) := by
  have h := toricSectionOpenEquiv_restrict X M (meetEq p (t ∘ s)) (meetEq q t)
    (Limits.Pi.lift (fun j : Fin (p+1) => Limits.Pi.π (opens.obj ∘ t) (s j))).le
    (opens.map (homOfLE (tupleMeet_le_selection s t))).le x
  exact h

/-- The entire alternating differential is the ordinary sheaf restriction differential. -/
theorem meetCechDegreeEquiv_d (q : ℕ) (x : (schemeCechComplex opens.obj M).X q) :
    meetCechDegreeEquiv k X opens meetEq M (q+1)
        ((schemeCechComplex opens.obj M).d q (q+1) x) =
      (tupleCoefficientComplex k (meetChartSections k X opens M)).d q (q+1)
        (meetCechDegreeEquiv k X opens meetEq M q x) := by
  apply (tupleEvaluation k (q+1) (meetChartSections k X opens M)).injective
  funext t
  rw [meetCechDegreeEquiv_apply, tupleCoefficient_d_apply, cechDifferential_component,
    map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_zsmul, meetCechDegreeEquiv_apply, meetCech_restriction k X opens meetEq M]

/-- An actual isomorphism of the complete complexes after forgetting scalars. -/
def meetCechComplexForgetIso :
    schemeCechComplex opens.obj M ≅
      ((forget₂ (ModuleCat k) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (tupleCoefficientComplex k (meetChartSections k X opens M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (meetCechDegreeEquiv k X opens meetEq M q).toAddCommGrpIso)
    (fun p q hpq => by
      obtain rfl : p+1=q := hpq
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      exact fun x => (meetCechDegreeEquiv_d k X opens meetEq M p x).symm)

include meetEq in
/-- Flasqueness proves exactness of every positive tuple-projective Hom row. -/
theorem meetTupleCoefficient_exactAt_positive [Finite B] [M.presheaf.IsFlasque] (q : ℕ) :
    (tupleCoefficientComplex k (meetChartSections k X opens M)).ExactAt (q+1) := by
  have h := (BondalThomsen.FiniteAffineCechHigherFlasqueAcyclicity.standardCech_exactAt_positive
    opens.obj M q).of_iso (meetCechComplexForgetIso k X opens meetEq M)
  rw [HomologicalComplex.exactAt_iff' _ q (q+1) (q+2) (by simp) (by simp)] at h ⊢
  exact (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (ModuleCat k) AddCommGrpCat)).mp h

end ToricPower.FiniteCech
