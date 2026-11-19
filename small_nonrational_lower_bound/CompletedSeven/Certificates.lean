module

public import SevenFamilyActualEncoding

@[expose] public section

/-!
# Exact certificates for the three seven-facet branches

The records retain the complete cell universe, all incidence data through
`FiniteClassification`, and the exact geometric placement coverage. The
numerical row only chooses a certificate; it is never an additional premise
about the original polytope.
-/

set_option autoImplicit false
noncomputable section
namespace Papers.RationalityTen.CompletedSeven

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open ActualResidualPartition MatroidChecked.SevenBudgetCoverage
open SevenFamilyActualEncoding

structure PureRowCertificate (row : CaseRow) where
  cellCount : Nat
  cells : Fin cellCount → ConcreteGrowth.Cell
  root : Fin cellCount
  template : Fin 34
  template_eq : row.template = template.val
  classification : RootedFamilyClosure.FiniteClassification cells
    (rowQuota row.T row.BP row.SP 0) root
  coverage : Coverage cells root template (fun a => a.size ≤ 5)
    (rowQuota row.T row.BP row.SP 0)

structure MixedRowCertificate (row : CaseRow) where
  cellCount : Nat
  cells : Fin cellCount → ConcreteGrowth.Cell
  root : Fin cellCount
  template : Fin 34
  sixTemplate : Fin 7
  template_eq : row.template = template.val
  six_eq : row.sixTemplate = some sixTemplate.val
  classification : RootedFamilyClosure.FiniteClassification cells
    (rowQuota row.T row.BP row.SP 1) root
  coverage : Coverage cells root template
    (fun a => a.size ≤ 5 ∨ a = .six sixTemplate)
    (rowQuota row.T row.BP row.SP 1)

structure TwoSixCertificate (template : Fin 34) (squares : Fin 8) where
  cellCount : Nat
  cells : Fin cellCount → ConcreteGrowth.Cell
  root : Fin cellCount
  classification : RootedFamilyClosure.FiniteClassification cells
    (rowQuota 0 (7 - squares.val) squares.val 2) root
  coverage : Coverage cells root template (fun _ => True)
    (rowQuota 0 (7 - squares.val) squares.val 2)

theorem pure_of_certificate (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenPureCase P) (D : PureRowCertificate C.row) :
    HasClassifiedEncoding P := by
  have ht : D.template = C.template :=
    Fin.ext (D.template_eq.symm.trans C.row_template)
  exact pure_case P hP C D.cells D.root D.classification (by
    simpa only [ht] using D.coverage)

theorem mixed_of_certificate (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenMixedCase P) (D : MixedRowCertificate C.row) :
    HasClassifiedEncoding P := by
  have ht : D.template = C.template :=
    Fin.ext (D.template_eq.symm.trans C.row_template)
  have hs : D.sixTemplate = C.sixTemplate :=
    Fin.ext (Option.some.inj (D.six_eq.symm.trans C.row_six))
  exact mixed_case P hP C D.cells D.root D.classification (by
    simpa only [ht, hs] using D.coverage)

theorem two_six_of_certificate (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (C : SevenTwoSixCase P) (D : TwoSixCertificate C.template C.squarePyramids) :
    HasClassifiedEncoding P :=
  two_six_case P hP C D.cells D.root D.classification D.coverage

#print axioms pure_of_certificate
#print axioms mixed_of_certificate
#print axioms two_six_of_certificate

end Papers.RationalityTen.CompletedSeven
