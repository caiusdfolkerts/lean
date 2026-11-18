module

public import ToricPower.CellularHomotopyInverseComparison
public import ToricPower.DerivedKProjectiveCompactness
public import ToricPower.BoundedComplexCoproductCompact
public import ToricPower.FiniteDiagramCoproductCompact
public import ToricPower.DiagramDerivedCoproducts

/-!
# Actual compactness of the finite homotopy inverse-Nakayama functor

The comparison is with a bounded complex of genuinely finite-dimensional
projective diagrams. Compactness is measured against all coproducts in
the original unbounded derived category.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex

namespace ToricPower.Cellular
open CompactExtraction

universe u w
variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]
  [Finite C] [∀ c d : C, Finite (c ⟶ d)]
  [∀ c : C, Subsingleton (c ⟶ c)]
  [HasDerivedCategory.{w} (C ⥤ ModuleCat.{u} k)]
variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  (N : ℕ) (bound : ∀ c, grade c ≤ N)

theorem finiteHomotopyInverseNakayama_coproductCompact
    (G : FiniteDerivedDiagrams k (C := C)) :
    letI := diagramDerived_hasCoproducts k grade grade_le eq_of_grade_eq N bound
    CoproductCompact.{u+1,w,u} ((finiteInverseNakayama k).obj G) := by
  letI := diagramDerived_hasCoproducts k grade grade_le eq_of_grade_eq N bound
  let M := finiteChosenModel k G
  have compactComplex : CoproductCompact.{u+1,u,u} M.sealedInverseComplex :=
    boundedComplex_coproductCompact M.sealedInverseComplex M.lower M.upper
      (fun q => finiteDiagram_coproductCompact k (M.sealedInverseComplex.X q))
  have compactDerived := derived_coproductCompact_of_kProjective
    (diagramDerived_kProjective_representative k grade grade_le eq_of_grade_eq N bound)
    M.sealedInverseComplex compactComplex
  exact coproductCompact_of_iso (finiteInversePairingModelIso k G).symm compactDerived

end ToricPower.Cellular
end
