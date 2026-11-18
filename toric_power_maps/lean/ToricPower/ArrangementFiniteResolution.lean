module

public import ToricPower.CellularConeResolution
public import ToricPower.ArrangementIncidenceCategory

/-!
# The finite resolution bound for actual arrangement diagrams

This module specializes the genuine projective resolution to the actual
translated incidence category, whose nonidentity arrows increase cell
dimension and whose object dimensions are bounded by the lattice rank.

Candidate source pending checking by the pinned Lean compiler.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

/-- In the actual translated incidence category, the `(n+1)`-st
syzygy is zero for every diagram, with arbitrary coefficient dimension. -/
theorem arrangementDiagramSyzygy_isZero (k : Type) [Field k]
    (F : IncidenceObject A ⥤ ModuleCat k) :
    IsZero ((Cellular.diagramSyzygyIterate k (n+1)).obj F) :=
  Cellular.diagramSyzygyIterate_isZero k (fun c : IncidenceObject A => c.1)
    (fun f => incidence_dimension_le A f)
    (fun f h => (incidence_eq_of_dimension_eq A f h).1) F n
    (fun c => cell_dimension_le A c.2.val)

/-- Every actual arrangement diagram has the displayed projective
resolution supported in degrees `0,…,n`, without any restriction on its
coefficient vector spaces. -/
theorem arrangementProjectiveResolution_bounded (k : Type) [Field k]
    (F : IncidenceObject A ⥤ ModuleCat k) (m : ℕ) (hm : n < m) :
    IsZero ((Cellular.diagramProjectiveResolution k F).complex.X m) :=
  Cellular.diagramProjectiveComplex_isZero_above k (fun c : IncidenceObject A => c.1)
    (fun f => incidence_dimension_le A f)
    (fun f h => (incidence_eq_of_dimension_eq A f h).1) F n m
    (fun c => cell_dimension_le A c.2.val) hm

/-- The finite cone augmentation is a quasi-isomorphism for every
genuinely unbounded complex of actual translated-incidence diagrams. -/
theorem arrangementFiniteConeResolution_quasiIso (k : Type) [Field k]
    (X : CochainComplex (IncidenceObject A ⥤ ModuleCat k) ℤ) :
    QuasiIso ((Cellular.finiteConeResolution k (n+1)).augmentation.app X) :=
  Cellular.finiteConeResolution_augmentation_quasiIso k
    (fun c : IncidenceObject A => c.1)
    (fun f => incidence_dimension_le A f)
    (fun f h => (incidence_eq_of_dimension_eq A f h).1) n
    (fun c => cell_dimension_le A c.2.val) X

end ToricPower.IntegralArrangement


end
