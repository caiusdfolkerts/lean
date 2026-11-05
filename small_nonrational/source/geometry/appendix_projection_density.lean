module
public import Papers.DensityTheorems
public import Batches.B066
public import Batches.B143

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Named projection-density cases from Appendix B

The literal tables below specify both complete face families in the paper's
vertex labels. Equality with the existing terminal tables is checked in the
kernel. The density conclusion concerns every realization of the entire face
type, through `CertifiedRelabelling.rationallyDense`.
-/

noncomputable section
namespace Nonrational.AppendixProjectionDensity

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection
open Nonrational.TerminalData Nonrational.TerminalVerification

/-- Exact agreement with the complete facet and polygon families, up to labels. -/
def HasBoundaryType (P : ConvexPolytope 4) (B : Boundary 9) : Prop :=
  ∃ lab : Fin 10 ≃ VertexType P, RealizesBoundary P lab B

/-- Restore the paper's names after normalizing projection vertex 2 to zero. -/
def centerTwoLabels : Equiv.Perm (Fin 10) where
  toFun := ![2, 0, 1, 3, 4, 5, 6, 7, 8, 9]
  invFun := ![1, 2, 0, 3, 4, 5, 6, 7, 8, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Restore the paper's names after normalizing projection vertex 8 to zero. -/
def centerEightLabels : Equiv.Perm (Fin 10) where
  toFun := ![8, 0, 1, 2, 3, 4, 5, 6, 7, 9]
  invFun := ![1, 2, 3, 4, 5, 6, 7, 8, 0, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem dense_of_relabel {B T : Boundary 9}
    (C : CertifiedRelabelling T) (σ : Equiv.Perm (Fin 10))
    (hBT : B = T.relabel σ) (P : ConvexPolytope 4)
    (hP : P.IsFullDim) (h : HasBoundaryType P B) : RationallyDense P := by
  obtain ⟨lab, hB⟩ := h
  have hB' : RealizesBoundary P (σ.symm.symm.trans lab) T := by
    simpa only [hBT, Boundary.relabel_symm] using hB.relabel σ.symm
  exact C.rationallyDense hP _ hB'

/-- Complete labelled boundary of the Appendix B.5 three-prism type. -/
def threePrismBoundary : Boundary 9 where
  facets := {{0, 1, 2, 3, 7, 9},
    {0, 1, 2, 7, 8},
    {0, 1, 4, 5, 6, 9},
    {0, 1, 4, 5, 8},
    {0, 2, 3, 5, 6, 9},
    {0, 2, 5, 8},
    {1, 3, 7, 8, 9},
    {1, 4, 6, 8, 9},
    {2, 3, 5, 6, 7},
    {2, 4, 5, 7, 8},
    {3, 4, 6, 7, 8},
    {3, 6, 8, 9},
    {4, 5, 6, 7}}
  polygons := {{0, 1, 2, 7},
    {0, 1, 4, 5},
    {0, 1, 8},
    {0, 1, 9},
    {0, 2, 3, 9},
    {0, 2, 5},
    {0, 2, 8},
    {0, 5, 6, 9},
    {0, 5, 8},
    {1, 3, 7, 9},
    {1, 4, 6, 9},
    {1, 4, 8},
    {1, 7, 8},
    {1, 8, 9},
    {2, 3, 5, 6},
    {2, 3, 7},
    {2, 5, 7},
    {2, 5, 8},
    {2, 7, 8},
    {3, 6, 7},
    {3, 6, 8},
    {3, 6, 9},
    {3, 7, 8},
    {3, 8, 9},
    {4, 5, 6},
    {4, 5, 7},
    {4, 5, 8},
    {4, 6, 7},
    {4, 6, 8},
    {4, 7, 8},
    {5, 6, 7},
    {6, 8, 9}}

/-- Exact canonical terminal correspondence; both face families are compared. -/
theorem threePrism_matches_terminal :
    threePrismBoundary = (decode (targets 1981)).relabel centerTwoLabels := by
  apply Boundary.ext_faces <;> decide +kernel

/-- Appendix B.5 three-prism type: rational realizations are dense near every realization
of this complete combinatorial type. -/
theorem threePrism_rationallyDense (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (h : HasBoundaryType P threePrismBoundary) : RationallyDense P := by
  obtain ⟨C⟩ := projection_1981
  exact dense_of_relabel C centerTwoLabels threePrism_matches_terminal P hP h

/-- Complete labelled boundary of the Appendix B.8 type 444. -/
def residue444Boundary : Boundary 9 where
  facets := {{0, 1, 7, 8, 9},
    {0, 2, 4, 8, 9},
    {0, 3, 6, 7, 8},
    {0, 4, 5, 6, 8},
    {0, 4, 6, 7},
    {0, 4, 7, 9},
    {1, 2, 3, 5, 7},
    {1, 2, 3, 5, 9},
    {1, 2, 4, 7, 9},
    {1, 3, 6, 8, 9},
    {1, 3, 7, 8},
    {2, 4, 5, 7},
    {2, 4, 5, 8},
    {2, 5, 6, 8, 9},
    {3, 4, 5, 6, 7},
    {3, 5, 6, 9}}
  polygons := {{0, 4, 6},
    {0, 4, 7},
    {0, 4, 8},
    {0, 4, 9},
    {0, 6, 7},
    {0, 6, 8},
    {0, 7, 8},
    {0, 7, 9},
    {0, 8, 9},
    {1, 2, 3, 5},
    {1, 2, 7},
    {1, 2, 9},
    {1, 3, 7},
    {1, 3, 8},
    {1, 3, 9},
    {1, 7, 8},
    {1, 7, 9},
    {1, 8, 9},
    {2, 4, 5},
    {2, 4, 7},
    {2, 4, 8},
    {2, 4, 9},
    {2, 5, 7},
    {2, 5, 8},
    {2, 5, 9},
    {2, 8, 9},
    {3, 5, 6},
    {3, 5, 7},
    {3, 5, 9},
    {3, 6, 7},
    {3, 6, 8},
    {3, 6, 9},
    {3, 7, 8},
    {4, 5, 6},
    {4, 5, 7},
    {4, 5, 8},
    {4, 6, 7},
    {4, 7, 9},
    {5, 6, 8},
    {5, 6, 9},
    {6, 8, 9}}

/-- Exact canonical terminal correspondence; both face families are compared. -/
theorem residue444_matches_terminal :
    residue444Boundary = (decode (targets 4331)).relabel centerEightLabels := by
  apply Boundary.ext_faces <;> decide +kernel

/-- Appendix B.8 type 444: rational realizations are dense near every realization
of this complete combinatorial type. -/
theorem residue444_rationallyDense (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (h : HasBoundaryType P residue444Boundary) : RationallyDense P := by
  obtain ⟨C⟩ := projection_4331
  exact dense_of_relabel C centerEightLabels residue444_matches_terminal P hP h

/-- Complete labelled boundary of the Appendix B.8 type 446. -/
def residue446Boundary : Boundary 9 where
  facets := {{0, 1, 4, 8, 9},
    {0, 2, 5, 6, 8},
    {0, 3, 6, 8, 9},
    {0, 4, 5, 6},
    {0, 4, 5, 7, 8},
    {0, 4, 6, 9},
    {1, 2, 3, 7, 9},
    {1, 3, 4, 6, 7},
    {1, 3, 4, 6, 9},
    {1, 4, 7, 8},
    {1, 5, 7, 8, 9},
    {2, 3, 5, 8, 9},
    {2, 3, 6, 7},
    {2, 3, 6, 8},
    {2, 4, 5, 6, 7},
    {2, 5, 7, 9}}
  polygons := {{0, 4, 5},
    {0, 4, 6},
    {0, 4, 8},
    {0, 4, 9},
    {0, 5, 6},
    {0, 5, 8},
    {0, 6, 8},
    {0, 6, 9},
    {0, 8, 9},
    {1, 3, 4, 6},
    {1, 3, 7},
    {1, 3, 9},
    {1, 4, 7},
    {1, 4, 8},
    {1, 4, 9},
    {1, 7, 8},
    {1, 7, 9},
    {1, 8, 9},
    {2, 3, 6},
    {2, 3, 7},
    {2, 3, 8},
    {2, 3, 9},
    {2, 5, 6},
    {2, 5, 7},
    {2, 5, 8},
    {2, 5, 9},
    {2, 6, 7},
    {2, 6, 8},
    {2, 7, 9},
    {3, 6, 7},
    {3, 6, 8},
    {3, 6, 9},
    {3, 8, 9},
    {4, 5, 6},
    {4, 5, 7},
    {4, 6, 7},
    {4, 6, 9},
    {4, 7, 8},
    {5, 7, 8},
    {5, 7, 9},
    {5, 8, 9}}

/-- Exact canonical terminal correspondence; both face families are compared. -/
theorem residue446_matches_terminal :
    residue446Boundary = (decode (targets 4333)).relabel centerEightLabels := by
  apply Boundary.ext_faces <;> decide +kernel

/-- Appendix B.8 type 446: rational realizations are dense near every realization
of this complete combinatorial type. -/
theorem residue446_rationallyDense (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (h : HasBoundaryType P residue446Boundary) : RationallyDense P := by
  obtain ⟨C⟩ := projection_4333
  exact dense_of_relabel C centerEightLabels residue446_matches_terminal P hP h

#print axioms threePrism_rationallyDense
#print axioms residue444_rationallyDense
#print axioms residue446_rationallyDense

end Nonrational.AppendixProjectionDensity
