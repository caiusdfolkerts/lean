module
public import graph_results.grading_foundations
public import graph_foundation.part010
public import graph_foundation.part011

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FinePerturbationGrading -/
section

/-!
# Fine degrees in the actual perturbation formulas

The degree labels are arbitrary. If the original contraction and added
differential preserve each label on basis vectors, every transferred map
preserves it as well. The inverse used in the finite perturbation formula
is the actual inverse of the displayed operator; its compatibility follows
from commutation with the basis projections.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation.LinearContraction
open CommAlg

variable {R M H I J Γ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : LinearContraction (R := R) (M := M) (H := H))
  (b : Module.Basis I R M) (c : Module.Basis J R H)
  (degree : I → Γ) (degree' : J → Γ)
  (δ : Module.End R M) (u : (Module.End R M)ˣ)
  (hu : (u : Module.End R M) = 1 + δ * C.h)
  (hh : ∀ i, C.h (b i) ∈ Grading.Piece b degree (degree i))
  (hδ : ∀ i, δ (b i) ∈ Grading.Piece b degree (degree i))
  (hi : ∀ j, C.inclusion (c j) ∈ Grading.Piece b degree (degree' j))
  (hp : ∀ i, C.projection (b i) ∈ Grading.Piece c degree' (degree i))

include hu hh hδ in
theorem correction_mem_finePiece (q : Γ) (x : M)
    (hx : x ∈ Grading.Piece b degree q) :
    correction u δ x ∈ Grading.Piece b degree q := by
  have hhq : C.h * Grading.projection b degree q =
      Grading.projection b degree q * C.h :=
    shiftedProjection_commutes b b degree degree id Function.injective_id C.h hh q
  have hδq : δ * Grading.projection b degree q =
      Grading.projection b degree q * δ :=
    shiftedProjection_commutes b b degree degree id Function.injective_id δ hδ q
  have he := LinearMap.congr_fun
    (C.internalCorrection_commutes (Grading.projection b degree q) δ u hu hhq hδq) x
  change correction u δ (Grading.projection b degree q x) =
    Grading.projection b degree q (correction u δ x) at he
  rw [Grading.projection_eq_self hx] at he
  rw [he]
  exact Grading.projection_mem _ _ _ _

include hu hh hδ hi hp in
/-- Fine preservation of the literal transferred differential. -/
theorem transferredDifferential_mem_finePiece (q : Γ) (x : H)
    (hx : x ∈ Grading.Piece c degree' q) :
    C.transferredDifferential δ u x ∈ Grading.Piece c degree' q := by
  change C.projection (correction u δ (C.inclusion x)) ∈ _
  apply map_mem_piece_of_basis b c degree degree' C.projection hp q
  apply correction_mem_finePiece C b degree δ u hu hh hδ q
  exact map_mem_piece_of_basis c b degree' degree C.inclusion hi q hx

include hu hh hδ hi in
/-- Fine preservation of the literal transferred inclusion. -/
theorem transferredInclusion_mem_finePiece (q : Γ) (x : H)
    (hx : x ∈ Grading.Piece c degree' q) :
    C.transferredInclusion δ u x ∈ Grading.Piece b degree q := by
  have hix := map_mem_piece_of_basis c b degree' degree C.inclusion hi q hx
  have hax := correction_mem_finePiece C b degree δ u hu hh hδ q (C.inclusion x) hix
  have hhax := map_mem_piece_of_basis b b degree degree C.h hh q hax
  change C.inclusion x - C.h (correction u δ (C.inclusion x)) ∈ _
  exact Submodule.sub_mem _ hix hhax

include hu hh hδ hp in
/-- Fine preservation of the literal transferred projection. -/
theorem transferredProjection_mem_finePiece (q : Γ) (x : M)
    (hx : x ∈ Grading.Piece b degree q) :
    C.transferredProjection δ u x ∈ Grading.Piece c degree' q := by
  have hhx := map_mem_piece_of_basis b b degree degree C.h hh q hx
  have hahx := correction_mem_finePiece C b degree δ u hu hh hδ q (C.h x) hhx
  change C.projection (x - correction u δ (C.h x)) ∈ _
  exact map_mem_piece_of_basis b c degree degree' C.projection hp q
    (Submodule.sub_mem _ hx hahx)

include hu hh hδ in
/-- Fine preservation of the literal transferred homotopy. -/
theorem transferredHomotopy_mem_finePiece (q : Γ) (x : M)
    (hx : x ∈ Grading.Piece b degree q) :
    C.transferredHomotopy δ u x ∈ Grading.Piece b degree q := by
  have hhx := map_mem_piece_of_basis b b degree degree C.h hh q hx
  have hahx := correction_mem_finePiece C b degree δ u hu hh hδ q (C.h x) hhx
  have hhahx := map_mem_piece_of_basis b b degree degree C.h hh q hahx
  change C.h x - C.h (correction u δ (C.h x)) ∈ _
  exact Submodule.sub_mem _ hhx hhahx

end FourPapers.HomologicalPerturbation.LinearContraction

#print axioms FourPapers.HomologicalPerturbation.LinearContraction.transferredDifferential_mem_finePiece
#print axioms FourPapers.HomologicalPerturbation.LinearContraction.transferredInclusion_mem_finePiece
#print axioms FourPapers.HomologicalPerturbation.LinearContraction.transferredProjection_mem_finePiece
#print axioms FourPapers.HomologicalPerturbation.LinearContraction.transferredHomotopy_mem_finePiece

end
end
end

end
