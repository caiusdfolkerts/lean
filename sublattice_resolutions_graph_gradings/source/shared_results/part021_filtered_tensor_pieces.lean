module
public import graph_foundation.part014
public import shared_results.part021_integer_filtered_components

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredTensorPieces -/
section

/-! # Exact homogeneous coefficient pieces under the tensor symbol equivalence

This identifies every exterior-coordinate restriction, including internal,
auxiliary and homological degrees. The associated piece is proved to be
the coordinatewise associated coefficient piece. No grading labels are
silently substituted for the actual coefficient submodules.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FilteredTensorKoszul

open Classical CommAlg TensorExteriorKoszul IntegerFiltered
open scoped TensorProduct BigOperators

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V]

def coordinatePiece (Q : Finset V → Submodule K A) :
    Submodule K (Total (K:=K) (A:=A) (V:=V)) :=
  ⨅ s : Finset V,(Q s).comap (coefficient s)

theorem mem_coordinatePiece (Q : Finset V → Submodule K A)
    (x : Total (K:=K) (A:=A) (V:=V)) :
    x∈coordinatePiece Q ↔ ∀ s,coefficient s x∈Q s := by
  simp only [coordinatePiece,Submodule.mem_iInf,Submodule.mem_comap]

theorem tmul_basis_mem_coordinatePiece (Q : Finset V → Submodule K A)
    (s : Finset V) (a : A) (ha : a∈Q s) :
    a ⊗ₜ[K] Simplicial.basis s∈coordinatePiece Q := by
  rw [mem_coordinatePiece]
  intro t
  rw [coefficient_tmul_basis]
  split_ifs with h
  · subst t
    exact ha
  · exact (Q t).zero_mem

/-- The coordinate restrictions give the literal finite product of the
coefficient pieces. This proves finite dimensionality without assigning
an unexplained finite basis to the Koszul strand. -/
def coordinatePieceEquivPi (Q : Finset V → Submodule K A) :
    coordinatePiece Q ≃ₗ[K] ∀ s : Finset V,Q s where
  toFun x s := ⟨coefficient s x.val,(mem_coordinatePiece Q x.val).mp x.property s⟩
  invFun x := ⟨∑ s : Finset V,(x s).val ⊗ₜ[K] Simplicial.basis s,by
    apply Submodule.sum_mem
    intro s _
    exact tmul_basis_mem_coordinatePiece Q s (x s).val (x s).property⟩
  left_inv x := Subtype.ext (sum_coefficients x.val)
  right_inv x := by
    funext s
    apply Subtype.ext
    simp only [map_sum,coefficient_tmul_basis]
    simp
  map_add' x y := by
    funext s
    apply Subtype.ext
    exact map_add (coefficient s) x.val y.val
  map_smul' c x := by
    funext s
    apply Subtype.ext
    exact map_smul (coefficient s) c x.val

theorem coordinatePiece_finite (Q : Finset V → Submodule K A)
    [∀ s,Module.Finite K (Q s)] : Module.Finite K (coordinatePiece Q) :=
  Module.Finite.equiv (coordinatePieceEquivPi Q).symm

variable (F : MultiplicativeFiltration K A) (w : V → ℤ)

local notation "T" => filtration F w

theorem associatedLinear_coordinatePiece
    (Q : Finset V → Submodule K A) (z : (T).AssociatedGraded)
    (hz : z∈(T).associatedPiece (coordinatePiece Q)) :
    associatedLinear F w z∈coordinatePiece (fun s => F.associatedPiece (Q s)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨n,a,ha,rfl⟩ := hz
      rw [associatedLinear_symbol,levelSymbol_apply]
      apply Submodule.sum_mem
      intro s _
      apply tmul_basis_mem_coordinatePiece
      exact F.symbol_mem_associatedPiece (Q s) _ _ ((mem_coordinatePiece Q a.val).mp ha s)
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem insertSymbol_coordinatePiece
    (Q : Finset V → Submodule K A) (s : Finset V) (a : F.AssociatedGraded)
    (ha : a∈F.associatedPiece (Q s)) :
    insertSymbol F w s a∈(T).associatedPiece (coordinatePiece Q) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨n,b,hb,rfl⟩ := ha
      rw [insertSymbol_symbol]
      apply (T).symbol_mem_associatedPiece (coordinatePiece Q)
      exact tmul_basis_mem_coordinatePiece Q s b.val hb
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add a b ha hb iha ihb => simpa only [map_add] using Submodule.add_mem _ iha ihb
  | smul c a ha ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem associatedInverse_coordinatePiece
    (Q : Finset V → Submodule K A)
    (z : F.AssociatedGraded ⊗[K] Simplicial.Ambient V K)
    (hz : z∈coordinatePiece (fun s => F.associatedPiece (Q s))) :
    associatedInverse F w z∈(T).associatedPiece (coordinatePiece Q) := by
  rw [← sum_coefficients z,map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [associatedInverse_tmul_basis]
  exact insertSymbol_coordinatePiece F w Q s _ ((mem_coordinatePiece _ z).mp hz s)

/-- Each actual exterior coordinate passes to the actual associated
coefficient submodule. This applies in particular to every fixed-(q,m,p)
Koszul strand of an arbitrary bigraded algebra. -/
theorem associated_coordinatePiece (Q : Finset V → Submodule K A) :
    ((T).associatedPiece (coordinatePiece Q)).map (associatedAlgebraEquiv F w).toLinearMap =
      coordinatePiece (fun s => F.associatedPiece (Q s)) := by
  apply le_antisymm
  · rintro z ⟨a,ha,rfl⟩
    exact associatedLinear_coordinatePiece F w Q a ha
  · intro z hz
    exact ⟨associatedInverse F w z,associatedInverse_coordinatePiece F w Q z hz,
      associatedInverse_right F w z⟩

def associatedCoordinatePieceEquiv (Q : Finset V → Submodule K A) :
    (T).associatedPiece (coordinatePiece Q) ≃ₗ[K]
      coordinatePiece (fun s => F.associatedPiece (Q s)) :=
  (associatedAlgebraEquiv F w).toLinearEquiv.ofSubmodules _ _
    (associated_coordinatePiece F w Q)

end FourPapers.FilteredTensorKoszul

end
end
end


end
