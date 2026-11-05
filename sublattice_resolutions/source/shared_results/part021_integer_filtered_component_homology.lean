module
public import graph_foundation.part014
public import shared_results.part021_filtered_tensor_pieces

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.IntegerFilteredComponentHomology -/
section

/-! # Actual associated-component homology and finite graded dimensions

The finite product of successive quotients is an explicit chain
coordinate change for the actual associated component, so its homology
dimension is the sum of the genuine successive-quotient homology
dimensions. This removes the abstract dimension expression from the
multiplicative degeneration criterion.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open Classical FilteredHomology
open scoped BigOperators

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x,x∈F.level n→D.d x∈F.level n)
  (hp : ∀ n x,x∈F.level n→D.parity x∈F.level n)

theorem associatedDifferential_symbol (n : ℤ) (a : F.level n) :
    (F.associatedDGA D hd hp).d (F.symbol n a)=
      F.symbol n ⟨D.d a.val,hd n a.val a.property⟩ := by
  change (F.associatedDGA D hd hp).d (F.leadingMap (F.monomial n a))=_
  rw [F.leadingMap_intertwines,F.reesDGA_d_monomial]
  rfl

variable (W U Z : Submodule K A)
  (hWU : ∀ x∈W,D.d x∈U) (hUZ : ∀ x∈U,D.d x∈Z)

def componentDifferentialBetween : W →ₗ[K] U :=
  (D.d.domRestrict W).codRestrict U (fun x => hWU x.val x.property)

theorem componentDifferentialBetween_comp :
    (componentDifferentialBetween D U Z hUZ).comp
      (componentDifferentialBetween D W U hWU)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact D.square_zero x.val

include hWU in
theorem associatedPiece_differential_mem (x : F.AssociatedGraded)
    (hx : x∈F.associatedPiece W) :
    (F.associatedDGA D hd hp).d x∈F.associatedPiece U := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨n,a,ha,rfl⟩ := hx
      rw [F.associatedDifferential_symbol D hd hp]
      exact F.symbol_mem_associatedPiece U n _ (hWU a.val ha)
  | zero => simpa only [map_zero] using (F.associatedPiece U).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (F.associatedPiece U).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (F.associatedPiece U).smul_mem c ih

def associatedPieceDifferential : F.associatedPiece W →ₗ[K] F.associatedPiece U :=
  ((F.associatedDGA D hd hp).d.domRestrict _).codRestrict _
    (fun x => F.associatedPiece_differential_mem D hd hp W U hWU x.val x.property)

@[simp] theorem associatedPieceDifferential_val (x : F.associatedPiece W) :
    (F.associatedPieceDifferential D hd hp W U hWU x).val=(F.associatedDGA D hd hp).d x.val := rfl

theorem associatedPieceDifferential_comp :
    (F.associatedPieceDifferential D hd hp U Z hUZ).comp
      (F.associatedPieceDifferential D hd hp W U hWU)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (F.associatedDGA D hd hp).square_zero x.val

abbrev associatedComponentHomology := Homology
  (F.associatedPieceDifferential D hd hp W U hWU)
  (F.associatedPieceDifferential D hd hp U Z hUZ)
  (F.associatedPieceDifferential_comp D hd hp W U Z hWU hUZ)

variable [FiniteDimensional K W] [FiniteDimensional K U] [FiniteDimensional K Z]
  (L : ℤ)
  (hLW : (F.level (L-1)).comap W.subtype=⊥)
  (hLU : (F.level (L-1)).comap U.subtype=⊥)
  (hLZ : (F.level (L-1)).comap Z.subtype=⊥)

local notation "GW" => F.componentFiltration W L hLW
local notation "GU" => F.componentFiltration U L hLU
local notation "GZ" => F.componentFiltration Z L hLZ

include hd in
theorem componentDifferentialBetween_preserves :
    Preserves GW GU (componentDifferentialBetween D W U hWU) := by
  intro n x hx
  exact hd (L+(n:ℤ)-1) x.val hx

theorem componentGradeSymbol_differential (n : ℕ) (x : FilteredHomology.Grade GW n) :
    F.componentGradeSymbol U L hLU n
      (gradeMap GW GU (componentDifferentialBetween D W U hWU)
        (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU) n x)=
      (F.associatedDGA D hd hp).d (F.componentGradeSymbol W L hLW n x) := by
  obtain ⟨a,rfl⟩ := (lowerInLevel GW n).mkQ_surjective x
  change F.componentGradeSymbol U L hLU n
      ((lowerInLevel GU n).mkQ
        (levelMap GW GU (componentDifferentialBetween D W U hWU)
          (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU) (n+1) a)) =
    (F.associatedDGA D hd hp).d
      (F.componentGradeSymbol W L hLW n ((lowerInLevel GW n).mkQ a))
  rw [F.componentGradeSymbol_mk,F.componentGradeSymbol_mk,
    F.associatedDifferential_symbol D hd hp]
  apply congrArg (F.symbol (L+(n:ℤ)))
  rfl

variable (N : ℕ)
  (hNW : (F.componentFiltration W L hLW).level N = (⊤ : Submodule K W))
  (hNU : (F.componentFiltration U L hLU).level N = (⊤ : Submodule K U))
  (hNZ : (F.componentFiltration Z L hLZ).level N = (⊤ : Submodule K Z))

theorem componentAssociatedEquiv_differential
    (x : ∀ n : Fin N,FilteredHomology.Grade GW n.val) :
    F.componentAssociatedEquiv U L hLU N hNU
      (componentwiseMap (fun n : Fin N => gradeMap GW GU
        (componentDifferentialBetween D W U hWU)
        (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU) n.val) x)=
      F.associatedPieceDifferential D hd hp W U hWU
        (F.componentAssociatedEquiv W L hLW N hNW x) := by
  apply Subtype.ext
  rw [F.componentAssociatedEquiv_val,F.associatedPieceDifferential_val,
    F.componentAssociatedEquiv_val,F.componentGradedSum_apply,F.componentGradedSum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact F.componentGradeSymbol_differential D hd hp W U hWU L hLW hLU n.val (x n)

/-- The actual associated-component homology is the finite product of the
actual successive-quotient homologies. This compares literal cycle and
boundary quotients, not only their dimensions. -/
def componentAssociatedHomologyEquivPi :
    F.associatedComponentHomology D hd hp W U Z hWU hUZ ≃ₗ[K]
      ∀ n : Fin N,GradedHomology GW GU GZ
        (componentDifferentialBetween D W U hWU) (componentDifferentialBetween D U Z hUZ)
        (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU)
        (F.componentDifferentialBetween_preserves D hd U Z hUZ L hLU hLZ)
        (componentDifferentialBetween_comp D W U Z hWU hUZ) n.val := by
  let f := fun n : Fin N => gradeMap GW GU (componentDifferentialBetween D W U hWU)
    (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU) n.val
  let g := fun n : Fin N => gradeMap GU GZ (componentDifferentialBetween D U Z hUZ)
    (F.componentDifferentialBetween_preserves D hd U Z hUZ L hLU hLZ) n.val
  let hfg := fun n : Fin N => gradeMap_comp GW GU GZ
    (componentDifferentialBetween D W U hWU) (componentDifferentialBetween D U Z hUZ)
    (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU)
    (F.componentDifferentialBetween_preserves D hd U Z hUZ L hLU hLZ)
    (componentDifferentialBetween_comp D W U Z hWU hUZ) n.val
  refine (threeTermHomologyEquiv
    (componentwiseMap f) (componentwiseMap g) (componentwiseMap_comp f g hfg)
    (F.associatedPieceDifferential D hd hp W U hWU)
    (F.associatedPieceDifferential D hd hp U Z hUZ)
    (F.associatedPieceDifferential_comp D hd hp W U Z hWU hUZ)
    (F.componentAssociatedEquiv W L hLW N hNW)
    (F.componentAssociatedEquiv U L hLU N hNU)
    (F.componentAssociatedEquiv Z L hLZ N hNZ) ?_ ?_).symm.trans
      (componentwiseHomologyEquiv f g hfg)
  · exact F.componentAssociatedEquiv_differential D hd hp W U hWU L hLW hLU N hNW hNU
  · exact F.componentAssociatedEquiv_differential D hd hp U Z hUZ L hLU hLZ N hNU hNZ

include hNW hNU hNZ in
theorem associatedComponentHomology_finrank :
    Module.finrank K (F.associatedComponentHomology D hd hp W U Z hWU hUZ)=
      ∑ n∈Finset.range N,Module.finrank K (GradedHomology GW GU GZ
        (componentDifferentialBetween D W U hWU) (componentDifferentialBetween D U Z hUZ)
        (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU)
        (F.componentDifferentialBetween_preserves D hd U Z hUZ L hLU hLZ)
        (componentDifferentialBetween_comp D W U Z hWU hUZ) n) := by
  rw [(F.componentAssociatedHomologyEquivPi D hd hp W U Z hWU hUZ
    L hLW hLU hLZ N hNW hNU hNZ).finrank_eq,Module.finrank_pi_fintype]
  exact Fin.sum_univ_eq_sum_range (fun n : ℕ => Module.finrank K (GradedHomology GW GU GZ
    (componentDifferentialBetween D W U hWU) (componentDifferentialBetween D U Z hUZ)
    (F.componentDifferentialBetween_preserves D hd W U hWU L hLW hLU)
    (F.componentDifferentialBetween_preserves D hd U Z hUZ L hLU hLZ)
    (componentDifferentialBetween_comp D W U Z hWU hUZ) n)) N

end FourPapers.IntegerFiltered.MultiplicativeFiltration

namespace FourPapers.IntegerFiltered.MultiplicativeFiltration

open FilteredHomology

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  (F : MultiplicativeFiltration K A) (D : ParityDifferential K A)
  (hd : ∀ n x,x∈F.level n→D.d x∈F.level n)
  (hp : ∀ n x,x∈F.level n→D.parity x∈F.level n)
  (W : Submodule K A) [FiniteDimensional K W]
  (hW : ∀ x∈W,D.d x∈W)

/-- Equality with the homology of the literal associated component is
equivalent to actual leading-cycle lifting in this finite component. -/
theorem relativeLiftsCycles_iff_actualAssociated :
    F.RelativeLiftsCycles D W ↔
      Module.finrank K (Homology (componentDifferential D W hW)
        (componentDifferential D W hW) (componentDifferential_square D W hW))=
      Module.finrank K (F.associatedComponentHomology D hd hp W W W hW hW) := by
  obtain ⟨L,hL,N,hN⟩ := F.exists_component_bounds W
  have hs := F.associatedComponentHomology_finrank D hd hp W W W hW hW
    L hL hL hL N hN hN hN
  constructor
  · intro hlift
    rw [hs]
    exact F.component_homology_dimension_eq_of_relative D hd W hW L hL N hN hlift
  · intro hdim
    apply F.relativeLiftsCycles_of_homology_dimension_eq D hd W hW L hL N hN
    exact hdim.trans hs

end FourPapers.IntegerFiltered.MultiplicativeFiltration

end
end
end


end
