module

public import Papers.GraphicalZonotopes.SeparatorRows
public import Papers.GraphicalZonotopes.PolyhedralConeEquiv
public import Papers.GraphicalZonotopes.SeparatorCapacity

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Separator
open Finset
open scoped BigOperators
variable {V J : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The exact normalized graphical cone and the separated row model agree. -/
theorem rowData_nonnegative_iff_contextRows (h : Partition G B A) (x : Coordinates G B A) :
    Polyhedral.Nonnegative (rowData h).row x ↔
      Polyhedral.Nonnegative (contextRow G) (functionEquiv h x) :=
  (rowData_nonnegative_iff h x).trans
    (supermodular_iff_boundarySlacks_nonnegative G (functionEquiv h x))

theorem rowData_extreme_iff (h : Partition G B A) (x : Coordinates G B A) :
    Polyhedral.ExtremeRay (rowData h).row x ↔
      ExtremeSupermodular (globalFunctionMap h x) := by
  rw [Polyhedral.extremeRay_equiv (rowData h).row (contextRow G) (functionEquiv h)
    (rowData_nonnegative_iff_contextRows h)]
  exact (extremeSupermodular_iff_contextRows G (functionEquiv h x)).symm

theorem rowData_pointed (h : Partition G B A) : Polyhedral.Pointed (rowData h).row := by
  intro x hx
  have hp : Polyhedral.Nonnegative (rowData h).row x := fun r => (hx r).ge
  have hm : Polyhedral.Nonnegative (rowData h).row (-x) := by
    intro r
    rw [map_neg,hx r]
    simp
  have hp' := (rowData_nonnegative_iff_contextRows h x).mp hp
  have hm' := (rowData_nonnegative_iff_contextRows h (-x)).mp hm
  have hz : functionEquiv h x=0 := by
    apply contextRows_pointed G
    intro r
    have hneg := hm' r
    rw [map_neg,map_neg] at hneg
    exact le_antisymm (by linarith) (hp' r)
  exact (functionEquiv h).injective (hz.trans (map_zero _).symm)

/-- The boundary slack map used by the separator model is injective because
its rows determine every boundary coefficient through the original graphical
Möbius isomorphism. -/
theorem rowData_boundary_injective (h : Partition G B A) :
    Function.Injective (rowData h).boundary := by
  suffices hz : ∀ z,(rowData h).boundary z=0 → z=0 by
    intro z w he
    exact sub_eq_zero.mp (hz (z-w) (by rw [map_sub,he,sub_self]))
  intro z hz
  let f : graphicalFunctionSpace G := functionEquiv h (z,0)
  have hf : f=0 := by
    apply boundarySlackMap_eq_zero G
    funext r
    change delta (boundaryFunctionMap h z) r.1.1.1 r.1.1.2 r.2.1=0
    by_cases huB : r.1.1.1∈B
    · by_cases hvB : r.1.1.2∈B
      · let b : BoundaryRow G B := ⟨restrictContext r B,huB,hvB,inter_subset_right⟩
        have hb := congrFun hz b
        rw [delta_inter_mobius_support (boundaryFunction_supported h z)
          (ne_of_lt r.1.2.1) (context_left_not_mem r) (context_right_not_mem r)]
        exact hb
      · rw [delta_comm r.1.1.1]
        exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h z)
          (ne_of_gt r.1.2.1) hvB (context_right_not_mem r) (context_left_not_mem r)
    · exact delta_zero_of_outside_mobius_support (boundaryFunction_supported h z)
        (ne_of_lt r.1.2.1) huB (context_left_not_mem r) (context_right_not_mem r)
  have he : ((z,0) : Coordinates G B A)=0 :=
    (functionEquiv h).injective (hf.trans (map_zero _).symm)
  exact congrArg Prod.fst he

/-- The complete original graphical tight space is isomorphic to the
separated model's full tight space; no row has been removed from either cone. -/
def graphicalTightEquiv (h : Partition G B A) (x : Coordinates G B A)
    (hx : Polyhedral.Nonnegative (rowData h).row x) :
    Polyhedral.tightKernel (rowData h).row x ≃ₗ[ℝ]
      Polyhedral.tightKernel (contextRow G) (functionEquiv h x) :=
  Polyhedral.tightKernelEquiv (rowData h).row (contextRow G) (functionEquiv h)
    (rowData_nonnegative_iff_contextRows h) x hx

end Separator
end GraphicalZonotopes
