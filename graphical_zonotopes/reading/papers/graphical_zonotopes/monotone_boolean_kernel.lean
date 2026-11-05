module

public import Papers.GraphicalZonotopes.SetFunction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The hub function in Section7.1. Every value, including all otherwise
unused private coordinates, remains part of the function space. -/
structure IsMonotoneBoolean (F : SetFunction V) : Prop where
  monotone : Monotone F
  values : ∀ S,F S=0 ∨ F S=1
  empty : F ∅=0
  full : F univ=1

def ZeroCoverKernel (F g : SetFunction V) : Prop :=
  g ∅=0 ∧ ∀ a S,a∉S → F (insert a S)-F S=0 → g (insert a S)-g S=0

/-- If the monotone function is constant at the endpoints of an interval,
the zero-cover equations make a variation constant throughout that interval. -/
theorem flat_interval {F g : SetFunction V} (hF : Monotone F)
    (hg : ZeroCoverKernel F g) {A B : Finset V} (hAB : A⊆B) (he : F A=F B) :
    g A=g B := by
  have hvalue : ∀ C,A⊆C → C⊆B → F C=F A := by
    intro C hAC hCB
    exact le_antisymm (by rw [he]; exact hF hCB) (hF hAC)
  have hstep : ∀ D : Finset V,A∪D⊆B → g (A∪D)=g A := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | @insert b D hb ih =>
      intro hsub
      rw [union_insert] at hsub ⊢
      have hsubD : A∪D⊆B:=fun x hx => hsub (mem_insert_of_mem hx)
      by_cases hbD : b∈A∪D
      · simpa only [insert_eq_of_mem hbD] using ih hsubD
      · have hzero : F (insert b (A∪D))-F (A∪D)=0 := by
          rw [hvalue _ (subset_union_left.trans (subset_insert _ _)) hsub,
            hvalue _ subset_union_left hsubD,sub_self]
        have hflat:=sub_eq_zero.mp (hg.2 b (A∪D) hbD hzero)
        exact hflat.trans (ih hsubD)
  have hu : A∪(B\A)=B:=union_sdiff_of_subset hAB
  have hh:=hstep (B\A) (by rw [hu])
  rw [hu] at hh
  exact hh.symm

/-- The full private spoke kernel is a line. No coefficient support or
nonzero-coordinate premise is imposed on the arbitrary variation `g`. -/
theorem zero_cover_kernel_line {F g : SetFunction V}
    (hF : IsMonotoneBoolean F) (hg : ZeroCoverKernel F g) :
    g=(g univ) • F := by
  funext S
  change g S=g univ*F S
  rcases hF.values S with hzero | hone
  · have he : F ∅=F S:=hF.empty.trans hzero.symm
    have hh:=flat_interval hF.monotone hg (empty_subset S) he
    rw [hg.1] at hh
    rw [hzero,mul_zero]
    exact hh.symm
  · have he : F S=F univ:=hone.trans hF.full.symm
    have hh:=flat_interval hF.monotone hg (subset_univ S) he
    simpa only [hone,mul_one] using hh

def privateKernel (F : SetFunction V) : Submodule ℝ (SetFunction V) where
  carrier := {g | ZeroCoverKernel F g}
  zero_mem' := by simp [ZeroCoverKernel]
  add_mem' := by
    intro g h hg hh
    refine ⟨by simp only [Pi.add_apply,hg.1,hh.1,add_zero],?_⟩
    intro a S ha hz
    have h1:=hg.2 a S ha hz
    have h2:=hh.2 a S ha hz
    change (g (insert a S)+h (insert a S))-(g S+h S)=0
    linarith
  smul_mem' := by
    intro c g hg
    refine ⟨by simp only [Pi.smul_apply,smul_eq_mul,hg.1,mul_zero],?_⟩
    intro a S ha hz
    have he:=hg.2 a S ha hz
    change c*g (insert a S)-c*g S=0
    rw [← mul_sub,he,mul_zero]

theorem self_mem_privateKernel {F : SetFunction V} (hF : IsMonotoneBoolean F) :
    F∈privateKernel F := ⟨hF.empty,fun _ _ _ h => h⟩

theorem privateKernel_eq_span {F : SetFunction V} (hF : IsMonotoneBoolean F) :
    privateKernel F=Submodule.span ℝ {F} := by
  apply le_antisymm
  · intro g hg
    exact Submodule.mem_span_singleton.mpr ⟨g univ,(zero_cover_kernel_line hF hg).symm⟩
  · apply Submodule.span_le.mpr
    intro g hg
    have he : g=F:=Set.mem_singleton_iff.mp hg
    subst g
    exact self_mem_privateKernel hF

theorem IsMonotoneBoolean.ne_zero {F : SetFunction V} (hF : IsMonotoneBoolean F) : F≠0 := by
  intro he
  have hh:=hF.full
  rw [he] at hh
  norm_num at hh

theorem privateKernel_finrank {F : SetFunction V} (hF : IsMonotoneBoolean F) :
    Module.finrank ℝ (privateKernel F)=1 := by
  rw [privateKernel_eq_span hF]
  exact finrank_span_singleton hF.ne_zero

theorem cover_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (a : V) (S : Finset V) : F (insert a S)-F S=0 ∨ F (insert a S)-F S=1 := by
  have hm:=hF.monotone (subset_insert a S)
  rcases hF.values S with h0 | h1 <;>
    rcases hF.values (insert a S) with hi0 | hi1 <;> simp_all <;> norm_num at *

theorem delta_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) :
    delta F u v S= -1 ∨ delta F u v S=0 ∨ delta F u v S=1 := by
  have h0:=hF.monotone (subset_insert u S)
  have h1:=hF.monotone (subset_insert v S)
  have h2:=hF.monotone (show insert u S⊆insert u (insert v S) from
    insert_subset_insert u (subset_insert v S))
  have h3:=hF.monotone (subset_insert u (insert v S))
  rcases hF.values S with hS | hS <;>
    rcases hF.values (insert u S) with hu | hu <;>
    rcases hF.values (insert v S) with hv | hv <;>
    rcases hF.values (insert u (insert v S)) with huv | huv <;>
    simp_all [delta] <;> norm_num at *

/-- The negative part of the literal central elemental response. -/
def negativeResponse (F : SetFunction V) (u v : V) (S : Finset V) : ℝ :=
  max 0 (-delta F u v S)

theorem negativeResponse_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) :
    negativeResponse F u v S=0 ∨ negativeResponse F u v S=1 := by
  rcases delta_values hF u v S with h | h | h <;>
    simp [negativeResponse,h]

theorem negativeResponse_eq_one_iff {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) :
    negativeResponse F u v S=1 ↔
      F S=0 ∧ F (insert u S)=1 ∧ F (insert v S)=1 := by
  have h0:=hF.monotone (subset_insert u S)
  have h1:=hF.monotone (subset_insert v S)
  have h2:=hF.monotone (show insert u S⊆insert u (insert v S) from
    insert_subset_insert u (subset_insert v S))
  have h3:=hF.monotone (subset_insert u (insert v S))
  rcases hF.values S with hS | hS <;>
    rcases hF.values (insert u S) with hu | hu <;>
    rcases hF.values (insert v S) with hv | hv <;>
    rcases hF.values (insert u (insert v S)) with huv | huv <;>
    simp_all [negativeResponse,delta] <;> norm_num at *

/-- Each summand in equation(7.1) is exactly a nonnegative zero-one literal
before multiplication by its positive branch scale. -/
theorem response_factor_values {F : SetFunction V} (hF : IsMonotoneBoolean F)
    (u v : V) (S : Finset V) (x : ℝ) (hx : x=0 ∨ x=1) :
    negativeResponse F u v S+x*delta F u v S=0 ∨
      negativeResponse F u v S+x*delta F u v S=1 := by
  rcases delta_values hF u v S with h | h | h <;>
    rcases hx with rfl | rfl <;> simp [negativeResponse,h]

end BooleanModule
end GraphicalZonotopes
