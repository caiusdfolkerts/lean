module

public import PaperVerification.FermionFilteredModuleSpanning
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Initial relations from actual bounded reduction and independence

The initial submodule is defined from the leading components of the actual
relation submodule.  Bounded reduction proves that it equals the homogeneous
relations once the same representatives are independent in the deformed
quotient.  No equality of dimensions or initial ideals is assumed.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

open scoped BigOperators

variable {R M I J E Q : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q] (b : Module.Basis I R M) (w : I → ℕ)

theorem bound_mono {d e : ℕ} {x : M} (hde : d ≤ e) (hx : Bound b w d x) :
    Bound b w e x := fun i hi ↦ (hx i hi).trans hde

theorem component_eq_zero_of_bound_lt {d e : ℕ} {x : M}
    (hde : d < e) (hx : Bound b w d x) : component b w e x=0 := by
  apply b.repr.injective
  ext i
  rw [repr_component,map_zero,Finsupp.zero_apply]
  split_ifs with hi
  · by_contra hxi
    have hw := hx i hxi
    omega
  · rfl

def initialSubmodule (N : Submodule R M) : Submodule R M :=
  Submodule.span R {y | ∃ x ∈ N, ∃ d, Bound b w d x ∧ component b w d x=y}

/-- Reduction preserves the degree bound and explicitly tracks the leading
part of the actual relation used. -/
theorem bounded_representative
    (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤)
    (d : ℕ) (x : M) (hx : Bound b w d x) :
    ∃ z ∈ Submodule.span R (Set.range v), Bound b w d z ∧
      x-z ∈ Submodule.span R (Set.range f) ∧
      component b w d (x-z) ∈ Submodule.span R (Set.range g) := by
  have hg (j : J) : Homogeneous b w (degree j) (g j) := by
    rw [← (hf j).2]
    exact homogeneous_component b w _ _
  have step (e : ℕ) (y : M) (hy : Bound b w e y) :
      ∃ u ∈ Submodule.span R (Set.range v), ∃ a ∈ Submodule.span R (Set.range f),
        Bound b w e u ∧ Bound b w e a ∧
        component b w e (y-u-a)=0 ∧
        component b w e a ∈ Submodule.span R (Set.range g) := by
    have hm : y ∈ Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g) := by
      rw [hspan]
      trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨a,ha,hab,hac⟩ := relation_component_lifts b w f g degree hf j hj e
    refine ⟨component b w e u,component_mem_span b w v vdegree hv u hu e,a,ha,
      bound_component b w e u,hab,?_,?_⟩
    · have huu : component b w e (component b w e u)=component b w e u := by
        rw [component_of_homogeneous b w (homogeneous_component b w e u),if_pos rfl]
      rw [map_sub,map_sub,huu,hac,← huj,map_add]
      abel
    · rw [hac]
      exact component_mem_span b w g degree hg j hj e
  induction d generalizing x with
  | zero =>
      obtain ⟨u,hu,a,ha,hub,hab,hc,hg⟩ := step 0 x hx
      have hz := eq_zero_of_bound_zero_component_zero b w
        (bound_sub b w (bound_sub b w hx hub) hab) hc
      have he : x-u=a := sub_eq_zero.mp hz
      exact ⟨u,hu,hub,by rw [he]; exact ha,by rw [he]; exact hg⟩
  | succ d ih =>
      obtain ⟨u,hu,a,ha,hub,hab,hc,hg⟩ := step (d+1) x hx
      have hb : Bound b w d (x-u-a) :=
        bound_pred_of_component_zero b w
          (bound_sub b w (bound_sub b w hx hub) hab) hc
      obtain ⟨z,hz,hzb,hr,ht⟩ := ih (x-u-a) hb
      have he : x-(u+z)=a+((x-u-a)-z) := by abel
      refine ⟨u+z,Submodule.add_mem _ hu hz,
        bound_add b w hub (bound_mono b w (Nat.le_succ d) hzb),?_,?_⟩
      · rw [he]
        exact Submodule.add_mem _ ha hr
      · rw [he,map_add,component_eq_zero_of_bound_lt b w (Nat.lt_succ_self d)
          (bound_sub b w hb hzb),add_zero]
        exact hg

/-- The actual leading submodule equals the homogeneous relation submodule.
The proof uses the independent representatives, not a dimension assertion. -/
theorem initialSubmodule_eq_of_basis [Fintype E]
    (f g : J → M) (degree : J → ℕ)
    (hf : ∀ j, HasTop b w (degree j) (f j) (g j))
    (v : E → M) (vdegree : E → ℕ)
    (hv : ∀ e, Homogeneous b w (vdegree e) (v e))
    (hspan : Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range g)=⊤)
    (q : M →ₗ[R] Q) (hker : q.ker=Submodule.span R (Set.range f))
    (hli : LinearIndependent R (fun e ↦ q (v e))) :
    initialSubmodule b w q.ker=Submodule.span R (Set.range g) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨x,hx,d,hb,rfl⟩
    obtain ⟨z,hz,hzb,hr,ht⟩ := bounded_representative b w f g degree hf v vdegree hv hspan d x hb
    have hqz : q z=0 := by
      have hqr : q (x-z)=0 := by
        apply LinearMap.mem_ker.mp
        rwa [hker]
      rw [map_sub,LinearMap.mem_ker.mp hx,zero_sub,neg_eq_zero] at hqr
      exact hqr
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hz
    have hzero : ∑ e, c e • q (v e)=0 := by
      simpa only [map_sum,map_smul] using (congrArg q hc).trans hqz
    have hcoef := Fintype.linearIndependent_iff.mp hli c hzero
    have hz0 : z=0 := by
      rw [← hc]
      simp only [hcoef,zero_smul,Finset.sum_const_zero]
    change component b w d x ∈ Submodule.span R (Set.range g)
    simpa only [hz0,sub_zero] using ht
  · apply Submodule.span_le.mpr
    rintro y ⟨j,rfl⟩
    apply Submodule.subset_span
    refine ⟨f j,?_,degree j,(hf j).1,(hf j).2⟩
    rw [hker]
    exact Submodule.subset_span ⟨j,rfl⟩

end PaperVerification.Fermion.BasisFiltered
