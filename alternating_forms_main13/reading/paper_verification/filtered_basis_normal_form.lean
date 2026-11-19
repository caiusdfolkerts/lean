module

public import PaperVerification.FilteredBasisTransfer
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Filtration bounds and top coefficients of the actual lifted normal form

The normal form is defined using the already established basis of the
actual quotient. Bounded relation lifts prove that it respects the weight
filtration. At the greatest weight its coefficients agree with the actual
initial-quotient basis coefficients. These are conclusions about the
literal quotient maps, not triangular-normal-form assumptions.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.FilteredBasisTransfer

open PaperVerification.Fermion.BasisFiltered
open scoped BigOperators

variable {K M I E Q Q₀ : Type*} [Field K]
  [AddCommGroup M] [Module K M]
  [AddCommGroup Q] [Module K Q] [AddCommGroup Q₀] [Module K Q₀]
  (b : Module.Basis I K M) (w : I → ℕ)

/-- Bounded relation lifting yields a representative with the same bound
in the span of the actual homogeneous standard representatives. -/
theorem bounded_spanning (N N₀ : Submodule K M)
    (hlift : ∀ x∈N₀,∀ d,∃ y∈N,Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hspan : Submodule.span K (Set.range v)⊔N₀=⊤)
    (d : ℕ) (x : M) (hx : Bound b w d x) :
    ∃ z∈Submodule.span K (Set.range v),Bound b w d z ∧ x-z∈N := by
  have step (e : ℕ) (y : M) (hy : Bound b w e y) :
      ∃ u∈Submodule.span K (Set.range v),∃ a∈N,
        Bound b w e u ∧ Bound b w e a ∧ component b w e (y-u-a)=0 := by
    have hm : y∈Submodule.span K (Set.range v)⊔N₀ := by rw [hspan]; trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨a,ha,hab,hac⟩ := hlift j hj e
    refine ⟨component b w e u,component_mem_span b w v degree hv u hu e,
      a,ha,bound_component b w e u,hab,?_⟩
    have huu : component b w e (component b w e u)=component b w e u := by
      rw [component_of_homogeneous b w (homogeneous_component b w e u),if_pos rfl]
    rw [map_sub,map_sub,huu,hac,←huj,map_add]
    abel
  induction d generalizing x with
  | zero =>
      obtain ⟨u,hu,a,ha,hub,hab,hc⟩ := step 0 x hx
      have hz := eq_zero_of_bound_zero_component_zero b w
        (bound_sub b w (bound_sub b w hx hub) hab) hc
      exact ⟨u,hu,hub,by rw [sub_eq_zero.mp hz]; exact ha⟩
  | succ d ih =>
      obtain ⟨u,hu,a,ha,hub,hab,hc⟩ := step (d+1) x hx
      have hb : Bound b w d (x-u-a) := bound_pred_of_component_zero b w
        (bound_sub b w (bound_sub b w hx hub) hab) hc
      obtain ⟨z,hz,hzb,hr⟩ := ih (x-u-a) hb
      have he : x-(u+z)=a+((x-u-a)-z) := by abel
      refine ⟨u+z,Submodule.add_mem _ hu hz,
        bound_add b w hub (bound_mono b w (Nat.le_succ d) hzb),?_⟩
      rw [he]
      exact N.add_mem ha hr

variable (q : M →ₗ[K] Q) (v : E → M) (B : Module.Basis E K Q)

def normalRepresentative : M →ₗ[K] M :=
  (Finsupp.linearCombination K v).comp (B.repr.toLinearMap.comp q)

@[simp] theorem normalRepresentative_apply (x : M) :
    normalRepresentative q v B x=(B.repr (q x)).sum (fun e c => c • v e) := rfl

theorem normalRepresentative_generator (hB : ∀ e,B e=q (v e)) (e : E) :
    normalRepresentative q v B (v e)=v e := by
  rw [normalRepresentative_apply,←hB e,B.repr_self,Finsupp.sum_single_index,one_smul]
  exact zero_smul _ _

theorem normalRepresentative_eq_self (hB : ∀ e,B e=q (v e))
    (x : M) (hx : x∈Submodule.span K (Set.range v)) : normalRepresentative q v B x=x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨e,rfl⟩ := hx; exact normalRepresentative_generator q v B hB e
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy]
  | smul c x hx ih => rw [map_smul,ih]

theorem quotient_normalRepresentative (hB : ∀ e,B e=q (v e)) (x : M) :
    q (normalRepresentative q v B x)=q x := by
  rw [normalRepresentative_apply]
  simp only [Finsupp.sum,map_sum,map_smul,←hB]
  simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using
    B.linearCombination_repr (q x)

theorem normalRepresentative_bound
    (q₀ : M →ₗ[K] Q₀) (hq₀ : Function.Surjective q₀)
    (hlift : ∀ x,q₀ x=0 → ∀ d,∃ y,q y=0 ∧ Bound b w d y ∧
      component b w d y=component b w d x)
    (degree : E → ℕ) (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (hB : ∀ e,B e=q (v e)) (x : M) (d : ℕ) (hx : Bound b w d x) :
    Bound b w d (normalRepresentative q v B x) := by
  have hspan : Submodule.span K (Set.range v)⊔q₀.ker=⊤ := by
    apply (LinearMap.map_eq_top_iff (LinearMap.range_eq_top.mpr hq₀)).mp
    rw [Submodule.map_span,←Set.range_comp']
    simpa only [←hB₀] using B₀.span_eq
  obtain ⟨z,hz,hzb,hxz⟩ := bounded_spanning b w q.ker q₀.ker
    (fun y hy e => by
      obtain ⟨a,ha,hb,ht⟩ := hlift y (LinearMap.mem_ker.mp hy) e
      exact ⟨a,LinearMap.mem_ker.mpr ha,hb,ht⟩)
    v degree hv hspan d x hx
  have hq : q x=q z := by
    have h := LinearMap.mem_ker.mp hxz
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  have hn : normalRepresentative q v B x=normalRepresentative q v B z := by
    simp only [normalRepresentative_apply,hq]
  rw [hn,normalRepresentative_eq_self q v B hB z hz]
  exact hzb

theorem initial_coordinate_normalRepresentative
    (q₀ : M →ₗ[K] Q₀) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (x : M) (d : ℕ) (e : E) :
    B₀.repr (q₀ (component b w d (normalRepresentative q v B x))) e=
      if degree e=d then B.repr (q x) e else 0 := by
  classical
  rw [normalRepresentative_apply]
  simp only [Finsupp.sum,map_sum,map_smul]
  simp_rw [component_of_homogeneous b w (hv _)]
  simp only [apply_ite,map_zero,←hB₀,B₀.repr_self]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single e]
  · by_cases he : d=degree e <;> simp [he,eq_comm]
  · intro j hj hje
    by_cases hd : d=degree j <;> simp [hd,hje,Ne.symm hje]
  · intro he
    simp [Finsupp.notMem_support_iff.mp he]

/-- The top coefficient of the actual quotient normal form equals the
coefficient in the initial quotient, once the input bound is established. -/
theorem top_coefficient_eq
    (q₀ : M →ₗ[K] Q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (degree : E → ℕ) (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (hB : ∀ e,B e=q (v e)) (x : M) (d : ℕ)
    (hx : Bound b w d x) (hn : Bound b w d (normalRepresentative q v B x))
    (e : E) (he : degree e=d) :
    B.repr (q x) e=B₀.repr (q₀ (component b w d x)) e := by
  have hq : q (x-normalRepresentative q v B x)=0 := by
    rw [map_sub,quotient_normalRepresentative q v B hB,sub_self]
  have h := hinitial _ hq d (bound_sub b w hx hn)
  rw [map_sub,map_sub,sub_eq_zero] at h
  rw [h,initial_coordinate_normalRepresentative b w q v B q₀ degree hv B₀ hB₀ x d e,
    if_pos he]

/-- No coefficient of weight greater than the bound can occur. -/
theorem coefficient_eq_zero_of_bound
    (q₀ : M →ₗ[K] Q₀) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e))
    (x : M) (d : ℕ) (hn : Bound b w d (normalRepresentative q v B x))
    (e : E) (he : d<degree e) : B.repr (q x) e=0 := by
  have hz := component_eq_zero_of_bound_lt b w he hn
  have h := congrArg (fun z : M => B₀.repr (q₀ z) e) hz
  rw [initial_coordinate_normalRepresentative b w q v B q₀ degree hv B₀ hB₀,
    if_pos rfl,map_zero,map_zero,Finsupp.zero_apply] at h
  exact h

end PaperVerification.FilteredBasisTransfer
