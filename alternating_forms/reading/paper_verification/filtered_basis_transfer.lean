module

public import PaperVerification.FermionFilteredInitial
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Transferring an actual homogeneous quotient basis

Every leading relation is required to have a bounded lift in the actual
relation space. Descending weight proves spanning. Conversely, independence
is proved by taking the greatest weight with a nonzero coefficient in a
finite relation. Neither conclusion assumes a dimension comparison or an
isomorphism between the two quotients.
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

private theorem bound_sum (S : Finset E) (v : E → M) (d : ℕ)
    (h : ∀ e∈S,Bound b w d (v e)) : Bound b w d (∑ e∈S,v e) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using bound_zero b w d
  | @insert e S he ih =>
      rw [Finset.sum_insert he]
      exact bound_add b w (h e (Finset.mem_insert_self _ _))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Actual bounded lifts of every relation component suffice for spanning. -/
theorem spanning (N N₀ : Submodule K M)
    (hlift : ∀ x∈N₀,∀ d,∃ y∈N,Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hspan : Submodule.span K (Set.range v)⊔N₀=⊤) :
    Submodule.span K (Set.range v)⊔N=⊤ := by
  let C := Submodule.span K (Set.range v)⊔N
  have step (d : ℕ) (x : M) (hx : Bound b w d x) :
      ∃ z∈C,Bound b w d (x-z) ∧ component b w d (x-z)=0 := by
    have hm : x∈Submodule.span K (Set.range v)⊔N₀ := by rw [hspan]; trivial
    obtain ⟨u,hu,j,hj,huj⟩ := Submodule.mem_sup.mp hm
    obtain ⟨y,hy,hyb,hyc⟩ := hlift j hj d
    refine ⟨component b w d u+y,Submodule.add_mem C
      ((show Submodule.span K (Set.range v)≤C from le_sup_left)
        (component_mem_span b w v degree hv u hu d))
      ((show N≤C from le_sup_right) hy),
      bound_sub b w hx (bound_add b w (bound_component b w d u) hyb),?_⟩
    have hid : component b w d (component b w d u)=component b w d u := by
      rw [component_of_homogeneous b w (homogeneous_component b w d u),if_pos rfl]
    rw [map_sub,map_add,hid,hyc,←huj,map_add,sub_self]
  have hm : ∀ d x,Bound b w d x → x∈C := by
    intro d
    induction d with
    | zero =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step 0 x hx
        rw [sub_eq_zero.mp (eq_zero_of_bound_zero_component_zero b w hb hc)]
        exact hz
    | succ d ih =>
        intro x hx
        obtain ⟨z,hz,hb,hc⟩ := step (d+1) x hx
        have hr := ih (x-z) (bound_pred_of_component_zero b w hb hc)
        simpa only [sub_add_cancel] using C.add_mem hr hz
  apply top_unique
  intro x hx
  obtain ⟨d,hd⟩ := exists_bound b w x
  exact hm d x hd

private theorem independent_finite [Fintype E]
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hli : LinearIndependent K (fun e => q₀ (v e))) :
    LinearIndependent K (fun e => q (v e)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc e
  by_contra hce
  let S := (Finset.univ : Finset E).filter (fun i => c i≠0)
  have hS : S.Nonempty := ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hce⟩⟩
  obtain ⟨j,hj,hmax⟩ := S.exists_max_image degree hS
  have hcj : c j≠0 := (Finset.mem_filter.mp hj).2
  let x := ∑ i,c i • v i
  have hqx : q x=0 := by simpa only [x,map_sum,map_smul] using hc
  have hbound : Bound b w (degree j) x := by
    apply bound_sum b w
    intro i hi
    by_cases hci : c i=0
    · simpa only [hci,zero_smul] using bound_zero b w (degree j)
    · exact bound_smul b w
        (bound_mono b w (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hci⟩))
          (homogeneous_bound b w (hv i))) (c i)
  have ht := hinitial x hqx (degree j) hbound
  have he : q₀ (component b w (degree j) x)=
      ∑ i,(if degree j=degree i then c i else 0) • q₀ (v i) := by
    simp only [x,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [component_of_homogeneous b w (hv i)]
    split_ifs <;> simp only [map_zero,smul_zero,zero_smul]
  rw [he] at ht
  have hz := Fintype.linearIndependent_iff.mp hli
    (fun i => if degree j=degree i then c i else 0) ht j
  exact hcj (by simpa using hz)

/-- An infinite homogeneous family is independent after lifting whenever
its initial family is independent; only finite coefficient supports enter
the argument. -/
theorem independent
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (hli : LinearIndependent K (fun e => q₀ (v e))) :
    LinearIndependent K (fun e => q (v e)) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  exact independent_finite b w q q₀ hinitial
    (fun e : S => v e.val) (fun e : S => degree e.val) (fun e => hv e.val)
    (hli.comp (fun e : S => e.val) Subtype.val_injective)

/-- Construct the lifted basis in the actual target of the original
surjection. All relation and projection hypotheses concern those maps. -/
def basis
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (hlift : ∀ x,q₀ x=0 → ∀ d,∃ y,q y=0 ∧ Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e)) :
    Module.Basis E K Q := by
  have hli₀ : LinearIndependent K (fun e => q₀ (v e)) := by
    simpa only [←hB₀] using B₀.linearIndependent
  have hspan₀ : Submodule.span K (Set.range v)⊔q₀.ker=⊤ := by
    apply (LinearMap.map_eq_top_iff (LinearMap.range_eq_top.mpr hq₀)).mp
    rw [Submodule.map_span,←Set.range_comp']
    simpa only [←hB₀] using B₀.span_eq
  have hspan : Submodule.span K (Set.range v)⊔q.ker=⊤ :=
    spanning b w q.ker q₀.ker
      (fun x hx d => by
        obtain ⟨y,hy,hb,ht⟩ := hlift x (LinearMap.mem_ker.mp hx) d
        exact ⟨y,LinearMap.mem_ker.mpr hy,hb,ht⟩)
      v degree hv hspan₀
  have hsp : Submodule.span K (Set.range (fun e => q (v e)))=⊤ := by
    rw [Set.range_comp',←Submodule.map_span]
    exact (LinearMap.map_eq_top_iff (LinearMap.range_eq_top.mpr hq)).mpr hspan
  exact Module.Basis.mk (independent b w q q₀ hinitial v degree hv hli₀)
    (by rw [hsp])

@[simp] theorem basis_apply
    (q : M →ₗ[K] Q) (q₀ : M →ₗ[K] Q₀)
    (hq : Function.Surjective q) (hq₀ : Function.Surjective q₀)
    (hinitial : ∀ x,q x=0 → ∀ d,Bound b w d x → q₀ (component b w d x)=0)
    (hlift : ∀ x,q₀ x=0 → ∀ d,∃ y,q y=0 ∧ Bound b w d y ∧
      component b w d y=component b w d x)
    (v : E → M) (degree : E → ℕ)
    (hv : ∀ e,Homogeneous b w (degree e) (v e))
    (B₀ : Module.Basis E K Q₀) (hB₀ : ∀ e,B₀ e=q₀ (v e)) (e : E) :
    basis b w q q₀ hq hq₀ hinitial hlift v degree hv B₀ hB₀ e=q (v e) := by
  simp only [basis,Module.Basis.mk_apply]

end PaperVerification.FilteredBasisTransfer
