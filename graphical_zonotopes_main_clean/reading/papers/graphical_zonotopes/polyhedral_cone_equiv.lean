module

public import Papers.GraphicalZonotopes.PolyhedralCone

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Polyhedral
variable {E F I J : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F] [Fintype I] [Fintype J]
variable (A : I → E →ₗ[ℝ] ℝ) (B : J → F →ₗ[ℝ] ℝ) (e : E ≃ₗ[ℝ] F)
variable (hcone : ∀ x,Nonnegative A x ↔ Nonnegative B (e x))
include hcone

/-- A genuine linear equivalence of inequality cones preserves extreme rays,
independently of the chosen or repeated inequality presentations. -/
theorem extremeRay_equiv (x : E) : ExtremeRay A x ↔ ExtremeRay B (e x) := by
  constructor
  · intro hx
    refine ⟨(hcone x).mp hx.1,?_,?_⟩
    · intro he
      exact hx.2.1 (e.injective (he.trans (e.map_zero).symm))
    · intro u v hu hv he
      have hu' : Nonnegative A (e.symm u) := (hcone _).mpr (by simpa using hu)
      have hv' : Nonnegative A (e.symm v) := (hcone _).mpr (by simpa using hv)
      have he' : e.symm u+e.symm v=x := by
        apply e.injective
        simpa only [map_add,LinearEquiv.apply_symm_apply] using he
      obtain ⟨a,ha,heu⟩ := hx.2.2 _ _ hu' hv' he'
      refine ⟨a,ha,?_⟩
      simpa only [LinearEquiv.apply_symm_apply,map_smul] using congrArg e heu
  · intro hx
    refine ⟨(hcone x).mpr hx.1,?_,?_⟩
    · intro he
      exact hx.2.1 (by simp [he])
    · intro u v hu hv he
      obtain ⟨a,ha,heu⟩ := hx.2.2 (e u) (e v) ((hcone u).mp hu)
        ((hcone v).mp hv) (by rw [←map_add,he])
      exact ⟨a,ha,e.injective (by simpa only [map_smul] using heu)⟩

/-- Complete tight kernels are preserved by a cone equivalence. The proof
uses actual small two-sided perturbations, so no row-spanning assumption is
hidden in the equivalence of the inequality descriptions. -/
theorem tightKernel_equiv_mem {x v : E} (hx : Nonnegative A x) :
    v∈tightKernel A x ↔ e v∈tightKernel B (e x) := by
  have forward : ∀ {x v : E},Nonnegative A x → v∈tightKernel A x →
      e v∈tightKernel B (e x) := by
    intro x v hx hv
    obtain ⟨ε,hε,hp,hm⟩ := exists_two_sided_perturbation hx hv
    have hp' := (hcone _).mp hp
    have hm' := (hcone _).mp hm
    intro j hj
    have h1 := hp' j
    have h2 := hm' j
    simp only [map_add,map_sub,map_smul,smul_eq_mul,hj,mul_zero,zero_add,zero_sub] at h1 h2
    have he : ε * B j (e v)=0 := le_antisymm (by linarith) h1
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hε)
  constructor
  · exact forward hx
  · intro hv
    obtain ⟨ε,hε,hp,hm⟩ := exists_two_sided_perturbation ((hcone x).mp hx) hv
    have hp' : Nonnegative A ((1/2 : ℝ) • x+ε • v) :=
      (hcone _).mpr (by simpa only [map_add,map_smul] using hp)
    have hm' : Nonnegative A ((1/2 : ℝ) • x-ε • v) :=
      (hcone _).mpr (by simpa only [map_sub,map_smul] using hm)
    intro i hi
    have h1 := hp' i
    have h2 := hm' i
    simp only [map_add,map_sub,map_smul,smul_eq_mul,hi,mul_zero,zero_add,zero_sub] at h1 h2
    have he : ε * A i v=0 := le_antisymm (by linarith) h1
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hε)

/-- The exact linear isomorphism between complete tight spaces. -/
def tightKernelEquiv (x : E) (hx : Nonnegative A x) :
    tightKernel A x ≃ₗ[ℝ] tightKernel B (e x) where
  toFun v := ⟨e v,(tightKernel_equiv_mem A B e hcone hx).mp v.2⟩
  invFun w := ⟨e.symm w,(tightKernel_equiv_mem A B e hcone hx).mpr (by simpa using w.2)⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv w := Subtype.ext (e.apply_symm_apply w)
  map_add' v w := Subtype.ext (e.map_add v w)
  map_smul' a v := Subtype.ext (e.map_smul a v)

end Polyhedral
end GraphicalZonotopes
