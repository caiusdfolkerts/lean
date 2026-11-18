module

public import Papers.GraphicalZonotopes.SeparatorCapacity

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Gluing
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {B J D : Type*} {K I X : J → Type*}
variable [Fintype B] [Fintype J] [Fintype D]
variable [∀ j,Fintype (K j)] [∀ j,Fintype (I j)] [∀ j,Fintype (X j)]
variable [DecidableEq J]

abbrev ActiveBranch (f : ∀ j,K j → ℝ) := {j : J // f j≠0}
noncomputable instance activeBranchFintype (f : ∀ j,K j → ℝ) : Fintype (ActiveBranch f) := by
  classical
  infer_instance

def extendActiveScales (f : ∀ j,K j → ℝ) : (ActiveBranch f → ℝ) →ₗ[ℝ] (J → ℝ) where
  toFun c j := if hj : f j≠0 then c ⟨j,hj⟩ else 0
  map_add' c d := by
    funext j
    by_cases hj : f j=0 <;> simp [hj]
  map_smul' a c := by
    funext j
    by_cases hj : f j=0 <;> simp [hj]

@[simp] theorem extendActiveScales_active (f : ∀ j,K j → ℝ)
    (c : ActiveBranch f → ℝ) (j : ActiveBranch f) : extendActiveScales f c j=c j := by
  classical
  simp [extendActiveScales,j.2]

theorem sum_extendActiveScales (f : ∀ j,K j → ℝ) (c : ActiveBranch f → ℝ) (m : J → ℝ) :
    (∑ j : J,extendActiveScales f c j*m j)=∑ j : ActiveBranch f,c j*m j := by
  classical
  apply Finset.sum_congr_set {j : J | f j≠0}
  · intro j hj
    change f j ≠ 0 at hj
    simp [extendActiveScales,hj]
  · intro j hj
    change ¬f j ≠ 0 at hj
    simp [extendActiveScales,hj]

variable (M : Data B J K D I X) (f : ∀ j,K j → ℝ) (m : J → B → ℝ)

def activeClosureLinear : ((D → ℝ) × (ActiveBranch f → ℝ)) →ₗ[ℝ] (B → ℝ) where
  toFun y := M.boundary y.1 + responseLinear (fun j : ActiveBranch f => m j) y.2
  map_add' x y := by simp; abel
  map_smul' a x := by simp [smul_add]

variable (hmin : ∀ j b x,m j b≤M.response j b x (f j))
variable (hatt : ∀ j b,∃ x,M.response j b x (f j)=m j b)
variable (z : D → ℝ) (lam : J → ℝ) (hlam : ∀ j,0<lam j)
variable (hcone : Polyhedral.Nonnegative M.row (assemble z lam f))

/-- Only the nonzero private blocks are allowed independent scalar variations.
All boundary variables remain free, including when no private block is active. -/
def activeCapacityEmbedding : LinearMap.ker (activeClosureLinear M f m) →ₗ[ℝ]
    Polyhedral.tightKernel M.row (assemble z lam f) where
  toFun y := ⟨assemble y.1.1 (extendActiveScales f y.1.2) f,by
    intro r hr
    rcases r with ⟨j,i⟩ | ⟨b,x⟩
    · change M.internal j i (lam j • f j)=0 at hr
      rw [map_smul,smul_eq_mul] at hr
      have hi := (mul_eq_zero.mp hr).resolve_left (ne_of_gt (hlam j))
      change M.internal j i (extendActiveScales f y.1.2 j • f j)=0
      rw [map_smul,hi,smul_zero]
    · have hx := tight_boundary_uses_minima M f m hmin hatt z lam hlam hcone b x hr
      have he := congrFun (LinearMap.mem_ker.mp y.2) b
      change M.boundary y.1.1 b+(∑ j : ActiveBranch f,y.1.2 j*m j b)=0 at he
      rw [←sum_extendActiveScales f y.1.2 (fun j => m j b)] at he
      change M.boundary y.1.1 b+∑ j,M.response j b (x j)
        (extendActiveScales f y.1.2 j • f j)=0
      simpa only [map_smul,smul_eq_mul,hx] using he⟩
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble,add_smul]
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext j k
      simp [assemble,smul_smul,mul_assoc]

theorem activeCapacityEmbedding_injective :
    Function.Injective (activeCapacityEmbedding M f m hmin hatt z lam hlam hcone) := by
  intro x y hxy
  have he := congrArg Subtype.val hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun w : Global J K D => w.1) he
  · funext j
    have h := congrArg (fun w : Global J K D => w.2 j.1) he
    change extendActiveScales f x.1.2 j • f j=extendActiveScales f y.1.2 j • f j at h
    rw [extendActiveScales_active,extendActiveScales_active] at h
    obtain ⟨k,hk⟩ : ∃ k,f j k≠0 := by
      by_contra hn
      push_neg at hn
      exact j.2 (funext hn)
    have hh := congrFun h k
    simp only [Pi.smul_apply,smul_eq_mul] at hh
    exact mul_right_cancel₀ hk hh

include hmin hatt hlam in
/-- Full separator capacity, counting exactly the nonzero private blocks.
There is no hypothesis excluding zero blocks or requiring private rigidity. -/
theorem active_separator_capacity
    (hext : Polyhedral.ExtremeRay M.row (assemble z lam f)) :
    Fintype.card (ActiveBranch f)≤Fintype.card B-Fintype.card D+1 := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (activeCapacityEmbedding_injective M f m hmin hatt z lam hlam hext.1)
  rw [hext.tightKernel_eq_span,finrank_span_singleton hext.2.1] at hle
  have hnull := (activeClosureLinear M f m).ker.finrank_quotient_add_finrank
  rw [(activeClosureLinear M f m).quotKerEquivRange.finrank_eq,
    Module.finrank_prod,Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hnull
  have hrange := Submodule.finrank_le (activeClosureLinear M f m).range
  rw [Module.finrank_fintype_fun_eq_card] at hrange
  change Module.finrank ℝ (activeClosureLinear M f m).ker≤1 at hle
  omega

end Gluing
end GraphicalZonotopes
