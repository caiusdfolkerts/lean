module

public import Papers.GraphicalZonotopes.MonotoneBooleanKernel
public import Papers.GraphicalZonotopes.Dilation
public import Papers.GraphicalZonotopes.GraphModels

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

theorem delta_swap (f : SetFunction (H⊕J)) (u v : H⊕J) (A : Finset (H⊕J)) :
    delta f u v A=delta f v u A := by
  unfold delta
  rw [insert_comm]
  ring

def hubs (A : Finset (H⊕J)) : Finset H:=univ.filter (fun a => Sum.inl a∈A)

@[simp] theorem mem_hubs (A : Finset (H⊕J)) (a : H) :
    a∈hubs A ↔ Sum.inl a∈A := by simp [hubs]

@[simp] theorem hubs_empty : hubs (∅ : Finset (H⊕J))=∅ := by ext a; simp

@[simp] theorem hubs_insert_hub (A : Finset (H⊕J)) (a : H) :
    hubs (insert (Sum.inl a) A)=insert a (hubs A) := by ext b; simp

@[simp] theorem hubs_insert_outer (A : Finset (H⊕J)) (j : J) :
    hubs (insert (Sum.inr j) A)=hubs A := by ext b; simp

def hubSet (A : Finset H) : Finset (H⊕J):=A.map ⟨Sum.inl,Sum.inl_injective⟩

@[simp] theorem mem_hubSet_hub (A : Finset H) (a : H) :
    Sum.inl a∈hubSet (J:=J) A ↔ a∈A := by simp [hubSet]

@[simp] theorem notMem_hubSet_outer (A : Finset H) (j : J) :
    Sum.inr j∉hubSet A := by simp [hubSet]

@[simp] theorem hubs_hubSet (A : Finset H) : hubs (hubSet (J:=J) A)=A := by ext a; simp

@[simp] theorem hubSet_insert (A : Finset H) (a : H) :
    hubSet (J:=J) (insert a A)=insert (Sum.inl a) (hubSet A) := by simp [hubSet]

@[simp] theorem hubSet_empty : hubSet (J:=J) (∅ : Finset H)=∅ := by simp [hubSet]

def boundaryLift (z : SetFunction H) : SetFunction (H⊕J):=fun A => z (hubs A)

def branchLift (j : J) (F : SetFunction H) : SetFunction (H⊕J):=
  fun A => if Sum.inr j∈A then F (hubs A) else 0

theorem boundaryLift_normalized {z : SetFunction H} (hz : TranslationNormalized z) :
    TranslationNormalized (boundaryLift (J:=J) z) := by
  refine ⟨?_,?_⟩
  · simpa only [Normalized,boundaryLift,hubs_empty] using hz.1
  · intro v
    cases v with
    | inl a => simpa only [boundaryLift,← insert_empty_eq,hubs_insert_hub,hubs_empty] using hz.2 a
    | inr j => simpa only [Normalized,boundaryLift,← insert_empty_eq,hubs_insert_outer,hubs_empty] using hz.1

theorem branchLift_normalized (j : J) {F : SetFunction H} (hF : F ∅=0) :
    TranslationNormalized (branchLift j F) := by
  constructor
  · simp [Normalized,branchLift]
  · intro v
    cases v <;> simp [branchLift,hubs,hF]

theorem delta_boundary_hubs (z : SetFunction H) (u v : H) (A : Finset (H⊕J)) :
    delta (boundaryLift z) (Sum.inl u) (Sum.inl v) A=delta z u v (hubs A) := by
  simp only [delta,boundaryLift,hubs_insert_hub]

theorem delta_boundary_spoke (z : SetFunction H) (u : H) (j : J) (A : Finset (H⊕J)) :
    delta (boundaryLift z) (Sum.inl u) (Sum.inr j) A=0 := by
  simp only [delta,boundaryLift,hubs_insert_hub,hubs_insert_outer]
  ring

theorem delta_boundary_outer (z : SetFunction H) (i j : J) (A : Finset (H⊕J)) :
    delta (boundaryLift z) (Sum.inr i) (Sum.inr j) A=0 := by
  simp only [delta,boundaryLift,hubs_insert_outer]
  ring

theorem delta_branch_hubs (j : J) (F : SetFunction H) (u v : H) (A : Finset (H⊕J)) :
    delta (branchLift j F) (Sum.inl u) (Sum.inl v) A=
      if Sum.inr j∈A then delta F u v (hubs A) else 0 := by
  by_cases hj : Sum.inr j∈A <;> simp [delta,branchLift,hj]

theorem delta_branch_spoke (i j : J) (F : SetFunction H) (u : H)
    (A : Finset (H⊕J)) (hj : Sum.inr j∉A) :
    delta (branchLift i F) (Sum.inl u) (Sum.inr j) A=
      if i=j then F (insert u (hubs A))-F (hubs A) else 0 := by
  by_cases hij : i=j
  · subst i
    simp [delta,branchLift,hj]
  · by_cases hi : Sum.inr i∈A <;> simp [delta,branchLift,hij,hi] <;> ring

theorem delta_branch_outer (k : J) (F : SetFunction H) (i j : J) (hij : i≠j)
    (A : Finset (H⊕J)) (hi : Sum.inr i∉A) (hj : Sum.inr j∉A) :
    delta (branchLift k F) (Sum.inr i) (Sum.inr j) A=0 := by
  by_cases hki : k=i
  · subst k
    simp [delta,branchLift,hij,hi]
  · by_cases hkj : k=j
    · subst k
      simp [delta,branchLift,Ne.symm hij,hj]
    · by_cases hk : Sum.inr k∈A <;> simp [delta,branchLift,hki,hkj,hk] <;> ring

def assembled (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ) :
    SetFunction (H⊕J) := boundaryLift z+∑ j : J,w j • branchLift j (F j)

theorem assembled_normalized {z : SetFunction H} (hz : TranslationNormalized z)
    (F : J → SetFunction H) (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℝ) :
    TranslationNormalized (assembled z F w) := by
  have hb:=boundaryLift_normalized (J:=J) hz
  have hp:=fun j => branchLift_normalized j (hF j).empty
  constructor
  · change boundaryLift z ∅+(∑ j : J,w j • branchLift j (F j)) ∅=0
    rw [Finset.sum_apply,hb.1,zero_add]
    apply sum_eq_zero
    intro j hj
    change w j*branchLift j (F j) ∅=0
    rw [(hp j).1,mul_zero]
  · intro v
    change boundaryLift z {v}+(∑ j : J,w j • branchLift j (F j)) {v}=0
    rw [Finset.sum_apply,hb.2 v,zero_add]
    apply sum_eq_zero
    intro j hj
    change w j*branchLift j (F j) {v}=0
    rw [(hp j).2 v,mul_zero]

theorem delta_assembled_spoke (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (u : H) (j : J) (A : Finset (H⊕J)) (hj : Sum.inr j∉A) :
    delta (assembled z F w) (Sum.inl u) (Sum.inr j) A=
      w j*(F j (insert u (hubs A))-F j (hubs A)) := by
  classical
  rw [assembled,delta_add,delta_boundary_spoke,zero_add,delta_sum]
  simp_rw [delta_smul,delta_branch_spoke _ _ _ _ _ hj]
  simp

theorem delta_assembled_outer (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (i j : J) (hij : i≠j) (A : Finset (H⊕J))
    (hi : Sum.inr i∉A) (hj : Sum.inr j∉A) :
    delta (assembled z F w) (Sum.inr i) (Sum.inr j) A=0 := by
  rw [assembled,delta_add,delta_boundary_outer,zero_add,delta_sum]
  apply sum_eq_zero
  intro k hk
  rw [delta_smul,delta_branch_outer _ _ _ _ hij _ hi hj,mul_zero]

theorem delta_assembled_hubs (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ)
    (u v : H) (A : Finset (H⊕J)) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v) A=
      delta z u v (hubs A)+∑ j : J,w j*(if Sum.inr j∈A then delta (F j) u v (hubs A) else 0) := by
  rw [assembled,delta_add,delta_boundary_hubs,delta_sum]
  simp_rw [delta_smul,delta_branch_hubs]

def Compatible (z : SetFunction H) (F : J → SetFunction H) (w : J → ℝ) : Prop :=
  ∀ u v,u≠v → ∀ S,u∉S → v∉S →
    delta z u v S=∑ j : J,w j*negativeResponse (F j) u v S

/-- Equation(7.1) is a literal equality for the genuine global set function. -/
theorem assembled_factorization (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (hc : Compatible z F w) (u v : H) (huv : u≠v)
    (A : Finset (H⊕J)) (hu : Sum.inl u∉A) (hv : Sum.inl v∉A) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v) A=
      ∑ j : J,w j*(negativeResponse (F j) u v (hubs A)+
        (if Sum.inr j∈A then 1 else 0)*delta (F j) u v (hubs A)) := by
  rw [delta_assembled_hubs,hc u v huv (hubs A) (by simpa using hu) (by simpa using hv),
    ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  by_cases hja : Sum.inr j∈A <;> simp only [hja,ite_true,ite_false,one_mul,zero_mul] <;> ring

theorem assembled_supermodular (z : SetFunction H) (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℝ) (hw : ∀ j,0≤w j)
    (hc : Compatible z F w) : Supermodular (assembled z F w) := by
  apply ElementallyNonnegative.supermodular
  intro a b hab A ha hb
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [assembled_factorization z F w hc u v (fun he => hab (congrArg Sum.inl he)) A ha hb]
      apply sum_nonneg
      intro j hj
      apply mul_nonneg (hw j)
      have hx : (if Sum.inr j∈A then (1 : ℝ) else 0)=0 ∨
          (if Sum.inr j∈A then (1 : ℝ) else 0)=1 := by split_ifs <;> simp
      rcases response_factor_values (hF j) u v (hubs A) _ hx with hval | hval <;> rw [hval] <;> norm_num
    | inr j =>
      rw [delta_assembled_spoke z F w u j A hb]
      exact mul_nonneg (hw j) (sub_nonneg.mpr ((hF j).monotone (subset_insert _ _)))
  | inr i =>
    cases b with
    | inl v =>
      rw [delta_swap,delta_assembled_spoke z F w v i A ha]
      exact mul_nonneg (hw i) (sub_nonneg.mpr ((hF i).monotone (subset_insert _ _)))
    | inr j =>
      rw [delta_assembled_outer z F w i j (fun he => hab (congrArg Sum.inr he)) A ha hb]

theorem assembled_graphical {s k : ℕ} (z : SetFunction (Fin s))
    (F : Fin k → SetFunction (Fin s)) (w : Fin k → ℝ) :
    Graphical (cliqueBook s k) (assembled z F w) := by
  intro a b hab hnon A ha hb
  cases a with
  | inl u => exact False.elim (hnon ⟨hab,Or.inl rfl⟩)
  | inr i =>
    cases b with
    | inl v => exact False.elim (hnon ⟨hab,Or.inr rfl⟩)
    | inr j =>
      exact delta_assembled_outer z F w i j
        (fun he => hab (congrArg Sum.inr he)) A ha hb

end BooleanModule
end GraphicalZonotopes
