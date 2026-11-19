module

public import Papers.GraphicalZonotopes.BookPositiveCircuit
public import Papers.GraphicalZonotopes.BookModuleGeometry

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

/-- Arbitrary monotone branch functions are allowed. Booleanity is needed
only in the earlier convenient sufficient criterion for private rigidity. -/
theorem assembled_normalized_general {z : SetFunction H} (hz : TranslationNormalized z)
    (F : J → SetFunction H) (hF : ∀ j,F j ∅=0) (w : J → ℝ) :
    TranslationNormalized (assembled z F w) := by
  have hb:=boundaryLift_normalized (J:=J) hz
  have hp:=fun j => branchLift_normalized j (hF j)
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

theorem response_factor_nonnegative (F : SetFunction H) (u v : H)
    (X : Finset H) (x : ℝ) (hx : x=0 ∨ x=1) :
    0≤negativeResponse F u v X+x*delta F u v X := by
  rcases hx with rfl | rfl
  · simp only [zero_mul,add_zero,negativeResponse]
    exact le_max_left _ _
  · simp only [one_mul,negativeResponse]
    have h:=le_max_right (0 : ℝ) (-delta F u v X)
    linarith

theorem assembled_supermodular_general (z : SetFunction H) (F : J → SetFunction H)
    (hF : ∀ j a X,0≤F j (insert a X)-F j X) (w : J → ℝ)
    (hw : ∀ j,0≤w j) (hc : Compatible z F w) :
    Supermodular (assembled z F w) := by
  apply ElementallyNonnegative.supermodular
  intro a b hab A ha hb
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [assembled_factorization z F w hc u v
        (fun he => hab (congrArg Sum.inl he)) A ha hb]
      apply sum_nonneg
      intro j hj
      apply mul_nonneg (hw j)
      apply response_factor_nonnegative
      split_ifs <;> simp
    | inr j =>
      rw [delta_assembled_spoke z F w u j A hb]
      exact mul_nonneg (hw j) (hF j u (hubs A))
  | inr i =>
    cases b with
    | inl v =>
      rw [delta_swap,delta_assembled_spoke z F w v i A ha]
      exact mul_nonneg (hw i) (hF i v (hubs A))
    | inr j =>
      rw [delta_assembled_outer z F w i j
        (fun he => hab (congrArg Sum.inr he)) A ha hb]

def minimizingOutersGeneral (F : J → SetFunction H) (u v : H)
    (X : Finset H) : Finset J := univ.filter (fun j => delta (F j) u v X<0)

@[simp] theorem mem_minimizingOutersGeneral (F : J → SetFunction H)
    (u v : H) (X : Finset H) (j : J) :
    j∈minimizingOutersGeneral F u v X ↔ delta (F j) u v X<0 := by
  simp [minimizingOutersGeneral]

theorem minimizing_general_literal (F : SetFunction H) (u v : H) (X : Finset H) :
    (if delta F u v X<0 then delta F u v X else 0)=
      -negativeResponse F u v X := by
  unfold negativeResponse
  by_cases h : delta F u v X<0
  · rw [if_pos h,max_eq_right (by linarith)]
    ring
  · rw [if_neg h,max_eq_left (by linarith),neg_zero]

theorem assembled_minimizer_zero_general {z : SetFunction H}
    {F : J → SetFunction H} {w : J → ℝ} (hc : Compatible z F w)
    (u v : H) (huv : u≠v) (X : Finset H) (hu : u∉X) (hv : v∉X) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v)
      (context X (minimizingOutersGeneral F u v X))=0 := by
  rw [delta_assembled_hubs,hubs_context,hc u v huv X hu hv]
  have he : (∑ j : J,w j*(if Sum.inr j∈context X (minimizingOutersGeneral F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,w j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOutersGeneral,minimizing_general_literal,mul_neg]
  rw [he,add_neg_cancel]

theorem compatible_of_tight_variation_general {z h : SetFunction H}
    {F : J → SetFunction H} {w t : J → ℝ} (hc : Compatible z F w)
    (ht : ∀ u v,u≠v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta (assembled h F t) u v A=0) :
    Compatible h F t := by
  intro u v huv X hu hv
  have hz:=ht (Sum.inl u) (Sum.inl v) (fun he => huv (Sum.inl_injective he))
    (context X (minimizingOutersGeneral F u v X)) (by simpa using hu) (by simpa using hv)
    (assembled_minimizer_zero_general hc u v huv X hu hv)
  rw [delta_assembled_hubs,hubs_context] at hz
  have he : (∑ j : J,t j*(if Sum.inr j∈context X (minimizingOutersGeneral F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,t j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOutersGeneral,minimizing_general_literal,mul_neg]
  rw [he] at hz
  linarith

theorem function_eq_private_assembly {f : SetFunction (H⊕J)} (hf : OuterZero f) :
    f=assembled (boundarySlice f) (privateSlice f) (fun _ => 1) := by
  apply eq_assembled_of_privateSlices hf
  intro j
  exact (one_smul ℝ _).symm

theorem delta_assembled_insert_outer (z : SetFunction H)
    (F : J → SetFunction H) (w : J → ℝ) (u v : H) (X : Finset H)
    (Y : Finset J) (j : J) (hj : j∉Y) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v) (context X (insert j Y))-
      delta (assembled z F w) (Sum.inl u) (Sum.inl v) (context X Y)=
        w j*delta (F j) u v X := by
  simp only [delta_assembled_hubs,hubs_context,mem_context_outer]
  have hsum : (∑ i : J,w i*(if i∈insert j Y then delta (F i) u v X else 0))=
      w j*delta (F j) u v X+∑ i : J,w i*(if i∈Y then delta (F i) u v X else 0) := by
    simp only [mul_ite,mul_zero]
    rw [← sum_filter,← sum_filter]
    have hY : (univ.filter (fun i => i∈Y))=Y := by ext i; simp
    have hI : (univ.filter (fun i => i∈insert j Y))=insert j Y := by ext i; simp
    rw [hI,hY,sum_insert hj]
  rw [hsum]
  ring

/-- These are precisely the local spoke equations and the differences of
minimizing boundary equations used by the non-Boolean modules of Section 8. -/
def PrivateRigid (F : SetFunction H) : Prop :=
  ∀ f : SetFunction H,f ∅=0 →
    (∀ a X,a∉X → F (insert a X)-F X=0 → f (insert a X)-f X=0) →
    (∀ u v,u≠v → ∀ X,u∉X → v∉X → delta F u v X=0 → delta f u v X=0) →
    ∃ c : ℝ,f=c • F

theorem privateSlice_scalar_general {z : SetFunction H}
    {F : J → SetFunction H} {w : J → ℝ} (hc : Compatible z F w)
    (hF : ∀ j,PrivateRigid (F j))
    {f : SetFunction (H⊕J)} (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) (j : J) :
    ∃ c : ℝ,privateSlice f j=c • F j := by
  have hout : OuterZero f := by
    intro i k hik A hi hk
    exact ht (Sum.inr i) (Sum.inr k) (fun he => hik (Sum.inr_injective he)) A hi hk
      (delta_assembled_outer z F w i k hik A hi hk)
  apply hF j (privateSlice f j) (privateSlice_empty hf j)
  · intro a X ha hz
    rw [privateSlice_cover]
    apply ht (Sum.inl a) (Sum.inr j) (by simp) (hubSet X)
      (by simpa using ha) (notMem_hubSet_outer X j)
    rw [delta_assembled_spoke _ _ _ _ _ _ (notMem_hubSet_outer X j),hubs_hubSet,hz,mul_zero]
  · intro u v huv X hu hv hz
    let Y:=minimizingOutersGeneral F u v X
    have hj : j∉Y := by simp [Y,hz]
    have hz0 := assembled_minimizer_zero_general hc u v huv X hu hv
    have hz1 : delta (assembled z F w) (Sum.inl u) (Sum.inl v)
        (context X (insert j Y))=0 := by
      have hdiff := delta_assembled_insert_outer z F w u v X Y j hj
      rw [hz,mul_zero] at hdiff
      change delta (assembled z F w) (Sum.inl u) (Sum.inl v) (context X Y)=0 at hz0
      linarith
    have hf0 := ht (Sum.inl u) (Sum.inl v)
      (fun he => huv (Sum.inl_injective he)) (context X Y)
      (by simpa using hu) (by simpa using hv) hz0
    have hf1 := ht (Sum.inl u) (Sum.inl v)
      (fun he => huv (Sum.inl_injective he)) (context X (insert j Y))
      (by simpa using hu) (by simpa using hv) hz1
    have hdiff := delta_assembled_insert_outer (boundarySlice f) (privateSlice f)
      (fun _ => 1) u v X Y j hj
    rw [←function_eq_private_assembly hout,hf0,hf1,sub_self,one_mul] at hdiff
    exact hdiff.symm

theorem assembled_tight_kernel_general {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} {w : J → ℝ} (hc : Compatible z F w)
    (hF : ∀ j,PrivateRigid (F j)) (hrel : UniqueIntegrableRelation F w)
    (f : SetFunction (H⊕J)) (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) :
    ∃ c : ℝ,f=c • assembled z F w := by
  have houter : OuterZero f := by
    intro i j hij A hi hj
    exact ht (Sum.inr i) (Sum.inr j) (fun he => hij (Sum.inr_injective he)) A hi hj
      (delta_assembled_outer z F w i j hij A hi hj)
  choose t htparts using privateSlice_scalar_general hc hF hf ht
  have hrep:=eq_assembled_of_privateSlices houter F t htparts
  have ht' : Compatible (boundarySlice f) F t :=
    compatible_of_tight_variation_general hc (by
      intro u v huv A hu hv hzero
      rw [← hrep]
      exact ht u v huv A hu hv hzero)
  obtain ⟨c,hct⟩:=hrel t ⟨boundarySlice f,boundarySlice_normalized hf,ht'⟩
  have hb:=compatible_central_unique hz (boundarySlice_normalized hf) hc ht' hct
  exact ⟨c,by rw [hrep,hb,hct,assembled_smul]⟩

theorem assembled_ne_zero_general (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (hne : ∃ j X,w j*F j X≠0) : assembled z F w≠0 := by
  obtain ⟨j,X,hj⟩:=hne
  intro he
  have hh:=privateSlice_assembled z F w j X
  rw [he] at hh
  exact hj (by simpa only [privateSlice,Pi.zero_apply,sub_self] using hh.symm)

theorem positive_circuit_extreme_general {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hzero : ∀ j,F j ∅=0)
    (hmono : ∀ j a X,0≤F j (insert a X)-F j X)
    (hrigid : ∀ j,PrivateRigid (F j))
    {w : J → ℝ} (hw : ∀ j,0≤w j) (hne : ∃ j X,w j*F j X≠0)
    (hc : Compatible z F w) (hrel : UniqueIntegrableRelation F w) :
    ExtremeSupermodular (assembled z F w) := by
  apply extremeSupermodular_of_tightEquations
    (assembled_normalized_general hz F hzero w)
    (assembled_supermodular_general z F hmono w hw hc)
    (assembled_ne_zero_general z F w hne)
  exact assembled_tight_kernel_general hz hc hrigid hrel

theorem IsMonotoneBoolean.privateRigid {F : SetFunction H} (hF : IsMonotoneBoolean F) :
    PrivateRigid F := by
  intro f hf hcover hdelta
  exact ⟨f univ,zero_cover_kernel_line hF ⟨hf,hcover⟩⟩

end BooleanModule
end GraphicalZonotopes
