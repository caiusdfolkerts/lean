module

public import Papers.GraphicalZonotopes.BookFunctionDecomposition

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

def minimizingOuters (F : J → SetFunction H) (u v : H) (X : Finset H) : Finset J:=
  univ.filter (fun j => delta (F j) u v X= -1)

@[simp] theorem mem_minimizingOuters (F : J → SetFunction H) (u v : H)
    (X : Finset H) (j : J) : j∈minimizingOuters F u v X ↔ delta (F j) u v X= -1 := by
  simp [minimizingOuters]

theorem minimizing_literal {F : SetFunction H} (hF : IsMonotoneBoolean F)
    (u v : H) (X : Finset H) :
    (if delta F u v X= -1 then delta F u v X else 0)= -negativeResponse F u v X := by
  rcases delta_values hF u v X with hd | hd | hd <;> norm_num [negativeResponse,hd]

theorem assembled_minimizer_zero {z : SetFunction H} {F : J → SetFunction H}
    (hF : ∀ j,IsMonotoneBoolean (F j)) {w : J → ℝ} (hc : Compatible z F w)
    (u v : H) (huv : u≠v) (X : Finset H) (hu : u∉X) (hv : v∉X) :
    delta (assembled z F w) (Sum.inl u) (Sum.inl v)
      (context X (minimizingOuters F u v X))=0 := by
  rw [delta_assembled_hubs,hubs_context,hc u v huv X hu hv]
  have he : (∑ j : J,w j*(if Sum.inr j∈context X (minimizingOuters F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,w j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOuters,minimizing_literal (hF j),mul_neg]
  rw [he,add_neg_cancel]

/-- Compatibility of a variation's central function is recovered from actual
global zero contexts, after the spoke equations have determined its scales. -/
theorem compatible_of_tight_variation {z h : SetFunction H} {F : J → SetFunction H}
    (hF : ∀ j,IsMonotoneBoolean (F j)) {w t : J → ℝ} (hc : Compatible z F w)
    (ht : ∀ u v,u≠v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta (assembled h F t) u v A=0) :
    Compatible h F t := by
  intro u v huv X hu hv
  have hz:=ht (Sum.inl u) (Sum.inl v) (fun he => huv (Sum.inl_injective he))
    (context X (minimizingOuters F u v X)) (by simpa using hu) (by simpa using hv)
    (assembled_minimizer_zero hF hc u v huv X hu hv)
  rw [delta_assembled_hubs,hubs_context] at hz
  have he : (∑ j : J,t j*(if Sum.inr j∈context X (minimizingOuters F u v X)
        then delta (F j) u v X else 0))= -(∑ j : J,t j*negativeResponse (F j) u v X) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj
    simp only [mem_context_outer,mem_minimizingOuters,minimizing_literal (hF j),mul_neg]
  rw [he] at hz
  linarith

/-- The actual integrability relation space, written without choosing a
quotient basis. A vector belongs to it precisely when its weighted response
has a normalized central set-function lift. -/
def UniqueIntegrableRelation (F : J → SetFunction H) (w : J → ℝ) : Prop :=
  ∀ t : J → ℝ,(∃ h : SetFunction H,TranslationNormalized h ∧ Compatible h F t) →
    ∃ c : ℝ,t=c • w

theorem compatible_central_unique {z h : SetFunction H}
    (hzn : TranslationNormalized z) (hhn : TranslationNormalized h)
    {F : J → SetFunction H} {w t : J → ℝ} (hz : Compatible z F w)
    (hh : Compatible h F t) {c : ℝ} (ht : t=c • w) : h=c • z := by
  have hn : TranslationNormalized (h-c • z) := by
    constructor
    · change h ∅-c*z ∅=0
      rw [hhn.1,hzn.1,mul_zero,sub_self]
    · intro a
      change h {a}-c*z {a}=0
      rw [hhn.2 a,hzn.2 a,mul_zero,sub_self]
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero hn
  intro u v huv X hu hv
  have he : delta h u v X=c*delta z u v X := by
    rw [hh u v huv X hu hv,hz u v huv X hu hv,mul_sum]
    apply sum_congr rfl
    intro j hj
    change t j*negativeResponse (F j) u v X=c*(w j*negativeResponse (F j) u v X)
    have htj:=congrFun ht j
    change t j=c*w j at htj
    rw [htj]
    ring
  rw [delta_sub,delta_smul,he,sub_self]

theorem assembled_smul (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (c : ℝ) :
    assembled (c • z) F (c • w)=c • assembled z F w := by
  unfold assembled
  rw [smul_add,Finset.smul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  change (c*w j) • branchLift j (F j)=c • (w j • branchLift j (F j))
  exact mul_smul _ _ _

/-- The whole normalized tight kernel, including all unused coordinates and
all nongraphical variations, is recovered from the positive response circuit. -/
theorem assembled_tight_kernel {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hc : Compatible z F w) (hrel : UniqueIntegrableRelation F w)
    (f : SetFunction (H⊕J)) (hf : TranslationNormalized f)
    (ht : ∀ u v,u≠v → ∀ A,u∉A → v∉A →
      delta (assembled z F w) u v A=0 → delta f u v A=0) :
    ∃ c : ℝ,f=c • assembled z F w := by
  have houter : OuterZero f := by
    intro i j hij A hi hj
    exact ht (Sum.inr i) (Sum.inr j) (fun he => hij (Sum.inr_injective he)) A hi hj
      (delta_assembled_outer z F w i j hij A hi hj)
  let t : J → ℝ:=fun j => privateSlice f j univ
  have hparts : ∀ j,privateSlice f j=t j • F j :=
    fun j => privateSlice_scalar_of_spokeZeros hF hf ht j
  have hrep:=eq_assembled_of_privateSlices houter F t hparts
  have ht' : Compatible (boundarySlice f) F t :=
    compatible_of_tight_variation hF hc (by
      intro u v huv A hu hv hzero
      rw [← hrep]
      exact ht u v huv A hu hv hzero)
  obtain ⟨c,hct⟩:=hrel t ⟨boundarySlice f,boundarySlice_normalized hf,ht'⟩
  have hb:=compatible_central_unique hz (boundarySlice_normalized hf) hc ht' hct
  exact ⟨c,by rw [hrep,hb,hct,assembled_smul]⟩

theorem assembled_at_hubs (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (X : Finset H) : assembled z F w (hubSet X)=z X := by
  simp [assembled,boundaryLift,branchLift,Finset.sum_apply]

theorem assembled_at_one_outer (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (j : J) (X : Finset H) :
    assembled z F w (insert (Sum.inr j) (hubSet X))=z X+w j*F j X := by
  simp [assembled,boundaryLift,branchLift,Finset.sum_apply]

theorem privateSlice_assembled (z : SetFunction H) (F : J → SetFunction H)
    (w : J → ℝ) (j : J) (X : Finset H) :
    privateSlice (assembled z F w) j X=w j*F j X := by
  rw [privateSlice,assembled_at_one_outer,assembled_at_hubs]
  ring

theorem assembled_ne_zero (z : SetFunction H) (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℝ) (hw : ∃ j,w j≠0) :
    assembled z F w≠0 := by
  obtain ⟨j,hj⟩:=hw
  intro he
  have hh:=privateSlice_assembled z F w j univ
  rw [he,(hF j).full,mul_one] at hh
  exact hj (by simpa only [privateSlice,Pi.zero_apply,sub_self] using hh.symm)

/-- Lemma7.3's extremality conclusion, proved directly from the actual
set-function zero rows and their complete integrability relation space. -/
theorem positive_circuit_extreme {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0≤w j) (hne : ∃ j,w j≠0)
    (hc : Compatible z F w) (hrel : UniqueIntegrableRelation F w) :
    ExtremeSupermodular (assembled z F w) := by
  apply extremeSupermodular_of_tightEquations
    (assembled_normalized hz F hF w) (assembled_supermodular z F hF w hw hc)
    (assembled_ne_zero z F hF w hne)
  exact assembled_tight_kernel hz hF hc hrel

end BooleanModule
end GraphicalZonotopes
