module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega
public import VolumeVerification.ConicCaratheodory
@[expose] public section
set_option autoImplicit false

/-!
# Measurable coefficients for a finitely generated cone

A finite family of linear left inverses is enough: enumerate the independent
supports, and choose the first inverse giving nonnegative coefficients and
the correct vector.  The candidate sets are closed.  Conic Caratheodory
supplies a successful support for every vector in the cone.
-/
namespace VolumeVerification.ConeSelection
open scoped BigOperators Classical
open Set MeasureTheory

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def combinationMap (v : ι → E) (s : Finset ι) : (s → ℝ) →ₗ[ℝ] E :=
  ∑ i : s, (LinearMap.proj i).smulRight (v i)

theorem combinationMap_apply (v : ι → E) (s : Finset ι) (c : s → ℝ) :
    combinationMap v s c = ∑ i : s, c i • v i := by
  simp [combinationMap]

noncomputable def coefficientMap (v : ι → E) (s : Finset ι) :
    E →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun i =>
    if h : i ∈ s then
      (LinearMap.proj (⟨i,h⟩ : s)).comp (combinationMap v s).leftInverse
    else 0

theorem coefficientMap_apply (v : ι → E) (s : Finset ι) (x : E) (i : ι) :
    coefficientMap v s x i =
      if h : i ∈ s then (combinationMap v s).leftInverse x ⟨i,h⟩ else 0 := by
  classical
  by_cases h : i ∈ s <;> simp [coefficientMap, h]

def Candidate (v : ι → E) (s : Finset ι) (x : E) : Prop :=
  (∀ i, 0 ≤ coefficientMap v s x i) ∧
    ∑ i, coefficientMap v s x i • v i = x

theorem candidate_isClosed (v : ι → E) (s : Finset ι) :
    IsClosed {x : E | Candidate v s x} := by
  have hc : Continuous (coefficientMap v s) :=
    (coefficientMap v s).continuous_of_finiteDimensional
  have hci : ∀ i, Continuous (fun x : E => coefficientMap v s x i) :=
    fun i => (continuous_apply i).comp hc
  have hsum : Continuous (fun x : E => ∑ i, coefficientMap v s x i • v i) :=
    continuous_finsetSum _ (fun i _ => (hci i).smul continuous_const)
  have he :
      {x : E | Candidate v s x} =
        (⋂ i, {x : E | 0 ≤ coefficientMap v s x i}) ∩
          {x : E | ∑ i, coefficientMap v s x i • v i = x} := by
    ext x
    simp [Candidate]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (hci i)).inter
    (isClosed_eq hsum continuous_id)

noncomputable def selectFrom (v : ι → E) : List (Finset ι) → E → (ι → ℝ)
  | [], _ => 0
  | s :: rest, x => if Candidate v s x then coefficientMap v s x else selectFrom v rest x

theorem selectFrom_measurable (v : ι → E) (supports : List (Finset ι)) :
    Measurable (selectFrom v supports) := by
  classical
  induction supports with
  | nil => exact measurable_const
  | cons s rest ih =>
      exact Measurable.ite (candidate_isClosed v s).measurableSet
        (coefficientMap v s).continuous_of_finiteDimensional.measurable ih

theorem selectFrom_nonnegative (v : ι → E) (supports : List (Finset ι)) :
    ∀ x i, 0 ≤ selectFrom v supports x i := by
  classical
  induction supports with
  | nil => intro x i; simp [selectFrom]
  | cons s rest ih =>
      intro x i
      by_cases h : Candidate v s x
      · simpa only [selectFrom, if_pos h] using h.1 i
      · simpa only [selectFrom, if_neg h] using ih x i

theorem selectFrom_reconstructs (v : ι → E) (supports : List (Finset ι)) (x : E)
    (hex : ∃ s ∈ supports, Candidate v s x) :
    ∑ i, selectFrom v supports x i • v i = x := by
  classical
  induction supports with
  | nil => simp at hex
  | cons s rest ih =>
      by_cases h : Candidate v s x
      · simpa only [selectFrom, if_pos h] using h.2
      · simp only [selectFrom, if_neg h]
        apply ih
        obtain ⟨t,ht,hvalid⟩ := hex
        rcases List.mem_cons.mp ht with rfl | ht
        · exact False.elim (h hvalid)
        · exact ⟨t,ht,hvalid⟩

noncomputable def selectionBound (v : ι → E) (supports : List (Finset ι)) : ℝ :=
  (supports.map fun s => ‖(coefficientMap v s).toContinuousLinearMap‖).sum

theorem selectionBound_nonnegative (v : ι → E) (supports : List (Finset ι)) :
    0 ≤ selectionBound v supports := by
  unfold selectionBound
  exact List.sum_nonneg fun x hx => by
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _

theorem selectFrom_norm_bound (v : ι → E) (supports : List (Finset ι)) (x : E) :
    ‖selectFrom v supports x‖ ≤ selectionBound v supports * ‖x‖ := by
  classical
  induction supports with
  | nil => simp [selectFrom, selectionBound]
  | cons s rest ih =>
      have hb := selectionBound_nonnegative v rest
      have hmap := norm_nonneg (coefficientMap v s).toContinuousLinearMap
      have hsplit : selectionBound v (s :: rest) =
          ‖(coefficientMap v s).toContinuousLinearMap‖ + selectionBound v rest := rfl
      rw [hsplit]
      by_cases h : Candidate v s x
      · simp only [selectFrom, if_pos h]
        exact ((coefficientMap v s).toContinuousLinearMap.le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))
      · simp only [selectFrom, if_neg h]
        exact ih.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))

theorem coefficientMap_eq_of_reduced (v : ι → E) (s : Finset ι)
    (c : ι → ℝ) (x : E)
    (hoff : ∀ i ∉ s, c i = 0)
    (hli : LinearIndepOn ℝ v (s : Set ι))
    (hsum : ∑ i ∈ s, c i • v i = x) :
    coefficientMap v s x = c := by
  classical
  have hinj : Function.Injective (combinationMap v s) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [combinationMap_apply] at ha
    funext i
    exact Fintype.linearIndependent_iff.mp hli a ha i
  have hker : (combinationMap v s).ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hs : combinationMap v s (fun i : s => c i) = x := by
    rw [combinationMap_apply]
    exact (Finset.sum_coe_sort s (fun i => c i • v i)).trans hsum
  have hleft := LinearMap.leftInverse_apply_of_inj hker (fun i : s => c i)
  rw [hs] at hleft
  funext i
  rw [coefficientMap_apply]
  by_cases hi : i ∈ s
  · rw [dif_pos hi]
    exact congrFun hleft ⟨i,hi⟩
  · rw [dif_neg hi, hoff i hi]

theorem exists_candidate (v : ι → E) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    ∃ s : Finset ι, Candidate v s (∑ i, c i • v i) := by
  classical
  obtain ⟨d,s,hd,hoff,hli,hsum⟩ :=
    ConicCaratheodory.conic_caratheodory v c hc
  have he := coefficientMap_eq_of_reduced v s d _ hoff hli hsum
  refine ⟨s, ?_⟩
  rw [Candidate, he]
  refine ⟨hd, ?_⟩
  have hfull : (∑ i ∈ s, d i • v i) = ∑ i, d i • v i := by
    apply Finset.sum_subset (Finset.subset_univ s)
    intro i _ hi
    rw [hoff i hi, zero_smul]
  rw [← hfull]
  exact hsum

noncomputable def select (v : ι → E) : E → (ι → ℝ) :=
  selectFrom v (Finset.univ : Finset (Finset ι)).toList

/-- One globally measurable, nonnegative selector, with a global linear bound.
Reconstruction holds at every point of the actual finitely generated cone. -/
theorem measurable_cone_coefficients (v : ι → E) :
    Measurable (select v) ∧
      (∀ x i, 0 ≤ select v x i) ∧
      (∀ x, (∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • v i = x) →
        ∑ i, select v x i • v i = x) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖select v x‖ ≤ C * ‖x‖ := by
  classical
  refine ⟨selectFrom_measurable v _, selectFrom_nonnegative v _, ?_, ?_⟩
  · rintro x ⟨c,hc,rfl⟩
    apply selectFrom_reconstructs
    obtain ⟨s,hs⟩ := exists_candidate v c hc
    exact ⟨s, by simp, hs⟩
  · exact ⟨selectionBound v _, selectionBound_nonnegative v _,
      selectFrom_norm_bound v _⟩

end VolumeVerification.ConeSelection

