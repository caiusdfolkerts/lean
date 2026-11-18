module
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section

open Matrix Module Set Filter Topology
open scoped BigOperators

namespace Papers.RationalityTen.ChirotopeDensity

def Spans {n r : ℕ} (p : Fin n → Fin r → ℝ) : Prop :=
  Submodule.span ℝ (Set.range p) = ⊤

def subsetRank {n r : ℕ} (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) : ℕ :=
  finrank ℝ (Submodule.span ℝ (p '' (↑S : Set (Fin n))))

@[simp] theorem subsetRank_empty {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    subsetRank p ∅ = 0 := by
  unfold subsetRank
  have hs : p '' (↑(∅ : Finset (Fin n)) : Set (Fin n)) = ∅ := by
    ext x
    simp
  rw [hs, Submodule.span_empty]
  exact finrank_bot ℝ (Fin r → ℝ)

theorem spans_iff_matrix_rank {n r : ℕ} (p : Fin n → Fin r → ℝ) :
    Spans p ↔ Matrix.rank (Matrix.of p) = r := by
  rw [Matrix.rank_eq_finrank_span_row]
  change Submodule.span ℝ (Set.range p) = ⊤ ↔
    finrank ℝ (Submodule.span ℝ (Set.range p)) = r
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa using h

theorem subsetRank_univ {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (hp : Spans p) :
    subsetRank p Finset.univ=r := by
  unfold subsetRank
  rw [Finset.coe_univ,Set.image_univ]
  rw [show Submodule.span ℝ (Set.range p)=⊤ from hp]
  simp

def maskRows {c r : ℕ} (p : Fin c → Fin r → ℝ) (S : Finset (Fin c)) :
    Matrix (Fin c) (Fin r) ℝ :=
  fun i => if i∈S then p i else 0

theorem maskRows_span {c r : ℕ}
    (p : Fin c → Fin r → ℝ) (S : Finset (Fin c)) :
    Submodule.span ℝ (Set.range (maskRows p S)) =
      Submodule.span ℝ (p '' (↑S : Set (Fin c))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hi : i∈S
    · simpa [maskRows,hi] using
        (Submodule.subset_span (s := p '' (↑S : Set (Fin c))) ⟨i,hi,rfl⟩)
    · simp [maskRows,hi]
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change i ∈ S at hi
    apply Submodule.subset_span
    exact ⟨i,by simp [maskRows,hi]⟩

theorem maskRows_rank {c r : ℕ}
    (p : Fin c → Fin r → ℝ) (S : Finset (Fin c)) :
    (maskRows p S).rank=subsetRank p S := by
  rw [Matrix.rank_eq_finrank_span_row]
  change finrank ℝ (Submodule.span ℝ (Set.range (maskRows p S))) = _
  rw [maskRows_span]
  rfl

theorem maskRows_continuous {c r : ℕ} (S : Finset (Fin c)) :
    Continuous (fun p : Fin c → Fin r → ℝ => maskRows p S) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i∈S
  · simpa [maskRows,hi] using (continuous_apply i : Continuous
      (fun p : Fin c → Fin r → ℝ => p i))
  · simpa [maskRows,hi] using
      (continuous_const : Continuous (fun _ : Fin c → Fin r → ℝ => (0 : Fin r → ℝ)))

def dotLinear {r : ℕ} (a : Fin r → ℝ) : (Fin r → ℝ) →ₗ[ℝ] ℝ where
  toFun x := a ⬝ᵥ x
  map_add' x y := dotProduct_add _ _ _
  map_smul' c x := by
    simp [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_comm,mul_left_comm]

/-- A subset lies in a supporting homogeneous hyperplane with a
nonzero normal. The unit norm is only a compact normalisation. -/
def SupportingSubset {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) : Prop :=
  ∃ a : Fin r → ℝ, ‖a‖=1 ∧
    (∀ i, 0 ≤ a ⬝ᵥ p i) ∧ (∀ i∈S, a ⬝ᵥ p i=0)

/-- Exact zero and strict-positive signs at all labelled points. -/
def StrictSupport {n r : ℕ} (p : Fin n → Fin r → ℝ)
    (S : Finset (Fin n)) (a : Fin r → ℝ) : Prop :=
  (∀ i∈S, a ⬝ᵥ p i=0) ∧ (∀ i∉S, 0<a ⬝ᵥ p i)

theorem dotProduct_continuousAt {T : Type*} [TopologicalSpace T]
    {r : ℕ} {f g : T → Fin r → ℝ} {t : T}
    (hf : ContinuousAt f t) (hg : ContinuousAt g t) :
    ContinuousAt (fun x => f x ⬝ᵥ g x) t := by
  have h : Continuous
      (fun z : (Fin r → ℝ) × (Fin r → ℝ) => z.1 ⬝ᵥ z.2) :=
    continuous_fst.dotProduct continuous_snd
  exact h.continuousAt.comp (hf.prodMk hg)

theorem maskRows_mulVec_zero_iff {n r : ℕ}
    (p : Fin n → Fin r → ℝ) (S : Finset (Fin n)) (a : Fin r → ℝ) :
    (maskRows p S).mulVec a=0 ↔ ∀ i∈S, a ⬝ᵥ p i=0 := by
  classical
  constructor
  · intro h i hi
    have hh := congrFun h i
    simpa [maskRows,hi,Matrix.mulVec,dotProduct,mul_comm] using hh
  · intro h
    ext i
    by_cases hi : i∈S
    · simpa [maskRows,hi,Matrix.mulVec,dotProduct,mul_comm] using h i hi
    · simp [maskRows,hi,Matrix.mulVec,dotProduct]

end Papers.RationalityTen.ChirotopeDensity
