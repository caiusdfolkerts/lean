module

public import ToricPower.ThomsenClasses
public import TauCeti.Algebra.Module.Primitive

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

/-- Integral relations among the rows of the literal ray matrix. -/
def rayRelations (A : Matrix (Fin s) (Fin n) ℤ) :
    Submodule ℤ (Fin s → ℤ) := LinearMap.ker A.transpose.mulVecLin

@[simp] theorem mem_rayRelations (A : Matrix (Fin s) (Fin n) ℤ) (h : Fin s → ℤ) :
    h ∈ rayRelations A ↔ ∀ j, ∑ i, A i j * h i = 0 := by
  simp [rayRelations, LinearMap.mem_ker, funext_iff, Matrix.mulVec, Matrix.vecMul,
    dotProduct, mul_comm]

/-- A primitive support-minimal integral relation. Both signs are included. -/
def IsCircuit (A : Matrix (Fin s) (Fin n) ℤ) (h : Fin s → ℤ) : Prop :=
  TauCeti.IsPrimitive h ∧ h ∈ rayRelations A ∧
    ∀ k ∈ rayRelations A, Function.support k ⊂ Function.support h → k = 0

theorem IsCircuit.ne_zero {A : Matrix (Fin s) (Fin n) ℤ}
    {h : Fin s → ℤ} (hh : IsCircuit A h) : h ≠ 0 := hh.1.ne_zero

theorem IsCircuit.neg {A : Matrix (Fin s) (Fin n) ℤ}
    {h : Fin s → ℤ} (hh : IsCircuit A h) : IsCircuit A (-h) := by
  refine ⟨hh.1.neg, (rayRelations A).neg_mem hh.2.1, ?_⟩
  intro k hk hs
  apply hh.2.2 k hk
  simpa only [Function.support_neg] using hs

/-- Minimal support forces every integral relation with smaller or equal support
to lie on the same rational line. The coordinate cross-products avoid division. -/
theorem IsCircuit.cross_mul_eq {A : Matrix (Fin s) (Fin n) ℤ}
    {h : Fin s → ℤ} (hh : IsCircuit A h)
    {k : Fin s → ℤ} (hk : k ∈ rayRelations A)
    (hs : Function.support k ⊆ Function.support h) (i : Fin s) :
    h i • k = k i • h := by
  by_cases hi : h i = 0
  · have hki : k i = 0 := by
      by_contra hn
      exact (hs hn) hi
    simp [hi, hki]
  let v : Fin s → ℤ := h i • k - k i • h
  have hv : v ∈ rayRelations A :=
    (rayRelations A).sub_mem ((rayRelations A).smul_mem _ hk)
      ((rayRelations A).smul_mem _ hh.2.1)
  have hvsub : Function.support v ⊆ Function.support h := by
    intro j hj
    by_contra hnj
    have hjh : h j = 0 := by simpa only [Function.mem_support, not_not] using hnj
    have hjk : k j = 0 := by
      by_contra hnk
      exact hnj (hs hnk)
    exact hj (by simp [v, hjh, hjk])
  have his : i ∈ Function.support h := hi
  have hiv : i ∉ Function.support v := by
    simp [v, Function.mem_support, smul_eq_mul, mul_comm]
  have hstrict : Function.support v ⊂ Function.support h :=
    Set.ssubset_iff_subset_ne.mpr ⟨hvsub, fun heq => hiv (heq.symm ▸ his)⟩
  have hz := hh.2.2 v hv hstrict
  exact sub_eq_zero.mp hz

/-- A primitive circuit generates all integral relations with its support. -/
theorem IsCircuit.eq_int_smul_of_support_subset
    {A : Matrix (Fin s) (Fin n) ℤ} {h : Fin s → ℤ}
    (hh : IsCircuit A h) {k : Fin s → ℤ} (hk : k ∈ rayRelations A)
    (hs : Function.support k ⊆ Function.support h) :
    ∃ m : ℤ, k = m • h := by
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hh.1
  obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hh.ne_zero
  have hc := hh.cross_mul_eq hk hs i
  have hm : h i * f k = k i := by
    have hmap := congrArg f hc
    simpa only [map_smul, hf, smul_eq_mul, mul_one] using hmap
  refine ⟨f k, funext fun j => ?_⟩
  have hcj := congrFun hc j
  simp only [Pi.smul_apply, smul_eq_mul] at hcj ⊢
  apply mul_left_cancel₀ hi
  rw [hcj, ← hm]
  ring

def circuitSignature (h : Fin s → ℤ) : Fin s → Bool × Bool :=
  fun i => (decide (h i = 0), decide (0 < h i))

theorem circuitSignature_injective (A : Matrix (Fin s) (Fin n) ℤ) :
    Function.Injective (fun h : {h : Fin s → ℤ // IsCircuit A h} =>
      circuitSignature h.val) := by
  intro h k heq
  have hzero (i : Fin s) : h.val i = 0 ↔ k.val i = 0 := by
    have hi := congrArg Prod.fst (congrFun heq i)
    simpa only [circuitSignature, decide_eq_decide] using hi
  have hpos (i : Fin s) : 0 < h.val i ↔ 0 < k.val i := by
    have hi := congrArg Prod.snd (congrFun heq i)
    simpa only [circuitSignature, decide_eq_decide] using hi
  have hs : Function.support k.val ⊆ Function.support h.val := by
    intro i hi hz
    exact hi ((hzero i).mp hz)
  obtain ⟨m, hm⟩ := h.property.eq_int_smul_of_support_subset k.property.2.1 hs
  obtain ⟨g, hg⟩ := TauCeti.isPrimitive_def.mp k.property.1
  have hunit : m = 1 ∨ m = -1 := by
    have hh := congrArg g hm
    simp only [map_smul, smul_eq_mul, hg] at hh
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hh.symm with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  rcases hunit with hmone | hmneg
  · apply Subtype.ext
    simpa [hmone] using hm.symm
  · obtain ⟨i, hi⟩ : ∃ i, h.val i ≠ 0 := by
      simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using h.property.ne_zero
    have hki : k.val i = -h.val i := by
      simpa [hmneg] using congrFun hm i
    have hp := hpos i
    rw [hki] at hp
    omega

/-- The complete set of primitive circuits is finite; no rank or full-dimensionality
hypothesis is used. -/
theorem circuits_finite (A : Matrix (Fin s) (Fin n) ℤ) :
    {h : Fin s → ℤ | IsCircuit A h}.Finite := by
  letI : Finite ↑{h : Fin s → ℤ | IsCircuit A h} :=
    Finite.of_injective _ (circuitSignature_injective A)
  exact Set.toFinite _

def circuits (A : Matrix (Fin s) (Fin n) ℤ) : Finset (Fin s → ℤ) :=
  (circuits_finite A).toFinset

@[simp] theorem mem_circuits (A : Matrix (Fin s) (Fin n) ℤ) (h : Fin s → ℤ) :
    h ∈ circuits A ↔ IsCircuit A h := Set.Finite.mem_toFinset _

/-- The support value of the cube [-1,0]^s in an integral direction. -/
def cubeSupport (h : Fin s → ℤ) : ℤ := ∑ i, max (-h i) 0

theorem cubeSupport_nonneg (h : Fin s → ℤ) : 0 ≤ cubeSupport h :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

def circuitBound (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  1 + (circuits A).sup (fun h => ((∑ i, h i * b i) - cubeSupport h).toNat)

theorem circuitBound_pos (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    0 < circuitBound A b := by unfold circuitBound; omega

theorem circuitBound_strict (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ)
    {h : Fin s → ℤ} (hh : IsCircuit A h) :
    (∑ i, h i * b i) - cubeSupport h < (circuitBound A b : ℤ) := by
  have hsup := Finset.le_sup (f := fun h : Fin s → ℤ =>
    ((∑ i, h i * b i) - cubeSupport h).toNat) ((mem_circuits A h).mpr hh)
  have hn : ((∑ i, h i * b i) - cubeSupport h) ≤
      (((∑ i, h i * b i) - cubeSupport h).toNat : ℤ) := by omega
  unfold circuitBound
  omega

end ToricPower

