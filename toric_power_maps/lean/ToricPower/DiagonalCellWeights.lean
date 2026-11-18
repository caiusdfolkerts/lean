module

public import ToricPower.ArrangementPeriodicity

/-! # Literal diagonal monomial weights and arrangement cells

The two labels of the diagonal resolution are `L(-x)` and `L(x)`, where
`L(x)` has coefficient `-ceil(Ax)`. A monomial pair of total character `u`
therefore has exponents `a` and `u-a`. Translating the actual cell by `a`
identifies its section inequalities with the convex strip
`0 ≤ A_i y` on the left cone and `A_i y ≤ A_i u` on the right cone.

This file proves the exact indexing equivalence and the literal strip
interpretation. It does not assume that a sheaf complex is exact, or identify
an abstract chain complex with a diagonal resolution by definition.
Candidate until an ordinary compiler check succeeds.
-/

@[expose] public noncomputable section

open Set
open scoped Classical BigOperators

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

def rayPairing (z : Fin n → ℤ) (i : Fin s) : ℤ := ∑ j, A i j * z j

@[simp]
theorem rayPairing_sub (u a : Fin n → ℤ) (i : Fin s) :
    rayPairing A (u-a) i = rayPairing A u i - rayPairing A a i := by
  simp [rayPairing, mul_sub, Finset.sum_sub_distrib]

/-- The ceiling of the reflected point. Equality walls use `-e`, whereas
the open interval between consecutive integer walls uses `1-e`. -/
def reflectedCeiling {d : ℕ} (c : Cell (augmentedForms A) d) (i : Fin s) : ℤ :=
  if Sum.inl i ∈ c.val.2 then -c.val.1 (.inl i) else 1-c.val.1 (.inl i)

theorem reflectedCeiling_eq_ceil {d : ℕ} (c : Cell (augmentedForms A) d)
    {x : Fin n → ℝ} (hx : x ∈ cell (augmentedForms A) c.val.1 c.val.2)
    (i : Fin s) : reflectedCeiling A c i = ⌈-integralRowForm A i x⌉ := by
  have h := hx (.inl i)
  change (if Sum.inl i ∈ c.val.2 then
    integralRowForm A i x = (c.val.1 (.inl i) : ℝ)
    else (c.val.1 (.inl i) : ℝ)-1 < integralRowForm A i x ∧
      integralRowForm A i x < (c.val.1 (.inl i) : ℝ)) at h
  unfold reflectedCeiling
  by_cases hi : Sum.inl i ∈ c.val.2
  · simp only [if_pos hi] at h ⊢
    rw [h, ← Int.cast_neg, Int.ceil_intCast]
  · simp only [if_neg hi] at h ⊢
    symm
    apply Int.ceil_eq_iff.mpr
    simp only [Int.cast_sub, Int.cast_one]
    constructor <;> linarith [h.1, h.2]

@[simp]
theorem reflectedCeiling_translate {d : ℕ} (c : Cell (augmentedForms A) d)
    (a : Fin n → ℤ) (i : Fin s) :
    reflectedCeiling A (translateCell A a c) i =
      reflectedCeiling A c i - rayPairing A a i := by
  unfold reflectedCeiling translateCell
  simp only [Pi.add_apply, augmentedLatticePairing, Sum.elim_inl, rayPairing]
  split_ifs <;> ring

/-- The actual convex region, with no extra inequality from the coordinate
hyperplanes used solely to subdivide the arrangement into bounded cells. -/
def diagonalStrip (S T : Set (Fin s)) (u : Fin n → ℤ) : Set (Fin n → ℝ) :=
  {y | (∀ i ∈ S, 0 ≤ integralRowForm A i y) ∧
    ∀ i ∈ T, integralRowForm A i y ≤ (rayPairing A u i : ℝ)}

def stripCellAllowed (S T : Set (Fin s)) (u : Fin n → ℤ)
    {d : ℕ} (c : Cell (augmentedForms A) d) : Prop :=
  (∀ i ∈ S, reflectedCeiling A c i ≤ 0) ∧
    ∀ i ∈ T, c.val.1 (.inl i) ≤ rayPairing A u i

/-- The literal inequalities for a monomial pair `(a,u-a)` in the two
line-bundle factors attached to a normalized arrangement cell. -/
def diagonalMonomialAllowed (S T : Set (Fin s)) (u : Fin n → ℤ)
    {d : ℕ} (p : NormalizedCell A d × (Fin n → ℤ)) : Prop :=
  (∀ i ∈ S, reflectedCeiling A p.1.val i ≤ rayPairing A p.2 i) ∧
    ∀ i ∈ T, p.1.val.val.1 (.inl i) ≤ rayPairing A (u-p.2) i

theorem stripCellAllowed_translate_iff (S T : Set (Fin s)) (u a : Fin n → ℤ)
    {d : ℕ} (c : Cell (augmentedForms A) d) :
    stripCellAllowed A S T u (translateCell A a c) ↔
      ((∀ i ∈ S, reflectedCeiling A c i ≤ rayPairing A a i) ∧
       ∀ i ∈ T, c.val.1 (.inl i) ≤ rayPairing A (u-a) i) := by
  unfold stripCellAllowed
  simp only [reflectedCeiling_translate, sub_nonpos]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  change c.val.1 (.inl i) + rayPairing A a i ≤ rayPairing A u i ↔ _
  rw [rayPairing_sub]
  omega

/-- The finite orbit representative and the literal monomial exponent
index exactly the cells of the corresponding convex weight subcomplex. -/
def diagonalMonomialCellEquiv (S T : Set (Fin s)) (u : Fin n → ℤ) (d : ℕ) :
    {p : NormalizedCell A d × (Fin n → ℤ) // diagonalMonomialAllowed A S T u p} ≃
      {c : Cell (augmentedForms A) d // stripCellAllowed A S T u c} :=
  (cellOrbitEquiv A d).symm.subtypeEquiv (fun p => by
    change diagonalMonomialAllowed A S T u p ↔
      stripCellAllowed A S T u (translateCell A p.2 p.1.val)
    exact (stripCellAllowed_translate_iff A S T u p.2 p.1.val).symm)

theorem stripCellAllowed_iff_point (S T : Set (Fin s)) (u : Fin n → ℤ)
    {d : ℕ} (c : Cell (augmentedForms A) d) {x : Fin n → ℝ}
    (hx : x ∈ cell (augmentedForms A) c.val.1 c.val.2) :
    stripCellAllowed A S T u c ↔ x ∈ diagonalStrip A S T u := by
  unfold stripCellAllowed diagonalStrip
  simp only [mem_setOf_eq]
  apply and_congr
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    rw [reflectedCeiling_eq_ceil A c hx i, Int.ceil_le]
    simp only [Int.cast_zero, neg_nonpos]
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    have he := ceil_eq_of_mem_cell (augmentedForms A) c.val.1 c.val.2 hx (.inl i)
    change ⌈integralRowForm A i x⌉ = c.val.1 (.inl i) at he
    rw [← he, Int.ceil_le]

theorem diagonalStrip_isClosed (S T : Set (Fin s)) (u : Fin n → ℤ) :
    IsClosed (diagonalStrip A S T u) := by
  simp only [diagonalStrip, Set.setOf_and, Set.setOf_forall]
  exact (isClosed_biInter fun i hi => isClosed_le continuous_const
    (integralRowForm A i).continuous_of_finiteDimensional).inter
    (isClosed_biInter fun i hi => isClosed_le
      (integralRowForm A i).continuous_of_finiteDimensional continuous_const)

/-- An allowed cell contributes its whole closure. This is the actual
attaching-map condition needed by the weighted cellular differential. -/
theorem stripCellAllowed_iff_closedCell_subset (S T : Set (Fin s))
    (u : Fin n → ℤ) {d : ℕ} (c : Cell (augmentedForms A) d) :
    stripCellAllowed A S T u c ↔
      closedCell (augmentedForms A) c.val.1 c.val.2 ⊆ diagonalStrip A S T u := by
  constructor
  · intro hc
    rw [← closure_cell (augmentedForms A)
      (fun i => (augmentedForms A i).continuous_of_finiteDimensional)
      c.val.1 c.val.2 c.property.1]
    exact closure_minimal (fun x hx => (stripCellAllowed_iff_point A S T u c hx).mp hc)
      (diagonalStrip_isClosed A S T u)
  · intro hc
    obtain ⟨x, hx⟩ := c.property.1
    exact (stripCellAllowed_iff_point A S T u c hx).mpr
      (hc (cell_subset_closedCell (augmentedForms A) c.val.1 c.val.2 hx))

end ToricPower.IntegralArrangement
