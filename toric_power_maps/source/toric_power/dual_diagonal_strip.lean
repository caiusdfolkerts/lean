module

public import ToricPower.ArrangementCostalkCells
public import ToricPower.ArrangementCostalkCellular

/-!
# The literal open strip in the dual diagonal calculation

Dualizing the two Cartier labels changes the closed section strip into
the open strip `-u(v)-1 < y(v) < 1`, with the two inequalities imposed on
the appropriate cones. The strict endpoints are forced by the exact
integer ceiling rules, including equality walls. The actual monomial
indices are precisely its periodic cells. Integer coordinate boxes give
an increasing exhaustion by bounded open convex unions of finitely many
cells. These are the finite stages used for compactly supported cellular
cochains; no full algebraic dual of an infinite chain module is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Topology
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ)

def dualDiagonalStrip (S T : Set (Fin s)) (u : Fin n → ℤ) : Set (Fin n → ℝ) :=
  {y | (∀ i ∈ S, integralRowForm A i y < 1) ∧
    ∀ i ∈ T, -(rayPairing A u i : ℝ) - 1 < integralRowForm A i y}

def dualStripCellAllowed (S T : Set (Fin s)) (u : Fin n → ℤ)
    {q : ℕ} (c : Cell (augmentedForms A) q) : Prop :=
  (∀ i ∈ S, 0 ≤ reflectedCeiling A c i) ∧
    ∀ i ∈ T, -rayPairing A u i ≤ c.val.1 (.inl i)

/-- The actual monomial conditions of the two dual Cartier factors. -/
def dualDiagonalMonomialAllowed (S T : Set (Fin s)) (u : Fin n → ℤ)
    {q : ℕ} (p : NormalizedCell A q × (Fin n → ℤ)) : Prop :=
  (∀ i ∈ S, 0 ≤ rayPairing A p.2 i + reflectedCeiling A p.1.val i) ∧
    ∀ i ∈ T, 0 ≤ rayPairing A (u - p.2) i + p.1.val.val.1 (.inl i)

theorem dualStripCellAllowed_iff_point (S T : Set (Fin s)) (u : Fin n → ℤ)
    {q : ℕ} (c : Cell (augmentedForms A) q) {x : Fin n → ℝ}
    (hx : x ∈ cell (augmentedForms A) c.val.1 c.val.2) :
    dualStripCellAllowed A S T u c ↔ x ∈ dualDiagonalStrip A S T u := by
  unfold dualStripCellAllowed dualDiagonalStrip
  apply and_congr
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro _
    rw [reflectedCeiling_eq_ceil A c hx i, Int.le_ceil_iff]
    simp only [Int.cast_zero, zero_sub]
    exact neg_lt_neg_iff
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro _
    rw [← ceil_eq_of_mem_cell (augmentedForms A) _ _ hx (.inl i),
      Int.le_ceil_iff, Int.cast_neg]
    rfl

theorem dualStripCellAllowed_translate_iff (S T : Set (Fin s))
    (u a : Fin n → ℤ) {q : ℕ} (c : NormalizedCell A q) :
    dualStripCellAllowed A S T u (translateCell A (-a) c.val) ↔
      dualDiagonalMonomialAllowed A S T u (c, a) := by
  have negative (i : Fin s) : rayPairing A (-a) i = -rayPairing A a i := by
    simp only [rayPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  unfold dualStripCellAllowed dualDiagonalMonomialAllowed
  apply and_congr
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro _
    rw [reflectedCeiling_translate, negative]
    dsimp only
    omega
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro _
    change -rayPairing A u i ≤ c.val.val.1 (.inl i) + rayPairing A (-a) i ↔ _
    rw [negative, rayPairing_sub]
    dsimp only
    omega

/-- The sign of the actual Laurent translation is fixed by the two
literal dual section inequalities. -/
def dualDiagonalMonomialCellEquiv (S T : Set (Fin s)) (u : Fin n → ℤ) (q : ℕ) :
    {p : NormalizedCell A q × (Fin n → ℤ) // dualDiagonalMonomialAllowed A S T u p} ≃
      {c : Cell (augmentedForms A) q // dualStripCellAllowed A S T u c} :=
  (signedCellOrbitEquiv A q).symm.subtypeEquiv (fun p =>
    (dualStripCellAllowed_translate_iff A S T u p.2 p.1).symm)

theorem dualDiagonalStrip_isOpen (S T : Set (Fin s)) (u : Fin n → ℤ) :
    IsOpen (dualDiagonalStrip A S T u) := by
  simp only [dualDiagonalStrip, Set.setOf_and, Set.setOf_forall]
  apply IsOpen.inter <;> apply isOpen_iInter_of_finite <;> intro i
  · apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (integralRowForm A i).continuous_of_finiteDimensional continuous_const
  · apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (integralRowForm A i).continuous_of_finiteDimensional

theorem dualDiagonalStrip_convex (S T : Set (Fin s)) (u : Fin n → ℤ) :
    Convex ℝ (dualDiagonalStrip A S T u) := by
  simp only [dualDiagonalStrip, Set.setOf_and, Set.setOf_forall]
  exact (convex_iInter fun i => convex_iInter fun _ =>
      (convex_Iio (1 : ℝ)).linear_preimage (integralRowForm A i)).inter
    (convex_iInter fun i => convex_iInter fun _ =>
      (convex_Ioi (-(rayPairing A u i : ℝ) - 1)).linear_preimage (integralRowForm A i))

theorem dualDiagonalStrip_cellwise (S T : Set (Fin s)) (u : Fin n → ℤ) :
    Cellwise (augmentedForms A) (dualDiagonalStrip A S T u) := by
  intro e I x y hx hy
  let c : Cell (augmentedForms A)
      (Module.finrank ℝ (cellDirection (augmentedForms A) I)) :=
    ⟨(e, I), ⟨x, hx⟩, rfl⟩
  exact (dualStripCellAllowed_iff_point A S T u c hx).symm.trans
    (dualStripCellAllowed_iff_point A S T u c hy)

def integerOpenBox (r : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ j, -(r : ℝ) < x j ∧ x j < (r : ℝ)}

theorem integerOpenBox_isOpen (r : ℕ) : IsOpen (integerOpenBox (n := n) r) := by
  simp only [integerOpenBox, Set.setOf_forall, Set.setOf_and]
  apply isOpen_iInter_of_finite
  intro j
  exact (isOpen_lt continuous_const (continuous_apply j)).inter
    (isOpen_lt (continuous_apply j) continuous_const)

theorem integerOpenBox_convex (r : ℕ) : Convex ℝ (integerOpenBox (n := n) r) := by
  simp only [integerOpenBox, Set.setOf_forall]
  exact convex_iInter fun j =>
    (convex_Ioo (-(r : ℝ)) r).linear_preimage (LinearMap.proj j :
      (Fin n → ℝ) →ₗ[ℝ] ℝ)

theorem integerOpenBox_bounded (r : ℕ) :
    Bornology.IsBounded (integerOpenBox (n := n) r) := by
  apply (isCompact_Icc (a := fun _ : Fin n => -(r : ℝ))
    (b := fun _ : Fin n => (r : ℝ))).isBounded.subset
  intro x hx
  exact ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩

theorem integerOpenBox_cellwise (r : ℕ) :
    Cellwise (augmentedForms A) (integerOpenBox (n := n) r) := by
  intro e I x y hx hy
  suffices transfer : ∀ {x y : Fin n → ℝ}, x ∈ cell (augmentedForms A) e I →
      y ∈ cell (augmentedForms A) e I → x ∈ integerOpenBox r → y ∈ integerOpenBox r from
    ⟨transfer hx hy, transfer hy hx⟩
  intro x y hx hy bounds j
  have xcell := hx (.inr j)
  have ycell := hy (.inr j)
  by_cases wall : Sum.inr j ∈ I
  · simp only [if_pos wall] at xcell ycell
    change x j = (e (.inr j) : ℝ) at xcell
    change y j = (e (.inr j) : ℝ) at ycell
    simpa only [← xcell, ycell] using bounds j
  · simp only [if_neg wall] at xcell ycell
    change (e (.inr j) : ℝ) - 1 < x j ∧ x j < (e (.inr j) : ℝ) at xcell
    change (e (.inr j) : ℝ) - 1 < y j ∧ y j < (e (.inr j) : ℝ) at ycell
    have lowerInt : -(r : ℤ) < e (.inr j) := by
      exact_mod_cast (bounds j).1.trans xcell.2
    have upperInt : e (.inr j) ≤ (r : ℤ) := by
      rw [← ceil_eq_of_mem_cell (augmentedForms A) e I hx (.inr j)]
      exact Int.ceil_le.mpr (by exact (bounds j).2.le)
    have lower : -(r : ℝ) ≤ (e (.inr j) : ℝ) - 1 := by
      have : -(r : ℤ) ≤ e (.inr j) - 1 := by omega
      exact_mod_cast this
    exact ⟨lower.trans_lt ycell.1, ycell.2.trans_le (by exact_mod_cast upperInt)⟩

def dualDiagonalWindow (S T : Set (Fin s)) (u : Fin n → ℤ) (r : ℕ) :
    Set (Fin n → ℝ) := dualDiagonalStrip A S T u ∩ integerOpenBox r

theorem dualDiagonalWindow_isOpen (S T : Set (Fin s)) (u : Fin n → ℤ) (r : ℕ) :
    IsOpen (dualDiagonalWindow A S T u r) :=
  (dualDiagonalStrip_isOpen A S T u).inter (integerOpenBox_isOpen r)

theorem dualDiagonalWindow_convex (S T : Set (Fin s)) (u : Fin n → ℤ) (r : ℕ) :
    Convex ℝ (dualDiagonalWindow A S T u r) :=
  (dualDiagonalStrip_convex A S T u).inter (integerOpenBox_convex r)

theorem dualDiagonalWindow_bounded (S T : Set (Fin s)) (u : Fin n → ℤ) (r : ℕ) :
    Bornology.IsBounded (dualDiagonalWindow A S T u r) :=
  (integerOpenBox_bounded r).subset inter_subset_right

theorem dualDiagonalWindow_cellwise (S T : Set (Fin s)) (u : Fin n → ℤ) (r : ℕ) :
    Cellwise (augmentedForms A) (dualDiagonalWindow A S T u r) :=
  (dualDiagonalStrip_cellwise A S T u).inter (integerOpenBox_cellwise A r)

theorem dualDiagonalWindow_mono (S T : Set (Fin s)) (u : Fin n → ℤ) :
    Monotone (dualDiagonalWindow A S T u) := by
  intro r t le x hx
  refine ⟨hx.1, fun j => ?_⟩
  have cast : (r : ℝ) ≤ (t : ℝ) := by exact_mod_cast le
  exact ⟨lt_of_le_of_lt (neg_le_neg cast) (hx.2 j).1, (hx.2 j).2.trans_le cast⟩

/-- Every point of the full open strip occurs in a finite geometric
stage; no boundedness of the full strip is asserted. -/
theorem dualDiagonalWindow_exhausts (S T : Set (Fin s)) (u : Fin n → ℤ) :
    (⋃ r : ℕ, dualDiagonalWindow A S T u r) = dualDiagonalStrip A S T u := by
  apply Subset.antisymm
  · exact iUnion_subset fun _ => inter_subset_left
  · intro x hx
    obtain ⟨r, hr⟩ := exists_nat_gt ‖x‖
    refine mem_iUnion.mpr ⟨r, hx, fun j => ?_⟩
    have bound : |x j| < (r : ℝ) := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x j).trans_lt hr
    exact abs_lt.mp bound

/-- Each bounded stage contains finitely many actual cells. The proof
uses the locally finite closed-cell family and the compact coordinate
box, rather than assuming finiteness of a lifted arrangement. -/
instance dualDiagonalWindow_cells_finite (S T : Set (Fin s))
    (u : Fin n → ℤ) (r q : ℕ) :
    Finite {c : Cell (augmentedForms A) q //
      cellCenter (augmentedForms A) c ∈ dualDiagonalWindow A S T u r} := by
  let K := Icc (fun _ : Fin n => -(r : ℝ)) (fun _ : Fin n => (r : ℝ))
  let F : ((Fin s ⊕ Fin n → ℤ) × Set (Fin s ⊕ Fin n)) → Set (Fin n → ℝ) :=
    fun p => closedCell (augmentedForms A) p.1 p.2
  have hloc : LocallyFinite F :=
    closedCells_locallyFinite (augmentedForms A)
      (fun i => (augmentedForms A i).continuous_of_finiteDimensional)
  have hfin : Set.Finite {p | (F p ∩ K).Nonempty} :=
    hloc.finite_nonempty_inter_compact isCompact_Icc
  let g : {c : Cell (augmentedForms A) q //
        cellCenter (augmentedForms A) c ∈ dualDiagonalWindow A S T u r} →
      {p | (F p ∩ K).Nonempty} := fun c =>
    ⟨c.val.val, cellCenter (augmentedForms A) c.val,
      cell_subset_closedCell (augmentedForms A) _ _
        (cellCenter_mem (augmentedForms A) c.val),
      (fun j => (c.property.2 j).1.le), (fun j => (c.property.2 j).2.le)⟩
  letI : Finite {p | (F p ∩ K).Nonempty} := hfin.to_subtype
  exact Finite.of_injective g (by
    intro c d h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {p | (F p ∩ K).Nonempty} => z.val) h)

end ToricPower.IntegralArrangement
