module

public import PaperVerification.E7TranslationGeometry


@[expose] public section
/-! # The 36 translation classes of E7* deep holes

Among the 135 nonzero isotropic E8 classes, exactly 72 meet the affine slice.
Orthogonal projection pairs each such class with its translate by the projection
root.  The resulting 36 classes are identified with the actual quotient of all
real E7* deep holes.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

abbrev E7SliceIndex := {c : E8HoleIndex // e8BinaryPolar c.val e8BinaryRoot = 1}
abbrev E7HoleIndex := {c : E8HoleIndex // e8BinaryPolar c.val e8BinaryRoot = 1 ∧ c.val 0 = 0}

theorem e7Slice_binary_representatives : ∀ c : E7SliceIndex,
    ∃! d : E7HoleIndex, c.val.val = d.val.val ∨ c.val.val = d.val.val + e8BinaryRoot := by
  intro c
  have hroot0 : e8BinaryRoot 0 = 1 := by decide
  have hdouble (a : Binary) : a + a = 0 := by
    rw [← two_mul, binary_two_eq_zero, zero_mul]
  have h11 : (1 : Binary) + 1 = 0 := hdouble 1
  have hrr : e8BinaryRoot + e8BinaryRoot = 0 := by
    funext i
    exact hdouble (e8BinaryRoot i)
  have hshift : (c.val.val + e8BinaryRoot) + e8BinaryRoot = c.val.val := by
    rw [add_assoc, hrr, add_zero]
  rcases binary_eq_zero_or_one (c.val.val 0) with h0 | h1
  · let d : E7HoleIndex := ⟨c.val, c.property, h0⟩
    refine ⟨d, Or.inl rfl, ?_⟩
    intro e he
    rcases he with he | he
    · exact Subtype.ext (Subtype.ext he.symm)
    · have hi := congrFun he 0
      simp only [Pi.add_apply, h0, e.property.2, hroot0, zero_add] at hi
      exact (zero_ne_one hi).elim
  · have hq : e8BinaryQ (c.val.val + e8BinaryRoot) = 0 := by
      have hp := c.property
      change e8BinaryQ (c.val.val + e8BinaryRoot) -
        e8BinaryQ c.val.val - e8BinaryQ e8BinaryRoot = 1 at hp
      rw [c.val.property.1, e8BinaryRoot_q, sub_zero] at hp
      have ha := congrArg (fun a : Binary => a + 1) hp
      simpa only [sub_add_cancel, h11] using ha
    have hp : e8BinaryPolar (c.val.val + e8BinaryRoot) e8BinaryRoot = 1 := by
      unfold e8BinaryPolar
      rw [hshift, hq, c.val.property.1, e8BinaryRoot_q, sub_zero]
      exact sub_eq_iff_eq_add.mpr h11.symm
    have hne : c.val.val + e8BinaryRoot ≠ 0 := by
      intro hz
      have hc : c.val.val = e8BinaryRoot := by
        calc
          c.val.val = (c.val.val + e8BinaryRoot) + e8BinaryRoot := hshift.symm
          _ = e8BinaryRoot := by rw [hz, zero_add]
      have hqc := c.val.property.1
      rw [hc, e8BinaryRoot_q] at hqc
      exact one_ne_zero hqc
    have hz0 : (c.val.val + e8BinaryRoot) 0 = 0 := by
      change c.val.val 0 + e8BinaryRoot 0 = 0
      rw [h1, hroot0]
      exact h11
    let d : E7HoleIndex := ⟨⟨c.val.val + e8BinaryRoot, hq, hne⟩, hp, hz0⟩
    have hd : c.val.val = d.val.val + e8BinaryRoot := hshift.symm
    refine ⟨d, Or.inr hd, ?_⟩
    intro e he
    rcases he with he | he
    · have hi := congrFun he 0
      rw [h1, e.property.2] at hi
      exact (one_ne_zero hi).elim
    · exact Subtype.ext (Subtype.ext (add_right_cancel (he.symm.trans hd)))

theorem e8BinaryRoot_zero : e8BinaryRoot 0 = 1 := by decide


/-- Translation by the projection root preserves the actual isotropic affine slice. -/
def e7Slice_addRoot (c : E7SliceIndex) : E7SliceIndex := by
  have hdouble (a : Binary) : a + a = 0 := by
    rw [← two_mul, binary_two_eq_zero, zero_mul]
  have h11 : (1 : Binary) + 1 = 0 := hdouble 1
  have hrr : e8BinaryRoot + e8BinaryRoot = 0 := by
    funext i
    exact hdouble (e8BinaryRoot i)
  have hshift : (c.val.val + e8BinaryRoot) + e8BinaryRoot = c.val.val := by
    rw [add_assoc, hrr, add_zero]
  have hq : e8BinaryQ (c.val.val + e8BinaryRoot) = 0 := by
    have hp := c.property
    change e8BinaryQ (c.val.val + e8BinaryRoot) -
      e8BinaryQ c.val.val - e8BinaryQ e8BinaryRoot = 1 at hp
    rw [c.val.property.1, e8BinaryRoot_q, sub_zero] at hp
    have ha := congrArg (fun a : Binary => a + 1) hp
    simpa only [sub_add_cancel, h11] using ha
  have hp : e8BinaryPolar (c.val.val + e8BinaryRoot) e8BinaryRoot = 1 := by
    unfold e8BinaryPolar
    rw [hshift, hq, c.val.property.1, e8BinaryRoot_q, sub_zero]
    exact sub_eq_iff_eq_add.mpr h11.symm
  have hne : c.val.val + e8BinaryRoot ≠ 0 := by
    intro hz
    have hc : c.val.val = e8BinaryRoot := by
      calc
        c.val.val = (c.val.val + e8BinaryRoot) + e8BinaryRoot := hshift.symm
        _ = e8BinaryRoot := by rw [hz, zero_add]
    have hqc := c.val.property.1
    rw [hc, e8BinaryRoot_q] at hqc
    exact one_ne_zero hqc
  exact ⟨⟨c.val.val + e8BinaryRoot, hq, hne⟩, hp⟩

@[simp] theorem e7Slice_addRoot_val (c : E7SliceIndex) :
    (e7Slice_addRoot c).val.val = c.val.val + e8BinaryRoot := rfl

/-- The second coordinate records which of the two slice points is chosen. -/
def e7SliceJoin (p : E7HoleIndex × Binary) : E7SliceIndex :=
  if p.2 = 0 then ⟨p.1.val, p.1.property.1⟩
  else e7Slice_addRoot ⟨p.1.val, p.1.property.1⟩

theorem e7SliceJoin_relation (p : E7HoleIndex × Binary) :
    (e7SliceJoin p).val.val = p.1.val.val ∨
      (e7SliceJoin p).val.val = p.1.val.val + e8BinaryRoot := by
  unfold e7SliceJoin
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem e7SliceJoin_bit (p : E7HoleIndex × Binary) :
    (e7SliceJoin p).val.val 0 = p.2 := by
  rcases binary_eq_zero_or_one p.2 with h0 | h1
  · rw [e7SliceJoin, if_pos h0]
    exact p.1.property.2.trans h0.symm
  · have hn : p.2 ≠ 0 := by rw [h1]; exact one_ne_zero
    rw [e7SliceJoin, if_neg hn]
    change (p.1.val.val + e8BinaryRoot) 0 = p.2
    simp only [Pi.add_apply, p.1.property.2, e8BinaryRoot_zero, zero_add]
    exact h1.symm

theorem e7SliceJoin_zero (d : E7HoleIndex) :
    (e7SliceJoin (d, 0)).val.val = d.val.val := by
  rw [e7SliceJoin, if_pos rfl]

theorem e7SliceJoin_one (d : E7HoleIndex) :
    (e7SliceJoin (d, 1)).val.val = d.val.val + e8BinaryRoot := by
  rw [e7SliceJoin, if_neg one_ne_zero, e7Slice_addRoot_val]

theorem e7SliceJoin_bijective : Function.Bijective e7SliceJoin := by
  constructor
  · intro p q hpq
    have hbit : p.2 = q.2 :=
      (e7SliceJoin_bit p).symm.trans
        ((congrArg (fun c : E7SliceIndex => c.val.val 0) hpq).trans (e7SliceJoin_bit q))
    have hp := e7SliceJoin_relation p
    have hq : (e7SliceJoin p).val.val = q.1.val.val ∨
        (e7SliceJoin p).val.val = q.1.val.val + e8BinaryRoot := by
      rw [hpq]
      exact e7SliceJoin_relation q
    obtain ⟨d, hd, huniq⟩ := e7Slice_binary_representatives (e7SliceJoin p)
    exact Prod.ext ((huniq p.1 hp).trans (huniq q.1 hq).symm) hbit
  · intro c
    obtain ⟨d, hd, _⟩ := e7Slice_binary_representatives c
    rcases hd with hd | hd
    · refine ⟨(d, 0), Subtype.ext (Subtype.ext ?_)⟩
      rw [e7SliceJoin_zero]
      exact hd.symm
    · refine ⟨(d, 1), Subtype.ext (Subtype.ext ?_)⟩
      rw [e7SliceJoin_one]
      exact hd.symm

/-- Exact two-point fibers, with the actual root translate distinguished by bit zero. -/
def e7SliceProductEquiv : E7SliceIndex ≃ E7HoleIndex × Binary :=
  (Equiv.ofBijective e7SliceJoin e7SliceJoin_bijective).symm

theorem card_e7HoleIndex : Fintype.card E7HoleIndex = 36 := by
  have h := Fintype.card_congr e7SliceProductEquiv
  rw [card_e8HalfSliceIndex, Fintype.card_prod] at h
  have hbinary : Fintype.card Binary = 2 := by decide
  rw [hbinary] at h
  omega

def e7ClassPoint (c : E7HoleIndex) : zeroSumSpace := project8 (e8ClassPoint c.val.val)

theorem e7ClassPoint_deep (c : E7HoleIndex) : IsE7DeepHole (e7ClassPoint c) := by
  let t : Fin 8 → ℤ := fun i => ((c.val.val i).val : ℤ)
  have hodd : Odd (e8HalfSumInt t) := by
    apply ZMod.intCast_eq_one_iff_odd.mp
    rw [e8HalfSumInt_cast]
    simpa only [t, binary_val_cast] using c.property.1
  exact e7_project_deep_of_odd_sum (e8ClassPoint_deep c.val) (e8HalfRootSum_sum t) hodd

theorem e7ClassPoint_distinct (c d : E7HoleIndex) :
    e7ClassPoint c - e7ClassPoint d ∈ e7ProjectedSet ↔ c = d := by
  rw [e7ClassPoint, e7ClassPoint, e8ClassPoint, e8ClassPoint, e7Projected_halfRoot_difference_iff]
  simp only [binary_val_cast]
  constructor
  · rintro (h | h)
    · exact Subtype.ext (Subtype.ext h)
    · have hi := congrFun h 0
      simp only [Pi.add_apply, c.property.2, d.property.2, e8BinaryRoot_zero, zero_add] at hi
      exact (zero_ne_one hi).elim
  · rintro rfl
    exact Or.inl rfl

theorem project8_e7Slice (x : zeroSumSpace) : project8 (e7Slice x) = x := by
  change project8 (fun i ↦ x.val i + 1 / 8) = x
  rw [project8_add_constant, project8_coe]

theorem e7DeepHole_coset_coverage {x : zeroSumSpace} (hx : IsE7DeepHole x) :
    ∃ c : E7HoleIndex, x - e7ClassPoint c ∈ e7ProjectedSet := by
  have hslice := (isDeepHole_slice_iff x).mpr hx
  obtain ⟨t, ht⟩ := e8_halfRoot_coordinates_of_deep hslice
  have htdeep : IsDeepHole (dPlusSet 8) (e8HalfRootSum t) := ht ▸ hslice
  have hs : (∑ i, e8HalfRootSum t i) = 1 := by
    rw [← ht]
    simp [e7Slice, Finset.sum_add_distrib, zeroSumSpace_sum]
  have hint : e8HalfSumInt t = 1 := by
    rw [e8HalfRootSum_sum] at hs
    exact_mod_cast hs
  have hpolar : e8BinaryPolar (fun i => (t i : Binary)) e8BinaryRoot = 1 := by
    rw [← e8HalfSumInt_cast, hint]
    norm_num
  let a : E7SliceIndex := ⟨⟨fun i => (t i : Binary), e8_deep_halfRoot_binary htdeep⟩, hpolar⟩
  obtain ⟨c, hc, _⟩ := e7Slice_binary_representatives a
  refine ⟨c, ?_⟩
  have hproj : x = project8 (e8HalfRootSum t) := by rw [← ht, project8_e7Slice]
  rw [hproj, e7ClassPoint, e8ClassPoint, e7Projected_halfRoot_difference_iff]
  simpa only [a, binary_val_cast] using hc

def E7DeepTranslationClasses :=
  {C : zeroSumSpace ⧸ e7ProjectedAddSubgroup // ∃ x : zeroSumSpace, IsE7DeepHole x ∧
    (x : zeroSumSpace ⧸ e7ProjectedAddSubgroup) = C}

def e7DeepClassMap (c : E7HoleIndex) : E7DeepTranslationClasses :=
  ⟨(e7ClassPoint c : zeroSumSpace ⧸ e7ProjectedAddSubgroup), e7ClassPoint c, e7ClassPoint_deep c, rfl⟩

theorem e7DeepClassMap_bijective : Function.Bijective e7DeepClassMap := by
  constructor
  · intro c d h
    apply (e7ClassPoint_distinct c d).mp
    rw [← e7ProjectedAddSubgroup_coe]
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C, x, hx, hC⟩
    obtain ⟨c, hc⟩ := e7DeepHole_coset_coverage hx
    refine ⟨c, Subtype.ext ?_⟩
    rw [← e7ProjectedAddSubgroup_coe] at hc
    exact (QuotientAddGroup.eq_iff_sub_mem.mpr hc).symm.trans hC

def e7DeepClassEquiv : E7HoleIndex ≃ E7DeepTranslationClasses :=
  Equiv.ofBijective e7DeepClassMap e7DeepClassMap_bijective

/-- Exactly 36 classes in the quotient by the actual E7* lattice. -/
theorem e7_dual_deep_translation_class_count : Nat.card E7DeepTranslationClasses = 36 := by
  rw [← Nat.card_congr e7DeepClassEquiv, Nat.card_eq_fintype_card, card_e7HoleIndex]

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e7_dual_deep_translation_class_count
