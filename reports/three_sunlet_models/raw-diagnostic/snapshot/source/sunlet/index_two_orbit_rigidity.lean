module

public import sunlet.orbit_models

/-!
# Rigidity of the index-two automorphism-orbit exception

The three orbit sets are literal orbits of an actual subgroup of `AddAut G`.
No prime-exponent classification or elementary-abelian hypothesis is assumed.
The proof uses only transitivity on the two nonzero orbit sets and the
index-two subgroup laws. This development source requires its own compiler
check; its presence is not an acceptance record.
-/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitClasses

variable {G : Type*} [AddCommGroup G] [Fintype G]

private theorem classOf_apply_automorphism (B : AddSubgroup (AddAut G))
    (φ : B) (x : G) : classOf B (φ.val x) = classOf B x :=
  ((classOf_eq_iff B x (φ.val x)).mpr ⟨φ, rfl⟩).symm

/-- If the actual automorphism orbits are `0`, the nonzero part of an
index-two subgroup, and its complement, a group of order at least five has
exponent two. The outside and inside classes are specified by exact iff
conditions, not by an assumed abstract transitivity property. -/
theorem index_two_orbit_partition_exponent_two
    (B : AddSubgroup (AddAut G)) (H : AddSubgroup G) (hindex : H.index = 2)
    (outside inside : Class B)
    (hout : ∀ x, classOf B x = outside ↔ x ∉ H)
    (hin : ∀ x, classOf B x = inside ↔ x ∈ H ∧ x ≠ 0)
    (hm : 5 ≤ Fintype.card G) : ∀ x : G, (2 : ℕ) • x = 0 := by
  classical
  obtain ⟨a, ha, _⟩ := H.index_eq_two_iff_exists_notMem_and.mp hindex
  have outside_map (φ : B) (x : G) (hx : x ∉ H) : φ.val x ∉ H :=
    (hout _).mp ((classOf_apply_automorphism B φ x).trans ((hout x).mpr hx))
  have inside_map (φ : B) (x : G) (hx : x ∈ H) : φ.val x ∈ H := by
    by_cases hx0 : x = 0
    · simpa only [hx0, map_zero] using H.zero_mem
    · exact ((hin _).mp ((classOf_apply_automorphism B φ x).trans
        ((hin x).mpr ⟨hx, hx0⟩))).1
  have outside_transitive (x y : G) (hx : x ∉ H) (hy : y ∉ H) :
      ∃ φ : B, φ.val x = y :=
    (classOf_eq_iff B x y).mp (((hout x).mpr hx).trans ((hout y).mpr hy).symm)
  have inside_transitive (x y : G) (hx : x ∈ H) (hx0 : x ≠ 0)
      (hy : y ∈ H) (hy0 : y ≠ 0) : ∃ φ : B, φ.val x = y :=
    (classOf_eq_iff B x y).mp
      (((hin x).mpr ⟨hx, hx0⟩).trans ((hin y).mpr ⟨hy, hy0⟩).symm)
  have outside_zero_of_one (z : G) (hz : z ∉ H) (hz2 : (2 : ℕ) • z = 0) :
      ∀ y : G, y ∉ H → (2 : ℕ) • y = 0 := by
    intro y hy
    obtain ⟨φ, hφ⟩ := outside_transitive z y hz hy
    simpa only [map_nsmul, hφ, map_zero] using congrArg (fun t : G => φ.val t) hz2
  have all_zero_of_outside (ho : ∀ y : G, y ∉ H → (2 : ℕ) • y = 0) :
      ∀ x : G, (2 : ℕ) • x = 0 := by
    intro x
    by_cases hx : x ∈ H
    · have hax : a + x ∉ H := by
        intro h
        exact ha (by simpa only [add_sub_cancel_right] using H.sub_mem h hx)
      have h := ho (a + x) hax
      simpa only [nsmul_add, ho a ha, zero_add] using h
    · exact ho x hx
  have inside_two (h : G) (hh : h ∈ H) : (2 : ℕ) • h = 0 := by
    by_contra hh2
    by_cases ha2 : (2 : ℕ) • a = 0
    · exact hh2 (all_zero_of_outside (outside_zero_of_one a ha ha2) h)
    · obtain ⟨φ, hφ⟩ := inside_transitive ((2 : ℕ) • h) ((2 : ℕ) • a)
        (H.nsmul_mem hh 2) hh2 (H.two_smul_mem_of_index_two hindex a) ha2
      have hφh : φ.val h ∈ H := inside_map φ h hh
      have hz : a - φ.val h ∉ H := by
        intro h
        exact ha (by simpa only [sub_add_cancel] using H.add_mem h hφh)
      have hφ2 : (2 : ℕ) • φ.val h = (2 : ℕ) • a := by
        simpa only [map_nsmul] using hφ
      have hz2 : (2 : ℕ) • (a - φ.val h) = 0 := by
        rw [nsmul_sub, hφ2, sub_self]
      exact hh2 (all_zero_of_outside (outside_zero_of_one _ hz hz2) h)
  have outside_difference (x y : G) (hx : x ∉ H) (hy : y ∉ H) : x - y ∈ H := by
    rw [sub_eq_add_neg, AddSubgroup.add_mem_iff_of_index_two hindex,
      AddSubgroup.neg_mem_iff]
    exact iff_of_false hx hy
  have outside_two (x : G) (hx : x ∉ H) : (2 : ℕ) • x = (2 : ℕ) • a := by
    apply sub_eq_zero.mp
    simpa only [nsmul_sub] using inside_two (x - a) (outside_difference x a hx ha)
  have ha2 : (2 : ℕ) • a = 0 := by
    by_contra ht
    have htH : (2 : ℕ) • a ∈ H := H.two_smul_mem_of_index_two hindex a
    have unique_inside (h : G) (hh : h ∈ H) (hh0 : h ≠ 0) : h = (2 : ℕ) • a := by
      obtain ⟨φ, hφ⟩ := inside_transitive ((2 : ℕ) • a) h htH ht hh hh0
      rw [← hφ, map_nsmul]
      exact outside_two (φ.val a) (outside_map φ a ha)
    letI : Fintype H := Fintype.ofFinite H
    let t : H := ⟨(2 : ℕ) • a, htH⟩
    have hsmall : (Finset.univ : Finset H) ⊆ {0, t} := by
      intro h _
      by_cases hz : (h : G) = 0
      · have he : h = 0 := Subtype.ext hz
        simp only [he, Finset.mem_insert, true_or]
      · have he : h = t := Subtype.ext (unique_inside h h.property hz)
        simp only [he, Finset.mem_insert, Finset.mem_singleton, or_true]
    have hcard := Finset.card_le_card hsmall
    have hbound := Finset.card_insert_le (0 : H) ({t} : Finset H)
    simp only [Finset.card_univ, Finset.card_singleton] at hcard hbound
    have hsize := H.card_mul_index
    rw [hindex, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hsize
    omega
  intro x
  by_cases hx : x ∈ H
  · exact inside_two x hx
  · exact (outside_two x hx).trans ha2

/-- The exceptional partition of the inverse-stable automorphism model forces
inversion itself to be the identity automorphism. -/
theorem index_two_orbit_partition_negation_eq_zero
    (B : AddSubgroup (AddAut G)) (H : AddSubgroup G) (hindex : H.index = 2)
    (outside inside : Class B)
    (hout : ∀ x, classOf B x = outside ↔ x ∉ H)
    (hin : ∀ x, classOf B x = inside ↔ x ∈ H ∧ x ≠ 0)
    (hm : 5 ≤ Fintype.card G) : negation (G := G) = 0 := by
  have h := index_two_orbit_partition_exponent_two B H hindex outside inside hout hin hm
  ext x
  change -x = x
  exact (eq_neg_of_add_eq_zero_left (by simpa only [two_nsmul] using h x)).symm

/-- Exact specialization to the exceptional predicate used by Theorem 7.1. -/
theorem indexTwoException_exponent_two
    (B : AddSubgroup (AddAut G)) (hneg : negation (G := G) ∈ B)
    (hm : 5 ≤ Fintype.card G)
    (hex : (inverseStablePartition B hneg).IndexTwoException) :
    ∀ x : G, (2 : ℕ) • x = 0 := by
  obtain ⟨H, d, c, hindex, hd, hc, hdc, hout, hin⟩ := hex
  exact index_two_orbit_partition_exponent_two B H hindex d c hout hin hm

end Sunlet.OrbitClasses
