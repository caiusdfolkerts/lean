module

public import sunlet.fine_invariant_kernel

/-! The arbitrary automorphism-orbit clause of Theorem 7.1, assembled from
actual orbit quotients, initial monomials, and the two exact exceptions. -/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitClasses

attribute [local instance 0] Classical.propDecidable

variable {G : Type*} [AddCommGroup G] [Fintype G]

def OrbitIndexTwoException (B : AddSubgroup (AddAut G)) : Prop :=
  ∃ (H : AddSubgroup G) (d c : Class B), H.index = 2 ∧
    d ≠ classOf B 0 ∧ c ≠ classOf B 0 ∧ d ≠ c ∧
    (∀ a, classOf B a = d ↔ a ∉ H) ∧
    (∀ a, classOf B a = c ↔ a ∈ H ∧ a ≠ 0)

def partitionOfStable (B : AddSubgroup (AddAut G))
    (hstable : ∀ a, classOf B (-a) = classOf B a) :
    OrbitHeight.InverseStablePartition G (Class B) where
  classOf := classOf B
  surjective := classOf_surjective B
  zeroClass := classOf B 0
  zero_iff := zero_class_iff B
  neg_class := hstable

theorem stable_of_two_classes (B : AddSubgroup (AddAut G))
    (hr : Fintype.card (Class B) = 2) : ∀ a, classOf B (-a) = classOf B a := by
  classical
  have hc : Fintype.card {i : Class B // i ≠ classOf B 0} = 1 := by
    simpa only [Fintype.card_subtype_eq,hr] using
      Fintype.card_subtype_compl (fun i : Class B => i = classOf B 0)
  haveI : Subsingleton {i : Class B // i ≠ classOf B 0} :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  intro a
  by_cases ha : a = 0
  · simp [ha]
  · have hqa : classOf B a ≠ classOf B 0 := fun h => ha ((zero_class_iff B a).mp h)
    have hqna : classOf B (-a) ≠ classOf B 0 := by
      intro h
      exact ha (neg_eq_zero.mp ((zero_class_iff B (-a)).mp h))
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨classOf B (-a),hqna⟩ : {i : Class B // i ≠ classOf B 0}) ⟨classOf B a,hqa⟩)

theorem stable_of_index_two_exception (B : AddSubgroup (AddAut G))
    (hm : 5 ≤ Fintype.card G) (hex : OrbitIndexTwoException B) :
    ∀ a, classOf B (-a) = classOf B a := by
  obtain ⟨H,d,c,hindex,hd,hc,hdc,hout,hin⟩ := hex
  have hg := index_two_orbit_partition_exponent_two B H hindex d c hout hin hm
  intro a
  have ha : -a = a :=
    (eq_neg_of_add_eq_zero_left (by simpa only [two_nsmul] using hg a)).symm
  rw [ha]

/-- The exceptional fiber description has precisely the three orbit classes
in the manuscript, including the singleton zero class. -/
theorem orbit_index_two_exception_card (B : AddSubgroup (AddAut G))
    (hm : 5 ≤ Fintype.card G) (hex : OrbitIndexTwoException B) :
    Fintype.card (Class B) = 3 := by
  classical
  letI : LinearOrder (Class B) := LinearOrder.lift' (Fintype.equivFin (Class B))
    (Fintype.equivFin (Class B)).injective
  exact (partitionOfStable B (stable_of_index_two_exception B hm hex)).index_two_exception_card hex

theorem nonstable_coarse_two_dimension {K : Type*} [Field K] [Infinite K]
    (B : AddSubgroup (AddAut G)) (hm : 5 ≤ Fintype.card G)
    (hr : Fintype.card (Class (withNegation B)) = 2)
    (hstable : ¬ ∀ a, classOf B (-a) = classOf B a) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) (classOf B)))) =
        (5 * Fintype.card (Class B) - 4 : ℕ) := by
  classical
  push_neg at hstable
  obtain ⟨a,ha⟩ := hstable
  have ha0 : a ≠ 0 := by intro h; subst a; exact ha (by simp)
  have hc : classOf B a ≠ classOf B 0 := fun h => ha0 ((zero_class_iff B a).mp h)
  have hd : classOf B (-a) ≠ classOf B 0 := by
    intro h; exact ha0 (neg_eq_zero.mp ((zero_class_iff B (-a)).mp h))
  have hgen := orbit_fiber_generates_of_coarse_two B hr (classOf B a) hc
  have hgen' := orbit_fiber_generates_of_coarse_two B hr (classOf B (-a)) hd
  have htwo := orbit_fiber_nontrivial_of_coarse_two B hr (classOf B a) hc hm
  have htwo' := orbit_fiber_nontrivial_of_coarse_two B hr (classOf B (-a)) hd hm
  apply StableSupport.dimension_of_generating_supports (classOf B) (classOf_surjective B)
    (classOf B 0) (zero_class_iff B) {classOf B a} {classOf B (-a)}
  · simpa only [Set.mem_singleton_iff] using Ne.symm hc
  · simpa only [Set.mem_singleton_iff] using Ne.symm hd
  · exact Set.disjoint_singleton.mpr ha.symm
  · have he : classOf B ⁻¹' {classOf B a} = {x : G | classOf B x = classOf B a} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [he]
    exact hgen
  · have he : classOf B ⁻¹' {classOf B (-a)} = {x : G | classOf B x = classOf B (-a)} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [he]
    exact hgen'
  · obtain ⟨x,hx,y,hy,hxy⟩ := htwo
    exact ⟨x,hx,y,hy,hxy⟩
  · obtain ⟨x,hx,y,hy,hxy⟩ := htwo'
    exact ⟨x,hx,y,hy,hxy⟩

/-- The complete arbitrary-automorphism-orbit dimension formula on the actual
pair-indexed five-family polynomial map, in every characteristic. -/
theorem arbitrary_orbit_imageClosure_dimension {K : Type*} [Field K] [IsAlgClosed K]
    (B : AddSubgroup (AddAut G)) (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (G × G) K ⧸ MvPolynomial.vanishingIdeal K
      (PolynomialImage.closure (Identified.coordinatePolynomial (K := K) (classOf B)))) =
      (if Fintype.card (Class B) = 2 then (5 : ℕ)
        else if OrbitIndexTwoException B then 10 else 5 * Fintype.card (Class B) - 4) := by
  classical
  letI : LinearOrder (Class B) := LinearOrder.lift' (Fintype.equivFin (Class B))
    (Fintype.equivFin (Class B)).injective
  by_cases hstable : ∀ a, classOf B (-a) = classOf B a
  · exact (partitionOfStable B hstable).inverse_stable_imageClosure_dimension hm
  · have hr : Fintype.card (Class B) ≠ 2 := fun h => hstable (stable_of_two_classes B h)
    have hex : ¬ OrbitIndexTwoException B := fun h => hstable (stable_of_index_two_exception B hm h)
    simp only [if_neg hr,if_neg hex]
    let D := Class (withNegation B)
    letI : LinearOrder D := LinearOrder.lift' (Fintype.equivFin D)
      (Fintype.equivFin D).injective
    let P := inverseStablePartition (withNegation B) (negation_mem_withNegation B)
    by_cases hD : Fintype.card D = 2
    · exact nonstable_coarse_two_dimension B hm hD hstable
    · have hno : ¬ P.IndexTwoException := by
        intro h
        have hb := coarse_indexTwoException_withNegation_eq B hm h
        have hn : negation (G := G) ∈ B := hb ▸ negation_mem_withNegation B
        exact hstable (classOf_neg B hn)
      haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨a,ha⟩ := exists_ne (0 : G)
      have hne : P.classOf a ≠ P.zeroClass := fun h => ha ((P.zero_iff a).mp h)
      haveI : Nontrivial D := ⟨⟨P.classOf a,P.zeroClass,hne⟩⟩
      have hcard := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial D)
      have hthree : 3 ≤ Fintype.card D := by omega
      rcases P.good_order_or_singletons hthree hno with hinj | ⟨O,hmin,hgood⟩
      · apply Identified.imageClosure_dimension_of_bijective (classOf B) _ hm
        refine ⟨?_,classOf_surjective B⟩
        intro a b hab
        exact hinj (congrArg (coarsenClass B) hab)
      · letI : LinearOrder D := O
        exact FineOddKernel.dimension_of_coarse_good_order P
          (classOf B) (classOf_surjective B) (classOf B 0) (zero_class_iff B)
          (coarsenClass B) (coarsen_classOf B) (negClass B) (negClass_classOf B)
          (fun a b h => (classOf_withNegation_eq_iff B a b).mp h) hmin hgood hm

/-- The full Theorem 7.1 in the paper's original six-family flow-indexed
coordinates. Equality of entire affine images, including zero parameters,
and the coordinate-ring equivalence are already proved. -/
theorem paper_theorem_7_1 {K : Type*} [Field K] [IsAlgClosed K]
    (B : AddSubgroup (AddAut G)) (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex G) K ⧸
      MvPolynomial.vanishingIdeal K
        (ClassGroupCoordinates.tripleImageClosure (K := K) (classOf B))) =
      (if Fintype.card (Class B) = 2 then (5 : ℕ)
        else if OrbitIndexTwoException B then 10 else 5 * Fintype.card (Class B) - 4) := by
  rw [ringKrullDim_eq_of_ringEquiv
    (ClassGroupCoordinates.flowCoordinateRingEquiv (K := K) (classOf B)).toRingEquiv]
  rw [ClassGroupCoordinates.imageClosure_eq_polynomial (classOf B) (negClass B)
    (negClass_classOf B)]
  exact arbitrary_orbit_imageClosure_dimension B hm

end Sunlet.OrbitClasses
