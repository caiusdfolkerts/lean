module

public import sunlet.arbitrary_orbit_classification
public import Mathlib.Data.ZMod.Aut
public import Mathlib.Algebra.Field.ZMod

/-!
# Cyclic automorphism-orbit models

The group is the literal additive group of `ZMod n`. The exceptional two-orbit
case is characterized by primality of `n` and equality of the acting subgroup
with the full automorphism group. The index-two exception is excluded by the
already proved exponent-two rigidity theorem.
-/

@[expose] public section
noncomputable section

namespace Sunlet.OrbitClasses

attribute [local instance 0] Classical.propDecidable

private theorem nonzero_classes_eq_of_card_two
    {G : Type*} [AddCommGroup G] [Fintype G]
    (B : AddSubgroup (AddAut G)) (hr : Fintype.card (Class B) = 2)
    (a b : G) (ha : a ≠ 0) (hb : b ≠ 0) : classOf B a = classOf B b := by
  classical
  have hc : Fintype.card {i : Class B // i ≠ classOf B 0} = 1 := by
    simpa only [Fintype.card_subtype_eq, hr] using
      Fintype.card_subtype_compl (fun i : Class B => i = classOf B 0)
  letI : Subsingleton {i : Class B // i ≠ classOf B 0} :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hqa : classOf B a ≠ classOf B 0 := fun h => ha ((zero_class_iff B a).mp h)
  have hqb : classOf B b ≠ classOf B 0 := fun h => hb ((zero_class_iff B b).mp h)
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨classOf B a, hqa⟩ : {i : Class B // i ≠ classOf B 0}) ⟨classOf B b, hqb⟩)

/-- An additive automorphism of `ZMod n` is determined by the image of `1`.
The proof uses Mathlib's actual automorphism/unit equivalence. -/
theorem zmod_addAut_ext_one (n : ℕ) (φ ψ : AddAut (ZMod n))
    (h : φ 1 = ψ 1) : φ = ψ := by
  apply (ZMod.AddAutEquivUnits n).injective
  apply Additive.toMul.injective
  apply Units.ext
  exact h

/-- The image of `1` under any additive automorphism of `ZMod n` is a unit. -/
theorem zmod_addAut_one_isUnit (n : ℕ) (φ : AddAut (ZMod n)) :
    IsUnit (φ 1) :=
  ⟨(ZMod.AddAutEquivUnits n φ).toMul, rfl⟩

theorem cyclic_two_classes_iff_prime_full (n : ℕ) [NeZero n]
    (hn : 5 ≤ n) (B : AddSubgroup (AddAut (ZMod n))) :
    Fintype.card (Class B) = 2 ↔ n.Prime ∧ B = ⊤ := by
  classical
  letI : Fact (1 < n) := ⟨by omega⟩
  constructor
  · intro hr
    have hunit (x : ZMod n) (hx : x ≠ 0) : IsUnit x := by
      obtain ⟨φ, hφ⟩ := (classOf_eq_iff B 1 x).mp
        (nonzero_classes_eq_of_card_two B hr 1 x one_ne_zero hx)
      exact hφ ▸ zmod_addAut_one_isUnit n φ.val
    have hprime : n.Prime := by
      apply Nat.prime_def_lt.mpr
      refine ⟨by omega, ?_⟩
      intro m hmn hdiv
      have hm0 : m ≠ 0 := by
        intro hm
        subst m
        have : n = 0 := Nat.eq_zero_of_zero_dvd hdiv
        omega
      have hcast : (m : ZMod n) ≠ 0 := by
        intro hz
        have hnm : n ∣ m := (ZMod.natCast_eq_zero_iff m n).mp hz
        have hle : n ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hnm
        omega
      have hcop : m.Coprime n := (ZMod.isUnit_iff_coprime m n).mp (hunit _ hcast)
      exact Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdiv
    refine ⟨hprime, top_unique ?_⟩
    intro ψ _
    have hψ : ψ (1 : ZMod n) ≠ 0 := by
      intro h
      exact one_ne_zero (ψ.injective (h.trans (map_zero ψ).symm))
    obtain ⟨φ, hφ⟩ := (classOf_eq_iff B 1 (ψ 1)).mp
      (nonzero_classes_eq_of_card_two B hr 1 (ψ 1) one_ne_zero hψ)
    have he : φ.val = ψ := zmod_addAut_ext_one n φ.val ψ hφ
    exact he ▸ φ.property
  · rintro ⟨hp, rfl⟩
    letI : Fact n.Prime := ⟨hp⟩
    have hone (x : ZMod n) (hx : x ≠ 0) :
        classOf (⊤ : AddSubgroup (AddAut (ZMod n))) x = classOf ⊤ 1 := by
      symm
      apply (classOf_eq_iff ⊤ 1 x).mpr
      refine ⟨⟨AddAut.mulLeft (Units.mk0 x hx), AddSubgroup.mem_top _⟩, ?_⟩
      change x * 1 = x
      exact mul_one x
    have hu : (Finset.univ : Finset (Class (⊤ : AddSubgroup (AddAut (ZMod n))))) =
        {classOf ⊤ 0, classOf ⊤ 1} := by
      ext c
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      obtain ⟨x, rfl⟩ := classOf_surjective ⊤ c
      by_cases hx : x = 0
      · exact Or.inl (congrArg (classOf ⊤) hx)
      · exact Or.inr (hone x hx)
    have hne : classOf (⊤ : AddSubgroup (AddAut (ZMod n))) 0 ≠ classOf ⊤ 1 := by
      intro h
      exact one_ne_zero ((zero_class_iff ⊤ (1 : ZMod n)).mp h.symm)
    rw [← Finset.card_univ, hu, Finset.card_pair hne]

/-- The three-orbit index-two exception cannot occur in a cyclic group of
order at least five. Evaluating exponent-two rigidity at `1` would force
`n ∣ 2`. -/
theorem cyclic_no_index_two_exception (n : ℕ) [NeZero n]
    (hn : 5 ≤ n) (B : AddSubgroup (AddAut (ZMod n))) :
    ¬ OrbitIndexTwoException B := by
  intro h
  obtain ⟨H, d, c, hindex, hd, hc, hdc, hout, hin⟩ := h
  have hm : 5 ≤ Fintype.card (ZMod n) := by simpa only [ZMod.card] using hn
  have hh := index_two_orbit_partition_exponent_two B H hindex d c hout hin hm (1 : ZMod n)
  have htwo : (2 : ZMod n) = 0 := by simpa only [two_nsmul, one_add_one_eq_two] using hh
  have hdiv : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp htwo
  have hle : n ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

theorem cyclic_orbit_imageClosure_dimension {K : Type*} [Field K] [IsAlgClosed K]
    (n : ℕ) [NeZero n] (hn : 5 ≤ n) (B : AddSubgroup (AddAut (ZMod n))) :
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex (ZMod n)) K ⧸
      MvPolynomial.vanishingIdeal K
        (ClassGroupCoordinates.tripleImageClosure (K := K) (classOf B))) =
      (if n.Prime ∧ B = ⊤ then (5 : ℕ) else 5 * Fintype.card (Class B) - 4) := by
  rw [paper_theorem_7_1 B (by simpa only [ZMod.card] using hn)]
  rw [if_neg (cyclic_no_index_two_exception n hn B)]
  simp only [cyclic_two_classes_iff_prime_full n hn B]

/-- Corollary 7.4 in the original six-family flow coordinates. `NeZero n` is
constructed from the stated lower bound, so it is not an additional hypothesis. -/
theorem paper_corollary_7_4 {K : Type*} [Field K] [IsAlgClosed K]
    (n : ℕ) (hn : 5 ≤ n) (B : AddSubgroup (AddAut (ZMod n))) :
    letI : NeZero n := ⟨by omega⟩
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex (ZMod n)) K ⧸
      MvPolynomial.vanishingIdeal K
        (ClassGroupCoordinates.tripleImageClosure (K := K) (classOf B))) =
      (if n.Prime ∧ B = ⊤ then (5 : ℕ) else 5 * Fintype.card (Class B) - 4) := by
  letI : NeZero n := ⟨by omega⟩
  exact cyclic_orbit_imageClosure_dimension n hn B

end Sunlet.OrbitClasses
