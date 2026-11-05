import Characterizations.Rejection
import Characterizations.SmallTestNumbers

/-! # Sharp rejection probabilities in two and three variables -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rejection_fraction_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hnot : ¬ IsPolymatroidal B) : (1:ℝ)/6 ≤ rejectionFraction k B := by
  have hbad : ∃ o : VariableOrder V,¬HasLinearQuotients k B (variableRevlex o) := by
    by_contra hn
    apply hnot
    exact (polymatroidal_iff_universal_revlex hB).mpr (by simpa using hn)
  haveI : Nonempty {o : VariableOrder V // ¬HasLinearQuotients k B (variableRevlex o)} :=
    ⟨⟨hbad.choose,hbad.choose_spec⟩⟩
  have hc : 1 ≤ Nat.card {o : VariableOrder V // ¬HasLinearQuotients k B (variableRevlex o)} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  have hord : Nat.card (VariableOrder V) = 6 := by
    rw [Nat.card_eq_fintype_card,variableOrder_card,hcard]
    norm_num
  unfold rejectionFraction finiteFraction
  rw [hord]
  norm_num only [Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by norm_num)

theorem exists_sharp_rejection_three {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 3) (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧ rejectionFraction k B = (1:ℝ)/6 := by
  obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
  let c : Exponent V := Finsupp.single i (d-2)
  let B := translatedFamily c (pairFamily i j)
  have hbase : Equigenerated (pairFamily i j) 2 := by simpa [hcard] using pairFamily_equigenerated i j
  have hcdeg : c.degree = d-2 := by simp only [c,Finsupp.degree_single]
  have hgen : Equigenerated B d := by
    have hh := translatedFamily_equigenerated hbase c
    have he : 2+c.degree = d := by omega
    exact he ▸ hh
  obtain ⟨o₀,h₀⟩ := exists_finalPair i j hij
  have hiff (o : VariableOrder V) : ¬HasLinearQuotients k B (variableRevlex o) ↔ o = o₀ := by
    rw [translatedFamily_linearQuotients_iff hbase c o,pairFamily_linearQuotients_iff hij (by omega) o]
    simp only [not_not]
    exact ⟨fun hf => finalPair_unique_card_three hcard hij hf h₀,fun he => he ▸ h₀⟩
  refine ⟨B,hgen,?_,?_⟩
  · intro hp
    exact pairFamily_not_polymatroidal hij (by omega) ((translatedFamily_polymatroidal_iff hbase c).mp hp)
  · change finiteFraction (fun o : VariableOrder V => ¬HasLinearQuotients k B (variableRevlex o)) = _
    rw [finiteFraction_congr hiff]
    norm_num [finiteFraction,Nat.card_eq_fintype_card,variableOrder_card,hcard]

theorem rejection_fraction_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V ≤ 2) {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (hnot : ¬ IsPolymatroidal B) : rejectionFraction k B = 1 := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  have hbad (o : VariableOrder V) : ¬HasLinearQuotients k B (variableRevlex o) :=
    fun hL => hnot (one_order_suffices_card_two hB hcard o hL)
  change finiteFraction (fun o : VariableOrder V => ¬HasLinearQuotients k B (variableRevlex o)) = _
  rw [finiteFraction_congr (fun o => iff_true_intro (hbad o)),finiteFraction_true]

theorem exists_sharp_rejection_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V = 2) (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧ rejectionFraction k B = 1 := by
  obtain ⟨i,j,hij⟩ := exists_distinct_of_card_two (V := V) (by omega)
  refine ⟨purePairFamily d i j,purePair_equigenerated d i j,purePair_not_polymatroidal hd hij,?_⟩
  exact rejection_fraction_two (by omega) (purePair_equigenerated d i j) (purePair_not_polymatroidal hd hij)

end Characterizations
