import Characterizations.PairMass
import Characterizations.FiniteCover

/-! # The sharp rejection fraction, including independent repeated tests -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def rejectionFraction (k : Type*) [CommSemiring k] (B : Family V) : ℝ :=
  finiteFraction (fun o : VariableOrder V => ¬ HasLinearQuotients k B (variableRevlex o))

def patternMass (s : ℕ) : ℝ := 1 / ((s+3)*(s+2).choose 2 : ℕ)

/-- Theorem 5.6: every nonpolymatroidal generator family has at least the
probability of one full active order pattern. -/
theorem rejection_fraction_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) :
    patternMass (min (d-1) (Fintype.card V-3)) ≤ rejectionFraction k B := by
  let G : Set (VariableOrder V) := {o | HasLinearQuotients k B (variableRevlex o)}
  by_cases hpatterns : CoversPatterns (min (d-1) (Fintype.card V-3)) G
  · have hnpairs : ¬ (Fintype.card V-1 ≤ d → CoversFinalPairs G) := by
      intro hpairs
      exact hnot ⟨⟨d,hB⟩,exchange_of_degree_coverage (k := k) hB hcard G hpatterns hpairs (fun _ h => h)⟩
    simp only [CoversFinalPairs,not_forall] at hnpairs
    obtain ⟨hdlarge,i,j,hij,hbad⟩ := hnpairs
    have hmass : patternMass (min (d-1) (Fintype.card V-3)) =
        1 / (Fintype.card V * (Fintype.card V-1).choose 2 : ℕ) := by
      have h1 : min (d-1) (Fintype.card V-3) = Fintype.card V-3 := by omega
      have h2 : Fintype.card V-3+3 = Fintype.card V := by omega
      have h3 : Fintype.card V-3+2 = Fintype.card V-1 := by omega
      simp only [patternMass,h1,h2,h3]
    rw [hmass]
    apply (finalPair_probability_lower_bound hcard hij).trans
    apply finiteFraction_mono
    intro o ho hgood
    exact hbad ⟨o,hgood,ho⟩
  · simp only [CoversPatterns,not_forall] at hpatterns
    obtain ⟨i,q,j,hiq,hij,hqj,C,hC,hCc,hbad⟩ := hpatterns
    have hm : patternMass (min (d-1) (Fintype.card V-3)) =
        finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) := by
      rw [orderPattern_probability C i q j hiq hij hqj hC,hCc]
      rfl
    rw [hm]
    apply finiteFraction_mono
    intro o ho hgood
    exact hbad ⟨o,hgood,ho⟩

/-- The lower bound is attained by an actual capped monomial ideal, extended
by unused variables and multiplied by a common monomial when necessary. -/
theorem exists_sharp_rejection_family {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      rejectionFraction k B = patternMass (min (d-1) (Fintype.card V-3)) := by
  obtain ⟨i,q,j,hiq,hij,hqj⟩ := exists_three_distinct (V := V) (by omega)
  have hcapcard : (tripleCap i q j).card = Fintype.card V-3 := by
    rw [tripleCap,card_sdiff_of_subset (subset_univ _)]
    simp [hiq,hij,hqj]
  obtain ⟨C,hC,hCc⟩ := exists_subset_card_eq
    (show min (d-1) (Fintype.card V-3) ≤ (tripleCap i q j).card by omega)
  have hCne : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨B,hB,hnot,hiff⟩ := exists_pattern_isolator (k := k) C i q j hiq hij hqj hC hCne d (by omega)
  refine ⟨B,hB,hnot,?_⟩
  calc
    rejectionFraction k B = finiteFraction (fun o : VariableOrder V => OrderPattern o C i q j) :=
      finiteFraction_congr (fun o => by rw [hiff o]; simp)
    _ = _ := by rw [orderPattern_probability C i q j hiq hij hqj hC,hCc]; rfl

theorem patternMass_formula (s : ℕ) :
    patternMass s = 2 / (((s:ℝ)+1)*((s:ℝ)+2)*((s:ℝ)+3)) := by
  have hn := Nat.add_one_mul_choose_eq (s+1) 1
  have hn' : ((s+2).choose 2 : ℝ)*2 = ((s:ℝ)+1)*((s:ℝ)+2) := by
    have hh : (s+2).choose 2*2 = (s+1)*(s+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (s+2).choose 2 := by exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ s+2))
  unfold patternMass
  push_cast
  field_simp
  nlinarith

theorem rejection_fraction_displayed {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) :
    let t := min d (Fintype.card V-2)
    2 / ((t:ℝ)*((t:ℝ)+1)*((t:ℝ)+2)) ≤ rejectionFraction k B := by
  have hh := rejection_fraction_lower_bound (k := k) hB hd hcard hnot
  rw [patternMass_formula] at hh
  have he : min d (Fintype.card V-2) = min (d-1) (Fintype.card V-3)+1 := by omega
  simpa only [he,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1:ℝ)+1=2 by norm_num,show (1:ℝ)+2=3 by norm_num] using hh

/-- The sharp examples attain exactly the rational expression printed in
Theorem 5.6, for every allowed degree and number of variables. -/
theorem exists_sharp_rejection_displayed {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) :
    ∃ B : Family V, Equigenerated B d ∧ ¬ IsPolymatroidal B ∧
      let t := min d (Fintype.card V-2)
      rejectionFraction k B = 2 / ((t:ℝ)*((t:ℝ)+1)*((t:ℝ)+2)) := by
  obtain ⟨B,hB,hnot,heq⟩ := exists_sharp_rejection_family (k := k) d hd hcard
  refine ⟨B,hB,hnot,?_⟩
  rw [heq,patternMass_formula]
  have he : min d (Fintype.card V-2) = min (d-1) (Fintype.card V-3)+1 := by omega
  simp only [he,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1:ℝ)+1=2 by norm_num,show (1:ℝ)+2=3 by norm_num]

theorem independent_tests_miss_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hd : 2 ≤ d)
    (hcard : 4 ≤ Fintype.card V) (hnot : ¬ IsPolymatroidal B) (M : ℕ) :
    finiteFraction (fun f : Fin M → VariableOrder V =>
      ∀ j, HasLinearQuotients k B (variableRevlex (f j))) ≤
      (1-patternMass (min (d-1) (Fintype.card V-3)))^M := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let P := fun o : VariableOrder V => HasLinearQuotients k B (variableRevlex o)
  have hrej : rejectionFraction k B = 1-finiteFraction P := finiteFraction_not P
  have hbound := rejection_fraction_lower_bound (k := k) hB hd hcard hnot
  rw [hrej] at hbound
  rw [finiteFraction_all_trials M P]
  exact pow_le_pow_left₀ (finiteFraction_nonneg P) (by linarith) M

end Characterizations
