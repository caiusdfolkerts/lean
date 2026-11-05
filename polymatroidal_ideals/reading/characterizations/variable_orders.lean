import Characterizations.FourObstruction
import Mathlib.Data.Fintype.EquivFin

/-! # Variable permutations and pure reverse lexicographic tests -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev VariableOrder (V : Type*) [Fintype V] := V ≃ Fin (Fintype.card V)

def variableLinearOrder (o : VariableOrder V) : LinearOrder V :=
  LinearOrder.lift' o o.injective

def variableRevlex (o : VariableOrder V) (a b : Exponent V) : Prop :=
  ∃ i, a i < b i ∧ ∀ j, o i < o j → a j = b j

theorem variableRevlex_irrefl (o : VariableOrder V) (a : Exponent V) :
    ¬ variableRevlex o a a := by rintro ⟨i, hi, _⟩; exact (lt_irrefl _ hi)

theorem variableRevlex_trans (o : VariableOrder V) {a b c : Exponent V}
    (hab : variableRevlex o a b) (hbc : variableRevlex o b c) : variableRevlex o a c := by
  letI := variableLinearOrder o
  exact revlexBefore_trans hab hbc

theorem variableRevlex_total (o : VariableOrder V) (a b : Exponent V) (hab : a ≠ b) :
    variableRevlex o a b ∨ variableRevlex o b a := by
  letI := variableLinearOrder o
  exact revlexBefore_total hab

theorem variableRevlex_exchange (o : VariableOrder V) (b : Exponent V) {i j : V}
    (hji : o j < o i) (hi : 0 < b i) : variableRevlex o (exchange b i j) b := by
  letI := variableLinearOrder o
  exact exchange_revlexBefore b hji hi

theorem variableRevlex_exchange_iff (o : VariableOrder V) (b : Exponent V) {i j : V}
    (hij : i ≠ j) (hi : 0 < b i) :
    variableRevlex o (exchange b i j) b ↔ o j < o i := by
  refine ⟨?_, fun h => variableRevlex_exchange o b h hi⟩
  rintro ⟨x, hx, he⟩
  have hxi : x = i := by
    by_contra hxi
    simp only [exchange_apply, if_neg hxi, Nat.sub_zero] at hx
    split_ifs at hx <;> omega
  subst x
  by_contra hji
  have hlt : o i < o j := lt_of_le_of_ne (le_of_not_gt hji) (fun h => hij (o.injective h))
  have hh := he j hlt
  simp only [exchange_apply, if_neg hij.symm, ite_true, Nat.sub_zero] at hh
  omega

theorem polymatroidal_variable_linearQuotients {k : Type*} [CommSemiring k]
    {B : Family V} (hB : ExchangeAxiom B) (o : VariableOrder V) :
    HasLinearQuotients k B (variableRevlex o) := by
  letI := variableLinearOrder o
  intro b hb
  exact ⟨revlexColonVariables B b, revlex_colon_eq_variableIdeal hB hb⟩

def FinalPair (o : VariableOrder V) (i j : V) : Prop :=
  o i < o j ∧ ∀ h, h ≠ i → h ≠ j → o h < o i

def FinalTriple (o : VariableOrder V) (i q j : V) : Prop :=
  o i < o j ∧ o q < o j ∧
    ∀ h, h ≠ i → h ≠ q → h ≠ j → o h < o i ∧ o h < o q

def CoversFinalPairs (F : Set (VariableOrder V)) : Prop :=
  ∀ i j, i ≠ j → ∃ o ∈ F, FinalPair o i j

def CoversFinalTriples (F : Set (VariableOrder V)) : Prop :=
  ∀ i q j, i ≠ q → i ≠ j → q ≠ j → ∃ o ∈ F, FinalTriple o i q j

theorem FinalPair.no_after {o : VariableOrder V} {i j : V} (hF : FinalPair o i j) (h : V) :
    ¬ o j < o h := by
  intro hlt
  by_cases hhi : h = i
  · subst h; exact (not_lt_of_gt hF.1) hlt
  by_cases hhj : h = j
  · subst h; exact (lt_irrefl _ hlt)
  exact (lt_irrefl _ (hlt.trans ((hF.2 h hhi hhj).trans hF.1)))

theorem FinalTriple.no_after {o : VariableOrder V} {i q j : V}
    (hF : FinalTriple o i q j) (h : V) : ¬ o j < o h := by
  intro hlt
  by_cases hhi : h = i
  · subst h; exact (not_lt_of_gt hF.1) hlt
  by_cases hhq : h = q
  · subst h; exact (not_lt_of_gt hF.2.1) hlt
  by_cases hhj : h = j
  · subst h; exact (lt_irrefl _ hlt)
  exact (lt_irrefl _ (hlt.trans (((hF.2.2 h hhi hhq hhj).1).trans hF.1)))

/-- Lemma 3.4: final-pair orders force every prescribed single-receiver exchange. -/
theorem singletonExchange_of_finalPairs {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (F : Set (VariableOrder V))
    (hF : CoversFinalPairs F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : SingletonExchange B := by
  intro a ha b hb i hi j hj
  have hij : i ≠ j := by
    intro he
    subst j
    have hh := (hi i).mpr rfl
    omega
  obtain ⟨o, ho, hp⟩ := hF i j hij
  have hab : variableRevlex o a b :=
    ⟨j, hj, fun x hx => False.elim (hp.no_after x hx)⟩
  obtain ⟨w, hw, hwb, z, hwz, haz⟩ :=
    witness_of_linearQuotients hB.antichain (variableRevlex_irrefl o) (hL o ho) a ha b hb hab
  have hzi : z = i := (hi z).mp haz
  subst z
  obtain ⟨t, hit, ht, hew⟩ := witness_is_exchange hB hw hb hwz
  have horder : o i < o t :=
    (variableRevlex_exchange_iff o b hit.symm ht).mp (hew ▸ hwb)
  have htj : t = j := by
    by_contra htj
    exact (not_lt_of_gt (hp.2 t hit.symm htj)) horder
  simpa [hew, htj] using hw

/-- Theorem 3.6: the exact final-pair and final-triple patterns suffice. -/
theorem exchange_of_order_coverage {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (F : Set (VariableOrder V))
    (hne : F.Nonempty) (hpairs : CoversFinalPairs F) (htriples : CoversFinalTriples F)
    (hL : ∀ o ∈ F, HasLinearQuotients k B (variableRevlex o)) : ExchangeAxiom B := by
  obtain ⟨o₀, ho₀⟩ := hne
  have hconn := boxConnected_of_linearQuotients hB (variableRevlex_irrefl o₀)
    (fun {_ _ _} => variableRevlex_trans o₀) (variableRevlex_total o₀) (hL o₀ ho₀)
  have hsingle := singletonExchange_of_finalPairs hB F hpairs hL
  by_contra hfail
  obtain ⟨c, u, hc, hu, p, q, i, j, hpq, hpj, hqj, hip, hij, hiq,
    hp, hj, he, hni, hnq, hnqi, hniq⟩ := four_coordinate_obstruction hB hconn hsingle hfail
  subst u
  obtain ⟨o, ho, hfinal⟩ := htriples i q j hiq hij hqj
  have huc : variableRevlex o (exchange (exchange c p q) j i) c := by
    refine ⟨j, ?_, fun x hx => False.elim (hfinal.no_after x hx)⟩
    simp only [exchange_apply, if_neg hpj.symm, if_neg hqj.symm, if_neg hij.symm,
      ite_true, Nat.sub_zero, Nat.add_zero]
    omega
  obtain ⟨w, hw, hwc, z, hwz, hcz⟩ := witness_of_linearQuotients hB.antichain
    (variableRevlex_irrefl o) (hL o ho) _ hu c hc huc
  have hziq : z = i ∨ z = q := by
    by_contra hz
    push_neg at hz
    simp only [exchange_apply, if_neg hz.1, if_neg hz.2, Nat.add_zero] at hcz
    split_ifs at hcz <;> omega
  obtain ⟨t, hzt, ht, hew⟩ := witness_is_exchange hB hw hc hwz
  have horder : o z < o t :=
    (variableRevlex_exchange_iff o c hzt.symm ht).mp (hew ▸ hwc)
  rcases hziq with rfl | rfl
  · by_cases htj : t = j
    · exact hni (by simpa [hew, htj] using hw)
    by_cases htq : t = q
    · exact hnqi (by simpa [hew, htq] using hw)
    exact (not_lt_of_gt (hfinal.2.2 t hzt.symm htq htj).1) horder
  · by_cases htj : t = j
    · exact hnq (by simpa [hew, htj] using hw)
    by_cases hti : t = i
    · exact hniq (by simpa [hew, hti] using hw)
    exact (not_lt_of_gt (hfinal.2.2 t hti hzt.symm htj).2) horder

end Characterizations
