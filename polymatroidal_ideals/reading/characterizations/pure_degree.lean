import Characterizations.OrderExistence

/-! # Universal pure reverse lexicographic quotients force one degree -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

def boxFamily (B : Family V) (C : Exponent V) : Family V := B.filter (· ≤ C)

@[simp] theorem mem_boxFamily (B : Family V) (C a : Exponent V) :
    a ∈ boxFamily B C ↔ a ∈ B ∧ a ≤ C := by simp [boxFamily]

theorem antichain_boxFamily {B : Family V} (hB : Antichain B) (C : Exponent V) :
    Antichain (boxFamily B C) := fun a ha b hb hab =>
  hB a ((mem_boxFamily _ _ _).mp ha).1 b ((mem_boxFamily _ _ _).mp hb).1 hab

theorem witness_boxFamily {B : Family V} {r : GeneratorOrder V}
    (hW : QuotientWitness B r) (C : Exponent V) : QuotientWitness (boxFamily B C) r := by
  intro a ha b hb hab
  obtain ⟨haB, haC⟩ := (mem_boxFamily _ _ _).mp ha
  obtain ⟨hbB, hbC⟩ := (mem_boxFamily _ _ _).mp hb
  obtain ⟨w, hw, hwr, i, hwi, hai⟩ := hW a haB b hbB hab
  exact ⟨w, (mem_boxFamily _ _ _).mpr ⟨hw, (witness_le_sup hwi hai).trans
    (sup_le haC hbC)⟩, hwr, i, hwi, hai⟩

/-- Lemma 3.8, expressed with ordinary polynomial colon ideals. -/
theorem linearQuotients_boxFamily {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (hL : HasLinearQuotients k B r) (C : Exponent V) :
    HasLinearQuotients k (boxFamily B C) r :=
  linearQuotients_of_witness (witness_boxFamily (witness_of_linearQuotients hB hirr hL) C)

theorem witness_degree_le {B : Family V} (hB : Antichain B)
    {w b : Exponent V} (hw : w ∈ B) (hb : b ∈ B) {i : V}
    (h : w - b = Finsupp.single i 1) : w.degree ≤ b.degree := by
  have hle := sub_single_le_add h
  have hd := degree_mono hle
  simp only [map_add, Finsupp.degree_single] at hd
  by_contra hbad
  have heq : w.degree = (b + Finsupp.single i 1).degree := by
    simp only [map_add, Finsupp.degree_single]
    omega
  have hwEq := eq_of_le_of_degree_eq hle heq
  have hbEq := hB b hb w hw (hwEq ▸ le_add_right le_rfl)
  have hwi := sub_single_receiver h
  rw [hbEq] at hwi
  omega

/-- Lemma 3.7: the first generator has the least total degree. -/
theorem first_generator_minimum_degree {B : Family V} (hB : Antichain B)
    {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a) (hW : QuotientWitness B r)
    (a : Exponent V) (ha : a ∈ B) (hfirst : ∀ b ∈ B, ¬ r b a) :
    ∀ b ∈ B, a.degree ≤ b.degree := by
  intro b hb
  generalize hm : (preceding B r b).card = m
  induction m using Nat.strong_induction_on generalizing b with
  | h m ih =>
    by_cases he : a = b
    · subst b; exact le_rfl
    have hab : r a b := (htotal a b he).resolve_right (hfirst b hb)
    obtain ⟨w, hw, hwr, i, hwi, _⟩ := hW a ha b hb hab
    have hlt := preceding_card_lt hirr htrans hw hwr
    exact (ih _ (by omega) w hw rfl).trans (witness_degree_le hB hw hb hwi)

theorem exists_first_generator {B : Family V} (hne : B.Nonempty)
    {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a)
    (htrans : ∀ {a b c}, r a b → r b c → r a c) :
    ∃ a ∈ B, ∀ b ∈ B, ¬ r b a := by
  obtain ⟨a, ha, hmin⟩ := B.exists_min_image (fun b => (preceding B r b).card) hne
  refine ⟨a, ha, ?_⟩
  intro b hb hba
  exact (not_lt_of_ge (hmin b hb)) (preceding_card_lt hirr htrans hb hba)

def LastVariable (o : VariableOrder V) (i : V) : Prop := ∀ j, j ≠ i → o j < o i

theorem exists_lastVariable (i : V) : ∃ o : VariableOrder V, LastVariable o i := by
  obtain ⟨o, ho⟩ := exists_order_refining (fun j : V => if j = i then 1 else 0)
  exact ⟨o, fun j hji => ho j i (by simp [hji])⟩

/-- Lemma 3.9. The selected last-variable orders need not be the same orders
for different variables, and no degree hypothesis is assumed. -/
theorem equigenerated_of_lastVariable_tests {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hne : B.Nonempty) (hB : Antichain B)
    (hL : ∀ i : V, ∃ o : VariableOrder V, LastVariable o i ∧
      HasLinearQuotients k B (variableRevlex o)) : ∃ d, Equigenerated B d := by
  obtain ⟨a₀, ha₀, hmin⟩ := B.exists_min_image Finsupp.degree hne
  let d := a₀.degree
  refine ⟨d, ?_⟩
  intro b hb
  have hdb : d ≤ b.degree := hmin b hb
  by_contra hbd
  have hbd' : d < b.degree := by omega
  let D := B.filter (fun a => a.degree = d)
  have hD : D.Nonempty := ⟨a₀, mem_filter.mpr ⟨ha₀, rfl⟩⟩
  obtain ⟨a, haD, hdelta⟩ := D.exists_min_image (fun a => (a - b).degree) hD
  obtain ⟨ha, had⟩ := mem_filter.mp haD
  have hnot : ¬ a ≤ b := by
    intro hab
    have he := hB a ha b hb hab
    have hh := congrArg Finsupp.degree he
    omega
  obtain ⟨i, hi⟩ : ∃ i, b i < a i := by
    change ¬ ∀ i, a i ≤ b i at hnot
    simpa only [not_forall, not_le] using hnot
  let C := a ⊔ b
  have haC : a ∈ boxFamily B C := (mem_boxFamily _ _ _).mpr ⟨ha, le_sup_left⟩
  have hbC : b ∈ boxFamily B C := (mem_boxFamily _ _ _).mpr ⟨hb, le_sup_right⟩
  have hfix {a' : Exponent V} (ha' : a' ∈ boxFamily B C) (hd' : a'.degree = d) : a' i = a i := by
    obtain ⟨ha'B, ha'C⟩ := (mem_boxFamily _ _ _).mp ha'
    have hle : a' - b ≤ a - b := by
      intro x
      have hh := ha'C x
      simp only [C, Finsupp.sup_apply, Finsupp.tsub_apply] at hh ⊢
      omega
    have hdeg : (a' - b).degree = (a - b).degree :=
      le_antisymm (degree_mono hle) (hdelta a' (mem_filter.mpr ⟨ha'B, hd'⟩))
    have he := congrArg (fun c : Exponent V => c i) (eq_of_le_of_degree_eq hle hdeg)
    simp only [Finsupp.tsub_apply] at he
    omega
  obtain ⟨o, holast, hoL⟩ := hL i
  have hW := witness_boxFamily (witness_of_linearQuotients hB (variableRevlex_irrefl o) hoL) C
  obtain ⟨w, hw, hfirst⟩ := exists_first_generator ⟨a, haC⟩ (variableRevlex_irrefl o)
    (fun {_ _ _} => variableRevlex_trans o)
  have hwd : w.degree = d := by
    have hlo := hmin w ((mem_boxFamily _ _ _).mp hw).1
    have hhi := first_generator_minimum_degree (antichain_boxFamily hB C)
      (variableRevlex_irrefl o) (fun {_ _ _} => variableRevlex_trans o)
      (variableRevlex_total o) hW w hw hfirst a haC
    omega
  apply hfirst b hbC
  refine ⟨i, ?_, ?_⟩
  · rw [hfix hw hwd]
    exact hi
  · intro j hij
    by_cases hji : j = i
    · subst j; exact (lt_irrefl _ hij).elim
    · exact (not_lt_of_gt (holast j hji) hij).elim

/-- Corollary 3.10: universal pure reverse-lexicographic quotients characterize
polymatroidality without any equigeneration assumption. -/
theorem polymatroidal_iff_universal_pure_revlex {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) :
    IsPolymatroidal B ↔ ∀ o : VariableOrder V, HasLinearQuotients k B (variableRevlex o) := by
  constructor
  · intro h o
    exact polymatroidal_variable_linearQuotients h.2 o
  · intro h
    by_cases hne : B.Nonempty
    · obtain ⟨d, hd⟩ := equigenerated_of_lastVariable_tests (k := k) hne hB (fun i => by
        obtain ⟨o, ho⟩ := exists_lastVariable i
        exact ⟨o, ho, h o⟩)
      exact (polymatroidal_iff_universal_revlex hd).mpr h
    · have hzero : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst B
      exact ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩

end Characterizations
