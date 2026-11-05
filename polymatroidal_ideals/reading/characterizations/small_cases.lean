import Characterizations.OptimalOrders

/-! # The small-variable and small-degree cases of the sharp test theorem -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem equigenerated_polymatroidal_of_card_le_one {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hcard : Fintype.card V ≤ 1) : IsPolymatroidal B := by
  refine ⟨⟨d,hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj⟩ := exists_surplus ((hB a ha).trans (hB b hb).symm) hi
  haveI : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hcard
  have he : i = j := Subsingleton.elim _ _
  subst j
  omega

theorem positive_coordinate_single_of_degree_one {a : Exponent V} {i : V}
    (ha : a.degree = 1) (hi : 0 < a i) : a = Finsupp.single i 1 := by
  apply (eq_of_le_of_degree_eq (a := Finsupp.single i 1) (b := a) ?_ (by simpa using ha.symm)).symm
  intro x
  by_cases hx : x = i
  · subst x; simp; omega
  · simp [Finsupp.single_apply, hx, Ne.symm hx]

theorem equigenerated_polymatroidal_of_degree_le_one {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hd : d ≤ 1) : IsPolymatroidal B := by
  refine ⟨⟨d,hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj⟩ := exists_surplus ((hB a ha).trans (hB b hb).symm) hi
  have hpos : 0 < d := by
    have hh := card_positive_except_le_degree (a := a) (S := ∅) (j := i) (by simp) (by omega) (by simp)
    rw [hB a ha] at hh
    simp only [card_empty, zero_add] at hh
    omega
  have hd1 : d = 1 := by omega
  have hai := positive_coordinate_single_of_degree_one ((hB a ha).trans hd1) (by omega : 0 < a i)
  have hbj := positive_coordinate_single_of_degree_one ((hB b hb).trans hd1) (by omega : 0 < b j)
  refine ⟨j,hj,?_⟩
  have he : exchange a i j = b := by simp [exchange, hai, hbj]
  exact he ▸ hb

theorem card_two_exhaust {i j : V} (hcard : Fintype.card V ≤ 2) (hij : i ≠ j) (x : V) :
    x = i ∨ x = j := by
  have he : (univ : Finset V) = {i,j} :=
    (eq_of_subset_of_card_le (subset_univ _) (by simp [hij]; omega)).symm
  have hx := mem_univ x
  rw [he] at hx
  simpa using hx

theorem exchange_of_boxConnected_card_two {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (hcard : Fintype.card V ≤ 2) (hconn : BoxConnected B) : ExchangeAxiom B := by
  intro a ha b hb i hi
  obtain ⟨j,hj⟩ := exists_surplus ((hB a ha).trans (hB b hb).symm) hi
  have hij : i ≠ j := by intro he; subst j; omega
  have hpath := hconn (a ⊔ b) a ha le_sup_left b hb le_sup_right
  rcases hpath.cases_head with he | ⟨c,hstep,_⟩
  · have hh := congrArg (fun x : Exponent V => x i) he
    omega
  obtain ⟨_,hc,_,hcbox,p,q,hpq,hp,hec⟩ := hstep
  have hpi : p = i := by
    rcases card_two_exhaust hcard hij p with hpI | hpJ
    · exact hpI
    · have hqi : q = i := (card_two_exhaust hcard hij q).resolve_right (fun hqJ => hpq (hpJ.trans hqJ.symm))
      have hcI := hcbox i
      rw [hec] at hcI
      simp only [exchange_apply, Finsupp.sup_apply] at hcI
      rw [hpJ, hqi] at hcI
      simp only [if_neg hij, ite_true, Nat.sub_zero] at hcI
      omega
  have hqj : q = j := (card_two_exhaust hcard hij q).resolve_left (fun hqI => hpq (hpi.trans hqI.symm))
  exact ⟨j,hj,by simpa [hec,hpi,hqj] using hc⟩

theorem one_order_suffices_card_two {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (hcard : Fintype.card V ≤ 2)
    (o : VariableOrder V) (hL : HasLinearQuotients k B (variableRevlex o)) : IsPolymatroidal B := by
  refine ⟨⟨d,hB⟩, exchange_of_boxConnected_card_two hB hcard ?_⟩
  exact boxConnected_of_linearQuotients hB (variableRevlex_irrefl o)
    (fun {_ _ _} => variableRevlex_trans o) (variableRevlex_total o) hL

theorem nonempty_order_family_card_two {k : Type*} [CommSemiring k] [Nontrivial k]
    (hcard : Fintype.card V ≤ 2) (F : Set (VariableOrder V)) (hne : F.Nonempty) :
    UniversalOrderTests k F := by
  intro B d hB hL
  obtain ⟨o,ho⟩ := hne
  exact one_order_suffices_card_two hB hcard o (hL o ho)

def purePairFamily (d : ℕ) (i j : V) : Family V := {Finsupp.single i d, Finsupp.single j d}

theorem purePair_equigenerated (d : ℕ) (i j : V) : Equigenerated (purePairFamily d i j) d := by
  intro a ha
  rcases (by simpa [purePairFamily] using ha : a = Finsupp.single i d ∨ a = Finsupp.single j d) with rfl | rfl <;> simp

theorem purePair_not_polymatroidal {d : ℕ} (hd : 2 ≤ d) {i j : V} (hij : i ≠ j) :
    ¬ IsPolymatroidal (purePairFamily d i j) := by
  intro h
  have ha : Finsupp.single i d ∈ purePairFamily d i j := by simp [purePairFamily]
  have hb : Finsupp.single j d ∈ purePairFamily d i j := by simp [purePairFamily]
  obtain ⟨q,hq,he⟩ := h.2 _ ha _ hb i (by simp [Finsupp.single_apply, hij, hij.symm]; omega)
  have hqj : q = j := by
    by_contra hn
    simp [Finsupp.single_apply, Ne.symm hn] at hq
  subst q
  rcases (by simpa [purePairFamily] using he :
    exchange (Finsupp.single i d) i j = Finsupp.single i d ∨
    exchange (Finsupp.single i d) i j = Finsupp.single j d) with he | he
  · have hh := congrArg (fun a : Exponent V => a j) he
    simp [exchange_apply, Finsupp.single_apply, hij, hij.symm] at hh
  · have hh := congrArg (fun a : Exponent V => a i) he
    simp [exchange_apply, Finsupp.single_apply, hij, hij.symm] at hh
    omega

end Characterizations
