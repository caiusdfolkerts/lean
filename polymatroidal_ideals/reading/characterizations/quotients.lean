import Characterizations.ExchangeGraph
import CommAlg.Polymatroid.LinearQuotients

/-! # Literal colon ideals and the combinatorial variable-witness condition -/

noncomputable section

namespace Characterizations

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev GeneratorOrder (V : Type*) := Exponent V → Exponent V → Prop

def preceding (B : Family V) (r : GeneratorOrder V) (b : Exponent V) : Family V :=
  B.filter (fun a => r a b)

@[simp] theorem mem_preceding (B : Family V) (r : GeneratorOrder V) (a b : Exponent V) :
    a ∈ preceding B r b ↔ a ∈ B ∧ r a b := by simp [preceding]

def QuotientWitness (B : Family V) (r : GeneratorOrder V) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, r a b →
    ∃ w ∈ B, r w b ∧ ∃ i, w - b = Finsupp.single i 1 ∧ b i < a i

def HasLinearQuotients (k : Type*) [CommSemiring k]
    (B : Family V) (r : GeneratorOrder V) : Prop :=
  ∀ b ∈ B, ∃ D : Finset V,
    (monomialIdeal k (preceding B r b)).colon {MvPolynomial.monomial b (1 : k)} =
      variableIdeal (k := k) D

theorem sub_single_le_add {w b : Exponent V} {i : V}
    (h : w - b = Finsupp.single i 1) : w ≤ b + Finsupp.single i 1 := by
  intro x
  have hx := congrArg (fun a : Exponent V => a x) h
  simp only [Finsupp.tsub_apply, Finsupp.add_apply] at hx ⊢
  omega

theorem sub_single_receiver {w b : Exponent V} {i : V}
    (h : w - b = Finsupp.single i 1) : w i = b i + 1 := by
  have hx := congrArg (fun a : Exponent V => a i) h
  simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hx
  omega

theorem sub_single_of_le_add {w b : Exponent V} {i : V}
    (hle : w ≤ b + Finsupp.single i 1) (hn : ¬ w ≤ b) :
    w - b = Finsupp.single i 1 := by
  have hi : b i < w i := by
    by_contra hi
    apply hn
    intro x
    by_cases hx : x = i
    · subst x; omega
    · have hh := hle x
      simpa [Finsupp.single_apply, hx, Ne.symm hx] using hh
  ext x
  have hh := hle x
  by_cases hx : x = i
  · subst x
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, Finsupp.add_apply] at hh ⊢
    omega
  · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply,
      if_neg hx, if_neg (Ne.symm hx), Nat.add_zero] at hh ⊢
    omega

theorem witness_of_linearQuotients {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) {r : GeneratorOrder V}
    (hirr : ∀ a, ¬ r a a) (hL : HasLinearQuotients k B r) : QuotientWitness B r := by
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  intro a ha b hb hab
  obtain ⟨D, hD⟩ := hL b hb
  have hratio : MvPolynomial.monomial (a - b) (1 : k) ∈
      (monomialIdeal k (preceding B r b)).colon {MvPolynomial.monomial b 1} := by
    rw [mem_monomialIdeal_colon_iff]
    intro x hx
    have he : x = a - b := by simpa [eq_comm] using hx
    subst x
    exact ⟨a, (mem_preceding _ _ _ _).mpr ⟨ha, hab⟩, by
      intro i
      simp only [Finsupp.tsub_apply, Finsupp.add_apply]
      omega⟩
  rw [hD, mem_variableIdeal_iff] at hratio
  obtain ⟨i, hiD, hi⟩ := hratio (a - b) (by simp)
  have hvar : MvPolynomial.X i ∈ variableIdeal (k := k) D :=
    Ideal.subset_span ⟨i, hiD, rfl⟩
  rw [← hD, mem_monomialIdeal_colon_iff] at hvar
  obtain ⟨w, hw, hwb⟩ := hvar (Finsupp.single i 1) (by simp [MvPolynomial.X])
  obtain ⟨hwB, hwr⟩ := (mem_preceding _ _ _ _).mp hw
  have hnot : ¬ w ≤ b := by
    intro hle
    have he := hB w hwB b hb hle
    exact hirr b (he ▸ hwr)
  refine ⟨w, hwB, hwr, i, sub_single_of_le_add (by simpa [add_comm] using hwb) hnot, ?_⟩
  simp only [Finsupp.tsub_apply] at hi
  omega

def witnessVariables (B : Family V) (r : GeneratorOrder V) (b : Exponent V) : Finset V :=
  univ.filter (fun i => ∃ w ∈ B, r w b ∧ w - b = Finsupp.single i 1)

theorem linearQuotients_of_witness {k : Type*} [CommSemiring k]
    {B : Family V} {r : GeneratorOrder V} (hW : QuotientWitness B r) :
    HasLinearQuotients k B r := by
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  intro b hb
  refine ⟨witnessVariables B r b, ?_⟩
  ext f
  rw [mem_monomialIdeal_colon_iff, mem_variableIdeal_iff]
  have he (a : Exponent V) : Contains (preceding B r b) (a + b) ↔
      ∃ i ∈ witnessVariables B r b, 0 < a i := by
    constructor
    · rintro ⟨c, hc, hca⟩
      obtain ⟨hcB, hcr⟩ := (mem_preceding _ _ _ _).mp hc
      obtain ⟨w, hw, hwr, i, hwb, hi⟩ := hW c hcB b hb hcr
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, w, hw, hwr, hwb⟩, ?_⟩
      have hh := hca i
      simp only [Finsupp.add_apply] at hh
      omega
    · rintro ⟨i, hi, hai⟩
      obtain ⟨w, hw, hwr, hwb⟩ := (mem_filter.mp hi).2
      refine ⟨w, (mem_preceding _ _ _ _).mpr ⟨hw, hwr⟩, ?_⟩
      have hle := sub_single_le_add hwb
      intro x
      have hh := hle x
      by_cases hx : x = i
      · subst x
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hh ⊢
        omega
      · simp [Finsupp.single_apply, hx, Ne.symm hx] at hh
        simp only [Finsupp.add_apply]
        omega
  simp_rw [he]

theorem linearQuotients_iff_witness {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} (hB : Antichain B) {r : GeneratorOrder V} (hirr : ∀ a, ¬ r a a) :
    HasLinearQuotients k B r ↔ QuotientWitness B r :=
  ⟨witness_of_linearQuotients hB hirr, linearQuotients_of_witness⟩

theorem witness_is_exchange {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    {w b : Exponent V} (hw : w ∈ B) (hb : b ∈ B) {i : V}
    (h : w - b = Finsupp.single i 1) :
    ∃ j, i ≠ j ∧ 0 < b j ∧ w = exchange b j i := by
  have hi := sub_single_receiver h
  obtain ⟨j, hj⟩ := exists_surplus ((hB w hw).trans (hB b hb).symm) (show b i < w i by omega)
  have hij : i ≠ j := by intro he; subst j; omega
  have hle : w ≤ exchange b j i := by
    have hwb := sub_single_le_add h
    intro x
    have hh := hwb x
    by_cases hxi : x = i
    · subst x
      simp only [exchange_apply, if_neg hij, ite_true, Nat.sub_zero]
      omega
    by_cases hxj : x = j
    · subst x
      simp only [exchange_apply, ite_true, if_neg hij.symm, Nat.add_zero]
      omega
    · simpa [exchange_apply, hxi, hxj, Finsupp.single_apply,
        Ne.symm hxi] using hh
  exact ⟨j, hij, by omega, eq_of_le_of_degree_eq hle
    ((hB w hw).trans ((exchange_degree b j i (by omega)).trans (hB b hb)).symm)⟩

end Characterizations
