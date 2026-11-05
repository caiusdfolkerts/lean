import Characterizations.DegreeCoverage

/-! # Common monomial factors and unused variables preserve quotient tests -/

noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def translatedFamily (c : Exponent V) (B : Family V) : Family V := B.image (fun a => a + c)
def embeddedFamily (e : W ↪ V) (B : Family W) : Family V := B.image (Finsupp.embDomain e)

theorem translatedFamily_equigenerated {B : Family V} {d : ℕ} (hB : Equigenerated B d)
    (c : Exponent V) : Equigenerated (translatedFamily c B) (d + c.degree) := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
  simp [hB b hb]

theorem variableRevlex_add_iff (o : VariableOrder V) (a b c : Exponent V) :
    variableRevlex o (a + c) (b + c) ↔ variableRevlex o a b := by
  simp [variableRevlex, Finsupp.add_apply]

theorem translatedFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family V} {d : ℕ} (hB : Equigenerated B d) (c : Exponent V) (o : VariableOrder V) :
    HasLinearQuotients k (translatedFamily c B) (variableRevlex o) ↔
      HasLinearQuotients k B (variableRevlex o) := by
  rw [linearQuotients_iff_witness (translatedFamily_equigenerated hB c).antichain (variableRevlex_irrefl o),
    linearQuotients_iff_witness hB.antichain (variableRevlex_irrefl o)]
  constructor
  · intro h a ha b hb hab
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h (a+c) (mem_image.mpr ⟨a, ha, rfl⟩)
      (b+c) (mem_image.mpr ⟨b, hb, rfl⟩) ((variableRevlex_add_iff o a b c).mpr hab)
    obtain ⟨w, hw₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp hw
    refine ⟨w, hw₀, (variableRevlex_add_iff o w b c).mp hwb, i, ?_, ?_⟩
    · simpa only [add_tsub_add_eq_tsub_right] using hwi
    · simpa using hai
  · intro h a ha b hb hab
    obtain ⟨a, ha₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp ha
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp hb
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h a ha₀ b hb₀ ((variableRevlex_add_iff o a b c).mp hab)
    refine ⟨w+c, mem_image.mpr ⟨w, hw, rfl⟩, (variableRevlex_add_iff o w b c).mpr hwb,
      i, ?_, ?_⟩
    · simpa only [add_tsub_add_eq_tsub_right] using hwi
    · simpa using hai

theorem translatedFamily_polymatroidal_iff {B : Family V} {d : ℕ}
    (hB : Equigenerated B d) (c : Exponent V) :
    IsPolymatroidal (translatedFamily c B) ↔ IsPolymatroidal B := by
  rw [polymatroidal_iff_universal_revlex (k := ℚ) (translatedFamily_equigenerated hB c),
    polymatroidal_iff_universal_revlex (k := ℚ) hB]
  simp only [translatedFamily_linearQuotients_iff hB c]

theorem embeddedFamily_equigenerated {B : Family W} {d : ℕ} (hB : Equigenerated B d)
    (e : W ↪ V) : Equigenerated (embeddedFamily e B) d := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
  simpa [Finsupp.embDomain_eq_mapDomain] using hB b hb

theorem embDomain_exchange (e : W ↪ V) (a : Exponent W) (i j : W) :
    Finsupp.embDomain e (exchange a i j) = exchange (Finsupp.embDomain e a) (e i) (e j) := by
  simp [exchange, Finsupp.embDomain_add, Finsupp.embDomain_tsub, Finsupp.embDomain_single]

theorem embDomain_positive_range (e : W ↪ V) (a : Exponent W) {j : V}
    (hj : 0 < Finsupp.embDomain e a j) : ∃ x, e x = j := by
  by_contra hn
  simp [Finsupp.embDomain_apply, hn] at hj

theorem embeddedFamily_polymatroidal_implies {B : Family W} {d : ℕ}
    (hB : Equigenerated B d) (e : W ↪ V) (h : IsPolymatroidal (embeddedFamily e B)) :
    IsPolymatroidal B := by
  refine ⟨⟨d, hB⟩, ?_⟩
  intro a ha b hb i hi
  obtain ⟨j, hj, hw⟩ := h.2 (Finsupp.embDomain e a) (mem_image.mpr ⟨a, ha, rfl⟩)
    (Finsupp.embDomain e b) (mem_image.mpr ⟨b, hb, rfl⟩) (e i) (by simpa using hi)
  obtain ⟨j, rfl⟩ := embDomain_positive_range e b (lt_of_le_of_lt (Nat.zero_le _) hj)
  obtain ⟨w, hw, he⟩ := mem_image.mp hw
  have hew : w = exchange a i j := Finsupp.embDomain_injective e
    (he.trans (embDomain_exchange e a i j).symm)
  exact ⟨j, by simpa using hj, hew ▸ hw⟩

/-- Restriction of a variable permutation to the active variables, retaining
exactly their relative order. -/
def restrictedOrder (o : VariableOrder V) (e : W ↪ V) : VariableOrder W := by
  letI : LinearOrder W := LinearOrder.lift' (o ∘ e) (o.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq W rfl).symm.toEquiv

theorem restrictedOrder_lt_iff (o : VariableOrder V) (e : W ↪ V) (a b : W) :
    restrictedOrder o e a < restrictedOrder o e b ↔ o (e a) < o (e b) := by
  letI : LinearOrder W := LinearOrder.lift' (o ∘ e) (o.injective.comp e.injective)
  exact (Fintype.orderIsoFinOfCardEq W rfl).symm.lt_iff_lt

theorem embedded_revlex_iff (o : VariableOrder V) (e : W ↪ V) (a b : Exponent W) :
    variableRevlex o (Finsupp.embDomain e a) (Finsupp.embDomain e b) ↔
      variableRevlex (restrictedOrder o e) a b := by
  constructor
  · rintro ⟨i, hi, hafter⟩
    obtain ⟨i, rfl⟩ := embDomain_positive_range e b (lt_of_le_of_lt (Nat.zero_le _) hi)
    refine ⟨i, by simpa using hi, ?_⟩
    intro j hij
    simpa using hafter (e j) ((restrictedOrder_lt_iff o e i j).mp hij)
  · rintro ⟨i, hi, hafter⟩
    refine ⟨e i, by simpa using hi, ?_⟩
    intro j hij
    by_cases hj : ∃ x, e x = j
    · obtain ⟨j, rfl⟩ := hj
      simpa using hafter j ((restrictedOrder_lt_iff o e i j).mpr hij)
    · simp [Finsupp.embDomain_apply, hj]

theorem embeddedFamily_linearQuotients_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    {B : Family W} {d : ℕ} (hB : Equigenerated B d) (e : W ↪ V) (o : VariableOrder V) :
    HasLinearQuotients k (embeddedFamily e B) (variableRevlex o) ↔
      HasLinearQuotients k B (variableRevlex (restrictedOrder o e)) := by
  rw [linearQuotients_iff_witness (embeddedFamily_equigenerated hB e).antichain (variableRevlex_irrefl o),
    linearQuotients_iff_witness hB.antichain (variableRevlex_irrefl _)]
  constructor
  · intro h a ha b hb hab
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h (Finsupp.embDomain e a) (mem_image.mpr ⟨a, ha, rfl⟩)
      (Finsupp.embDomain e b) (mem_image.mpr ⟨b, hb, rfl⟩) ((embedded_revlex_iff o e a b).mpr hab)
    obtain ⟨w, hw₀, rfl⟩ := (Finset.mem_image (s := B) (f := Finsupp.embDomain e)).mp hw
    obtain ⟨i, rfl⟩ := embDomain_positive_range e a (lt_of_le_of_lt (Nat.zero_le _) hai)
    refine ⟨w, hw₀, (embedded_revlex_iff o e w b).mp hwb, i, ?_, by simpa using hai⟩
    apply Finsupp.embDomain_injective e
    simpa only [Finsupp.embDomain_tsub, Finsupp.embDomain_single] using hwi
  · intro h a ha b hb hab
    obtain ⟨a, ha₀, rfl⟩ := (Finset.mem_image (s := B) (f := Finsupp.embDomain e)).mp ha
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := Finsupp.embDomain e)).mp hb
    obtain ⟨w, hw, hwb, i, hwi, hai⟩ := h a ha₀ b hb₀ ((embedded_revlex_iff o e a b).mp hab)
    refine ⟨Finsupp.embDomain e w, mem_image.mpr ⟨w, hw, rfl⟩,
      (embedded_revlex_iff o e w b).mpr hwb, e i, ?_, by simpa using hai⟩
    simpa only [Finsupp.embDomain_tsub, Finsupp.embDomain_single] using
      congrArg (Finsupp.embDomain e) hwi

end Characterizations
