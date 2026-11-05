import Characterizations.Resolution.Lift
import CommAlg.Polymatroid.Exponents

/-! The generator degree of an actual homogeneous free resolution. -/
noncomputable section
namespace Characterizations
open Classical Resolution MvPolynomial CommAlg.Polymatroid
open scoped BigOperators
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k]

namespace Resolution
lemma component_mul_below {a : MvPolynomial V k} {d e : ℕ}
    (ha : a.IsHomogeneous d) (b : MvPolynomial V k) (he : e < d) :
    homogeneousComponent e (a * b) = 0 := by
  induction b using MvPolynomial.induction_on' with
  | monomial f c =>
      have hf : (monomial f c : MvPolynomial V k).IsHomogeneous f.degree :=
        isHomogeneous_monomial c rfl
      rw [homogeneousComponent_of_mem (ha.mul hf)]
      simp only [show e ≠ d + f.degree by omega, ↓reduceIte]
  | add b c hb hc => simp [mul_add, map_add, hb, hc]
end Resolution

namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)
include P

lemma augmentation_component_below (x : P.Index 0 → MvPolynomial V k)
    {e : ℕ} (he : e < d) : homogeneousComponent e (P.augmentation x) = 0 := by
  have hx : x = ∑ j, x j • Pi.single j (1 : MvPolynomial V k) := by
    funext j
    simp [Pi.single_apply]
  rw [hx, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [map_smul, smul_eq_mul, mul_comm]
  exact component_mul_below (P.augmentation_homogeneous j) (x j) he

lemma degree_le_of_homogeneous_mem {y : MvPolynomial V k} {e : ℕ}
    (hy : y.IsHomogeneous e) (hy0 : y ≠ 0) (hyI : y ∈ I) : d ≤ e := by
  by_contra h
  have he : e < d := by omega
  have hr : y ∈ LinearMap.range P.augmentation := by rw [P.augmentation_range]; exact hyI
  obtain ⟨x, hx⟩ := hr
  have hh := P.augmentation_component_below x he
  rw [hx, homogeneousComponent_eq_self hy] at hh
  exact hy0 hh

variable [Nontrivial k]

omit P in
lemma equigenerated_of_monomial (B : Family V) (hB : Antichain B)
    (P : LinearResolution (monomialIdeal k B) d) : Equigenerated B d := by
  have hlo : ∀ a ∈ B, d ≤ a.degree := by
    intro a ha
    apply P.degree_le_of_homogeneous_mem (isHomogeneous_monomial (1 : k) rfl)
      (by simp) ((monomial_mem_iff B a).mpr ⟨a, ha, le_rfl⟩)
  let C := B.filter (fun a => a.degree = d)
  have hgen : ∀ j, P.augmentation (Pi.single j 1) ∈ monomialIdeal k C := by
    intro j
    apply (mem_monomialIdeal_iff C _).mpr
    intro a ha
    have hmem : P.augmentation (Pi.single j 1) ∈ monomialIdeal k B := by
      simpa only [P.augmentation_range] using
        LinearMap.mem_range_self P.augmentation (Pi.single j 1)
    obtain ⟨b, hb, hba⟩ := (mem_monomialIdeal_iff B _).mp hmem a ha
    have had : a.degree = d := by
      simpa only [← Finsupp.degree_apply] using
        ((P.augmentation_homogeneous j).degree_eq_sum_deg_support ha).symm
    have hbd : b.degree = d := le_antisymm ((degree_mono hba).trans_eq had) (hlo b hb)
    exact ⟨b, Finset.mem_filter.mpr ⟨hb, hbd⟩, hba⟩
  have hsub : monomialIdeal k B ≤ monomialIdeal k C := by
    rw [← P.augmentation_range]
    rintro y ⟨x, rfl⟩
    have hx : x = ∑ j, x j • Pi.single j (1 : MvPolynomial V k) := by
      funext j
      simp [Pi.single_apply]
    rw [hx, map_sum]
    exact (monomialIdeal k C).sum_mem (fun j _ => by
      rw [map_smul]
      exact (monomialIdeal k C).smul_mem _ (hgen j))
  intro a ha
  have ham : monomial a (1 : k) ∈ monomialIdeal k C :=
    hsub ((monomial_mem_iff B a).mpr ⟨a, ha, le_rfl⟩)
  obtain ⟨b, hb, hba⟩ := (monomial_mem_iff C a).mp ham
  obtain ⟨hbB, hbd⟩ := Finset.mem_filter.mp hb
  exact (hB b hbB a ha hba) ▸ hbd

end LinearResolution
end Characterizations
