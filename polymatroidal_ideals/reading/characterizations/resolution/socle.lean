import Characterizations.Resolution.KoszulStaircase
import Characterizations.Resolution.KoszulSocleCycle
import Characterizations.Resolution.Degree
import Characterizations.Socles

/-! The socle-degree theorem derived from a genuine exact linear free resolution. -/
noncomputable section
set_option maxHeartbeats 400000
namespace Characterizations
open Classical Resolution MvPolynomial CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
namespace LinearResolution
variable {I : Ideal (MvPolynomial V k)} {d : ℕ} (P : LinearResolution I d)
include P

/-- Lemma2.2 in its full homogeneous form. The cycle is the actual top Koszul
boundary inside the ideal, and the staircase proves that its degree is forced. -/
theorem homogeneous_socle_degree [Nonempty V] {y : MvPolynomial V k} {e : ℕ}
    (hy : y.IsHomogeneous e) (hout : y ∉ I)
    (hmul : ∀ i : V, X i * y ∈ I) : e + 1 = d := by
  have hy0 : y ≠ 0 := fun h => hout (h ▸ I.zero_mem)
  let i₀ : V := Classical.choice inferInstance
  have hx0 : X i₀ * y ≠ 0 := by
    intro hz
    apply hy0
    apply (MvPolynomial.X_mul_cancel_left_iff (i := i₀)).mp
    simpa only [mul_zero] using hz
  have hlo : d ≤ e + 1 := P.degree_le_of_homogeneous_mem
    (by simpa only [Nat.add_comm] using (isHomogeneous_X (R := k) i₀).mul hy) hx0 (hmul i₀)
  by_contra hne
  have hlt : d < e + 1 := lt_of_le_of_ne hlo (Ne.symm hne)
  let t := e + 1 - d
  have ht : 0 < t := Nat.sub_pos_of_lt hlt
  have hdegree : d + t = e + 1 := Nat.add_sub_of_le hlo
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
  let s : Set.powersetCard V (m + 1) := ⟨Finset.univ, hm⟩
  let z := socleBoundary I s y (fun j => hmul j.val)
  have hz : ∀ a, (z a).val.IsHomogeneous (d + t) := by
    rw [hdegree]
    exact socleBoundary_homogeneous I s y (fun j => hmul j.val) hy
  have hc := socleBoundary_cycle I s y (fun j => hmul j.val)
  have hb := P.idealRows_boundary_above t ht m z hz hc
  exact socleBoundary_not_boundary I m hm y hmul hout hb

omit P in
theorem monomial_socle_degree [Nonempty V] (B : Family V)
    (P : LinearResolution (monomialIdeal k B) d) (a : Exponent V)
    (hout : ¬ Contains B a) (hmul : ∀ i : V, Contains B (a + Finsupp.single i 1)) :
    a.degree + 1 = d := by
  apply P.homogeneous_socle_degree (isHomogeneous_monomial (1 : k) rfl)
  · exact fun h => hout ((monomial_mem_iff B a).mp h)
  · intro i
    have he : (X i : MvPolynomial V k) * monomial a 1 = monomial (a + Finsupp.single i 1) 1 := by
      rw [X, monomial_mul]
      simp [add_comm]
    rw [he]
    exact (monomial_mem_iff B _).mpr (hmul i)

omit P in
/-- Every actual quotient-socle class has a homogeneous representative of degree d−1.
The zero-variable case is included for every nonzero monomial ideal. -/
theorem socleConcentrated (B : Family V) (hB : B.Nonempty)
    (P : LinearResolution (monomialIdeal k B) d) :
    SocleConcentrated (monomialIdeal k B) (d - 1) := by
  rw [socleConcentrated_iff]
  intro a ha hs
  cases isEmpty_or_nonempty V with
  | inl h =>
      letI := h
      obtain ⟨b, hb⟩ := hB
      have he : b = a := Subsingleton.elim _ _
      exact False.elim (ha ⟨b, hb, he.le⟩)
  | inr h =>
      letI := h
      have he := P.monomial_socle_degree B a ha hs
      omega

end LinearResolution
end Characterizations
