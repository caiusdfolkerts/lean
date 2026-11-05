import CommAlg.IntegralClosure.HomologicalRees
import CommAlg.Polymatroid.HomologicalStabilization
import CommAlg.Rees.OneColor

/-! # Full generation bounds for the genuine homological-shift modules

The conclusions are literal ideal-span equalities inside the actual ordinary
and multi-Rees algebras. They include every polynomial element of the modules,
all fixed twists, zero ideals and inactive coordinates.
-/

noncomputable section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem homologicalMultiPiece_le_powerProduct (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) (s : C →₀ ℕ) :
    homologicalMultiPiece J I hJ hI i s ≤ powerProduct I s :=
  (homologicalShiftIdeal_le _ _ i).trans Ideal.mul_le_right

/-- The complete module-generation assertion of Corollary 4.1, for the
actual ideal of genuine homological shifts in the actual multi-Rees ring. -/
theorem homologicalMultiIdeal_generated_in_box (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) :
    homologicalMultiIdeal J I hJ hI i =
      Ideal.span (reesBoxGenerators I (homologicalMultiPiece J I hJ hI i) i) := by
  apply multiReesIdeal_span_box _ _ (homologicalMultiPiece_action J I hJ hI i)
    (homologicalMultiPiece_le_powerProduct J I hJ hI i)
  intro s c hs
  exact homologicalShift_severalColors I J hI hJ s i c hs

theorem homologicalShiftIdeal_top_pos
    (hS : IsPolymatroidalIdeal (⊤ : Ideal (MvPolynomial V k))) (i : ℕ) (hi : 0 < i) :
    homologicalShiftIdeal ⊤ hS i = ⊥ := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ hS zeroRank (rankIdeal_zeroRank k).symm i]
  exact rankShiftIdeal_zeroRank_pos i hi

theorem homologicalMultiPiece_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (s : Unit →₀ ℕ) :
    homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i s =
      homologicalShiftIdeal (I ^ (s ())) (hI.pow _) i := by
  apply homologicalShiftIdeal_congr
  simp [powerProduct]

theorem homologicalPowerPiece_eq_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) (s : Unit →₀ ℕ) :
    homologicalPowerPiece I hI i (s ()) =
      homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i s := by
  rw [homologicalMultiPiece_oneColor]
  by_cases hs : s () = 0
  · simp only [homologicalPowerPiece, hs, ite_true, pow_zero, Ideal.one_eq_top]
    exact (homologicalShiftIdeal_top_pos _ i hi).symm
  · simp [homologicalPowerPiece, hs]

theorem mem_homologicalPowerIdeal_iff_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) (p : reesAlgebra I) :
    p ∈ homologicalPowerIdeal I hI i ↔
      reesMultiEquiv I p ∈ homologicalMultiIdeal ⊤ (fun _ : Unit => I)
        isPolymatroidalIdeal_top (fun _ => hI) i := by
  rw [mem_homologicalPowerIdeal, mem_homologicalMultiIdeal]
  simp only [reesMultiEquiv_apply, reesToMulti_coeff,
    ← homologicalPowerPiece_eq_oneColor I hI i hi]
  constructor
  · intro h s
    exact h (s ())
  · intro h n
    simpa using h (Finsupp.single () n)

theorem homologicalPowerIdeal_eq_map_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.map (reesMultiEquiv I).symm.toRingHom
      (homologicalMultiIdeal ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) := by
  calc
    _ = Ideal.comap (reesMultiEquiv I).toRingHom
        (homologicalMultiIdeal ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) := by
      ext p
      exact mem_homologicalPowerIdeal_iff_oneColor I hI i hi p
    _ = _ := (Ideal.map_comap_of_equiv (reesMultiEquiv I).symm.toRingEquiv).symm

/-- Homogeneous elements of the actual positive-power shift module in Rees
degrees at most `i`. Its degree-zero component is zero by definition. -/
def homologicalPowerBoxGenerators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s r, s ≤ i ∧ r ∈ homologicalPowerPiece I hI i s ∧
    p.val = Polynomial.monomial s r}

theorem oneColor_box_image (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    (reesMultiEquiv I).symm '' reesBoxGenerators (fun _ : Unit => I)
      (homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) i =
        homologicalPowerBoxGenerators I hI i := by
  ext p
  constructor
  · rintro ⟨q, ⟨s, r, hs, hr, he⟩, rfl⟩
    refine ⟨s (), r, hs (), ?_, ?_⟩
    · rwa [homologicalPowerPiece_eq_oneColor I hI i hi s]
    · rw [reesMultiEquiv_symm_val, he, MvPolynomial.uniqueAlgEquiv_monomial]
  · rintro ⟨n, r, hn, hr, he⟩
    refine ⟨reesMultiEquiv I p, ?_, (reesMultiEquiv I).symm_apply_apply p⟩
    refine ⟨Finsupp.single () n, r, ?_, ?_, ?_⟩
    · intro c
      cases c
      simpa using hn
    · rw [← homologicalPowerPiece_eq_oneColor I hI i hi (Finsupp.single () n)]
      simpa using hr
    · change (MvPolynomial.uniqueAlgEquiv (MvPolynomial V k) Unit).symm p.val = _
      rw [he]
      simpa using (MvPolynomial.uniqueAlgEquiv_symm_monomial
        (R := MvPolynomial V k) (d := Finsupp.single () n) (r := r))

/-- The full module-generation conclusion of Theorem 1.1, as a literal span
inside Mathlib's ordinary Rees algebra. It holds for all polymatroidal ideals,
including zero and unit ideals, over every field. -/
theorem homologicalPowerIdeal_generated_le (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.span (homologicalPowerBoxGenerators I hI i) := by
  rw [homologicalPowerIdeal_eq_map_oneColor I hI i hi,
    homologicalMultiIdeal_generated_in_box, Ideal.map_span]
  exact congrArg Ideal.span (oneColor_box_image I hI i hi)

end CommAlg
