import PaperVerification.AlternatingFormsHilbertSeries

/-!
# A reader-facing form of Theorem 1.1

The polynomial in this theorem is nonzero and has an explicitly proved
nonempty nonvanishing locus in the full coefficient space of pairs of
two-forms. The same locus controls every degree. The last clause states
literal vanishing of every element in degrees above the cutoff, in addition
to the complete formal-power-series identity.
-/

namespace PaperVerification.MainStatements

noncomputable section

open MvPolynomial PaperVerification.AlternatingForms

variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- The complete Hilbert series and actual high-degree vanishing hold
on one nonempty principal open of the full space of pairs of quadrics.
Taking `M = V*` gives exactly the exterior algebra in the paper. -/
theorem genericHilbertSeriesAndVanishing (n : ℕ) (hdim : Module.finrank K M = n) :
    ∃ (ι : Type) (fin : Fintype ι),
      letI := fin
      ∃ b₂ : Module.Basis ι K (⋀[K]^2 M),
        ∃ Q : MvPolynomial (ι ⊕ ι) K, Q ≠ 0 ∧
          (∃ y : (ι ⊕ ι) → K, eval y Q ≠ 0) ∧
          ∀ y : (ι ⊕ ι) → K, eval y Q ≠ 0 →
            exteriorPairHilbertSeries
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 =
              paperExteriorHilbertSeries n ∧
            ∀ s : ℕ, (n + 1) / 2 < s →
              ∀ x : ExteriorQuotientDegree
                (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s,
                x = 0 := by
  obtain ⟨ι, fin, h⟩ := paper_theorem_1_1 (K := K) (M := M) n hdim
  letI := fin
  obtain ⟨b₂, Q, hQ, hnonempty, h⟩ := h
  refine ⟨ι, fin, b₂, Q, hQ, hnonempty, ?_⟩
  intro y hy
  obtain ⟨hzero, hlow, hhigh⟩ := h y hy
  refine ⟨(exteriorPairHilbertSeries_eq_iff _ _ n).mpr
    ⟨hzero, fun s hs hd => (hlow s hs hd).1, hhigh⟩, ?_⟩
  intro s hs x
  letI : Subsingleton (ExteriorQuotientDegree
      (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 s) :=
    (Module.finrank_zero_iff (R := K)).mp (hhigh s hs)
  exact Subsingleton.elim x 0

end
end PaperVerification.MainStatements
