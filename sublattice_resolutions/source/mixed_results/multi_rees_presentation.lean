module
public import shared_results.part003
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.MultiReesPresentation -/
section

/-! # The coefficientwise multi-Rees algebra is the generated algebra

The coefficient presentation is exactly the ordinary subalgebra generated
by the elements `f * t_c`, for `f ∈ I_c`, over the original coefficient
ring. The proof includes the zero exponent vector and uses actual ideal
products, without choosing generators for the ideals.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

namespace FourPapers.MixedTransfer
open Classical CommAlg FourPapers.Sublattice MvPolynomial

variable {C R : Type*} [Fintype C] [DecidableEq C] [CommRing R]

/-- The universal containment property of the multi-Rees coefficients. -/
theorem monomial_powerProduct_mem_subalgebra (I : C → Ideal R)
    (A : Subalgebra R (MvPolynomial C R))
    (hI : ∀ c f, f ∈ I c → monomial (Finsupp.single c 1) f ∈ A)
    (a : C →₀ ℕ) (f : R) (hf : f ∈ powerProduct I a) :
    monomial a f ∈ A := by
  generalize hn : a.degree = n
  induction n generalizing a f with
  | zero =>
      have ha : a = 0 := (Finsupp.degree_eq_zero_iff a).mp hn
      subst a
      change MvPolynomial.C f ∈ A
      exact A.algebraMap_mem f
  | succ n ih =>
      have hne : a ≠ 0 := by
        intro he
        simp [he] at hn
      obtain ⟨c, hc⟩ := Finsupp.support_nonempty_iff.mpr hne
      have hcpos : 0 < a c :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hc)
      have hs : Finsupp.single c 1 ≤ a := by
        intro j
        by_cases hj : c = j
        · subst j
          simpa only [Finsupp.single_eq_same] using Nat.succ_le_iff.mpr hcpos
        · simp only [Finsupp.single_apply, if_neg hj, zero_le]
      let b := a - Finsupp.single c 1
      have he : b + Finsupp.single c 1 = a := tsub_add_cancel_of_le hs
      have hb : b.degree = n := by
        have hh : b.degree + 1 = n + 1 := by
          simpa only [map_add, Finsupp.degree_single, hn] using
            congrArg (fun t : C →₀ ℕ => t.degree) he
        exact Nat.add_right_cancel hh
      have hprod : powerProduct I a = powerProduct I b * I c := by
        rw [← he, powerProduct_add, powerProduct_single, pow_one]
      rw [hprod] at hf
      refine Submodule.mul_induction_on hf
        (fun x hx y hy => ?_) (fun x y hx hy => ?_)
      · have hmul := A.mul_mem (ih b x hx hb) (hI c y hy)
        rwa [monomial_mul, he] at hmul
      · rw [map_add]
        exact A.add_mem hx hy

/-- The usual generated-algebra notation `R[I₁t₁, …, Iᵣtᵣ]` agrees
with the literal mixed-product coefficient condition used throughout the
formalization. In particular, the constant component is exactly `R`. -/
theorem multiReesAlgebra_eq_adjoin (I : C → Ideal R) :
    multiReesAlgebra I = Algebra.adjoin R
      {p : MvPolynomial C R | ∃ c, ∃ f ∈ I c,
        p = monomial (Finsupp.single c 1) f} := by
  let A := Algebra.adjoin R
    {p : MvPolynomial C R | ∃ c, ∃ f ∈ I c,
      p = monomial (Finsupp.single c 1) f}
  change multiReesAlgebra I = A
  apply le_antisymm
  · intro p hp
    rw [p.as_sum]
    apply A.sum_mem
    intro a ha
    exact monomial_powerProduct_mem_subalgebra I A
      (fun c f hf => Algebra.subset_adjoin ⟨c, f, hf, rfl⟩)
      a (p.coeff a) (hp a)
  · apply Algebra.adjoin_le
    rintro _ ⟨c, f, hf, rfl⟩
    change monomial (Finsupp.single c 1) f ∈ multiReesAlgebra I
    rw [monomial_mem_multiReesAlgebra, powerProduct_single, pow_one]
    exact hf

end FourPapers.MixedTransfer

end
end
end

end
