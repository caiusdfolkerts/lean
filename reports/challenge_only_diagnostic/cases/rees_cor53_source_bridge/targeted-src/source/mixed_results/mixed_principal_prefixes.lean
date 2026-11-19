module
public import shared_results.part024

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedPrincipalPrefixes -/
section

/-! # Mixed powers of principal lattice prefixes

The example immediately following Theorem 5.5 uses a monotone sequence of
elements of the same finite sublattice. Restricting below these elements
gives the required colored sublattice, so the full mixed-power theorems
apply without a linear-resolution hypothesis.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice
open Classical
open IntegerFiltered.MultiplicativeFiltration

variable {d r : ℕ} {n : Fin d → ℕ}

/-- The color `c` consists of the lattice elements below `b c`. -/
def principalLatticePrefixes (E : Finset (FiniteTuple n))
    (b : Fin r → FiniteTuple n) : Fin r → Finset (FiniteTuple n) :=
  fun c => E.filter (fun a => a ≤ b c)

theorem principalLatticePrefixes_mono (E : Finset (FiniteTuple n))
    (b : Fin r → FiniteTuple n) (hb : Monotone b) :
    Monotone (principalLatticePrefixes E b) := by
  intro c e hce a ha
  obtain ⟨haE, hab⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨haE, hab.trans (hb hce)⟩

theorem principalLatticePrefixes_nonempty (E : Finset (FiniteTuple n))
    (b : Fin r → FiniteTuple n) (hb : ∀ c, b c ∈ E) (c : Fin r) :
    (principalLatticePrefixes E b c).Nonempty :=
  ⟨b c, Finset.mem_filter.mpr ⟨hb c, le_rfl⟩⟩

/-- Coordinatewise meet and join preserve the colored prefix family. -/
theorem principalLatticePrefixes_colored (E : Finset (FiniteTuple n))
    (hE : finiteLatticeClosed n E) (b : Fin r → FiniteTuple n)
    (hb : Monotone b) : ColoredLatticeClosed n (principalLatticePrefixes E b) := by
  constructor
  · intro c a ha e x hx
    obtain ⟨haE, hab⟩ := Finset.mem_filter.mp ha
    obtain ⟨hxE, hxb⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hE.1 a haE x hxE, ?_⟩
    by_cases hce : c ≤ e
    · rw [inf_eq_left.mpr hce]
      exact inf_le_left.trans hab
    · rw [inf_eq_right.mpr (le_of_not_ge hce)]
      exact inf_le_right.trans hxb
  · intro c a ha e x hx
    obtain ⟨haE, hab⟩ := Finset.mem_filter.mp ha
    obtain ⟨hxE, hxb⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hE.2 a haE x hxE,
      sup_le (hab.trans (hb le_sup_left)) (hxb.trans (hb le_sup_right))⟩

/-- The actual multi-Rees Koszul homology for principal prefixes is
generated in coordinate-unit colors, over every field. -/
theorem principalLatticePrefixes_generation {k : Type*} [Field k]
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (b : Fin r → FiniteTuple n) (hb : Monotone b) :
    Algebra.adjoin k (selectedHomologyClasses
      (MixedTransfer.idealReesKoszulDGA (coloredIdeals (k := k) n
        (principalLatticePrefixes E b)))
      (actualMixedUnitColorPiece (E := principalLatticePrefixes E b) (k := k))) = ⊤ :=
  theorem55_monomial_generation (principalLatticePrefixes_colored E hE b hb)

end FourPapers.Sublattice

end
end
end


end
