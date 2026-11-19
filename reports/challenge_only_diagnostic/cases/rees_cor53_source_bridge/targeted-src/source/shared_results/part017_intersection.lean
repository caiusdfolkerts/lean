module
public import shared_results.part017_order

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.NestedMixedIntersection -/
section

/-! # Corollary 5.7: literal mixed products, powers and intersections -/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 512
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg MvPolynomial
open scoped MonomialOrder
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {K : Type u} [Field K]
  (J : ULift.{u} (Fin r) → Ideal (MvPolynomial (FiniteVariable.{u} n) K))
  (E : Fin r → Finset (FiniteTuple n))

/-- Transport the symbolic/ordinary identity through a ring isomorphism.
The proof is carried out with an abstract equivalence, so applications do
not expand a large concrete polynomial equivalence inside ideal lattices. -/
lemma radicalSymbolicPower_eq_power_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (L : Ideal A) (s : ℕ)
    (hrad : (L.map e.toRingHom).IsRadical)
    (hs : symbolicPower (L.map e.toRingHom) s = (L.map e.toRingHom)^s) :
    radicalSymbolicPower L s = L^s := by
  have hr : L.IsRadical := by
    have h := hrad.comap (f := e.toRingHom)
    rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at h
    exact h
  rw [← symbolicPower_eq_radicalSymbolicPower L hr]
  have hm : (symbolicPower L s).map e.toRingHom = (L^s).map e.toRingHom := by
    rw [symbolicPower_map_ringEquiv e, Ideal.map_pow]
    exact hs
  have hc := congrArg (Ideal.comap e.toRingHom) hm
  simpa only [Ideal.comap_map_of_bijective e.toRingHom e.bijective] using hc

/-- The symbolic-power conclusion for the actual colored ideal before
its polynomial variables are flattened into the finite-row presentation. -/
theorem colored_radicalSymbolicPower_eq_power
    (M : MonomialOrder (FiniteVariable.{u} (coloredRows (r := r) n)))
    (hE : ColoredLatticeClosed n E)
    (hinit : FourPapers.initialIdeal M (coloredDeformedIdeal J) =
      finiteSublatticeIdeal (coloredRows (r := r) n) (coloredFamily n E)) (s : ℕ) :
    radicalSymbolicPower (coloredIdeal J) s = (coloredIdeal J)^s := by
  apply radicalSymbolicPower_eq_power_of_ringEquiv
    (coloredPolynomialEquiv (k := K) n).toRingEquiv (coloredIdeal J) s
  · exact finite_radical_of_sublattice_initial (coloredRows (r := r) n)
      M (coloredDeformedIdeal J) (coloredFamily n E) hinit
  · exact finite_symbolicPower_eq_power (coloredRows (r := r) n) M
      (coloredDeformedIdeal J) (coloredFamily n E)
      ((coloredLatticeClosed_iff n E).mp hE) hinit s

/-- The intersection clause of Corollary 5.7, with the exact original
arbitrary monomial order retained and no symbolic-power premise added. -/
theorem corollary57_intersection
    (M : MonomialOrder (FiniteVariable.{u} n))
    (hE : ColoredLatticeClosed n E) (hJ : Monotone J)
    (hinit : ∀ c, FourPapers.initialIdeal M (J c) = coloredIdeals (k := K) n E c)
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    powerProduct J m = ⨅ c, (J c)^prefixExponent m c := by
  apply nested_powerProduct_eq_iInf J hJ m
  apply colored_radicalSymbolicPower_eq_power J E (coloredExtendedOrder M) hE
  rw [colored_initial_of_nested J (coloredIdeals (k := K) n E)
    (coloredExtendedOrder M) hJ (fun c => by simpa using hinit c)]
  exact coloredIdeal_map_eq_sublattice (k := K) n E

/-- The all-mixed initial clause with the same original order, rather
than an order assumed to extend it. -/
theorem corollary57_original_initial
    (M : MonomialOrder (FiniteVariable.{u} n))
    (hE : ColoredLatticeClosed n E) (hJ : Monotone J)
    (hinit : ∀ c, FourPapers.initialIdeal M (J c) = coloredIdeals (k := K) n E c)
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    FourPapers.initialIdeal M (powerProduct J m) =
      powerProduct (coloredIdeals (k := K) n E) m := by
  simpa using corollary57_initial J (coloredExtendedOrder M) E hE hJ
    (fun c => by simpa using hinit c) m

/-- The parallel intersection formula for the literal monomial products. -/
theorem corollary57_monomial_intersection
    (M : MonomialOrder (FiniteVariable.{u} n))
    (hE : ColoredLatticeClosed n E) (hJ : Monotone J)
    (hinit : ∀ c, FourPapers.initialIdeal M (J c) = coloredIdeals (k := K) n E c)
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    powerProduct (coloredIdeals (k := K) n E) m =
      ⨅ c, (coloredIdeals (k := K) n E c)^prefixExponent m c := by
  have hI : Monotone (coloredIdeals (k := K) n E) := by
    intro a b hab
    rw [← hinit a, ← hinit b]
    exact FourPapers.initialIdeal_mono M (hJ hab)
  apply corollary57_intersection (coloredIdeals (k := K) n E) E M hE hI
  intro c
  change FourPapers.initialIdeal M (finiteSublatticeIdeal n (E c.down)) =
    finiteSublatticeIdeal n (E c.down)
  rw [finiteSublatticeIdeal_eq_monomialIdeal (k := K)]
  simpa only [CommAlg.Polymatroid.monomialIdeal] using!
    (FourPapers.initialIdeal_monomialSpan (k := K) (V := FiniteVariable.{u} n) M
      (finiteRowFamily n (E c.down) :
        Set (CommAlg.Polymatroid.Exponent (FiniteVariable.{u} n))))

/-- Every ideal identity displayed in (5.3), with the cumulative exponents
and the original term order exactly as stated in the paper. -/
theorem corollary57_ideal_identities
    (M : MonomialOrder (FiniteVariable.{u} n))
    (hE : ColoredLatticeClosed n E) (hJ : Monotone J)
    (hinit : ∀ c, FourPapers.initialIdeal M (J c) = coloredIdeals (k := K) n E c)
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    powerProduct J m = (⨅ c, (J c)^prefixExponent m c) ∧
    powerProduct (coloredIdeals (k := K) n E) m =
      (⨅ c, (coloredIdeals (k := K) n E c)^prefixExponent m c) ∧
    FourPapers.initialIdeal M (powerProduct J m) =
      powerProduct (coloredIdeals (k := K) n E) m :=
  ⟨corollary57_intersection J E M hE hJ hinit m,
    corollary57_monomial_intersection J E M hE hJ hinit m,
    corollary57_original_initial J E M hE hJ hinit m⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary57_ideal_identities
#print axioms FourPapers.Sublattice.corollary57_intersection
#print axioms FourPapers.Sublattice.corollary57_original_initial

end
end
end


end
