import CommAlg.KoszulComplex.Resolution
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # The polynomial Koszul resolution and the actual coefficient field -/

noncomputable section

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial

universe u
variable {V k : Type u} [CommRing k]

lemma ker_constantCoeff :
    RingHom.ker (constantCoeff : MvPolynomial V k →+* k) = idealOfVars V k := by
  classical
  ext f
  rw [RingHom.mem_ker, constantCoeff_eq]
  change f.coeff 0 = 0 ↔ f ∈ Ideal.span (Set.range (X : V → MvPolynomial V k))
  rw [← Set.image_univ, mem_ideal_span_X_image]
  constructor
  · intro hf a ha
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      exact (MvPolynomial.mem_support_iff.mp ha) hf
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (Finsupp.ext h)
    exact ⟨i, Set.mem_univ i, hi⟩
  · intro hf
    by_contra h
    obtain ⟨i, _, hi⟩ := hf 0 (MvPolynomial.mem_support_iff.mpr h)
    exact hi rfl

/-- Quotienting the polynomial ring by all variables really recovers its coefficient ring. -/
def residueRingEquiv :
    (MvPolynomial V k ⧸ idealOfVars V k) ≃+* k :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    ((constantCoeff : MvPolynomial V k →+* k).quotientKerEquivOfRightInverse
      (fun a => constantCoeff_C V a))

@[simp] lemma residueRingEquiv_mk (f : MvPolynomial V k) :
    residueRingEquiv (Ideal.Quotient.mk (idealOfVars V k) f) = constantCoeff f := by
  simp [residueRingEquiv]

lemma ofList_fin_variables (n : ℕ) :
    Ideal.ofList (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) =
      idealOfVars (Fin n) k := by
  apply congrArg Ideal.span
  ext f
  simp

/-- The residue module used in Tor; the preceding ring equivalence identifies it with `k`. -/
abbrev Residue (n : ℕ) (k : Type u) [CommRing k] :=
  MvPolynomial (Fin n) k ⧸ idealOfVars (Fin n) k

/-- An actual finite free Koszul resolution of the polynomial coefficient field. -/
def polynomialResolution [Nontrivial k] (n : ℕ) :
    ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) k) (Residue n k)) :=
  transportResolution
    (regularSequenceResolution (List.ofFn (X : Fin n → MvPolynomial (Fin n) k))
      (fin_variables_regular n))
    (Submodule.quotEquivOfEq _ _ (ofList_fin_variables (k := k) n)).toModuleIso

@[simp] lemma polynomialResolution_complex [Nontrivial k] (n : ℕ) :
    (polynomialResolution (k := k) n).complex =
      koszulComplex.ofList (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) := rfl

/-- Derived Tor against the actual polynomial residue field. -/
def polynomialTor [Nontrivial k] (n i : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) k)) :
    ModuleCat.{u} (MvPolynomial (Fin n) k) :=
  ((Tor' (ModuleCat (MvPolynomial (Fin n) k)) i).obj
    (ModuleCat.of (MvPolynomial (Fin n) k) (Residue n k))).obj M

/-- The canonical isomorphism from genuine derived Tor to the variable Koszul homology. -/
def polynomialTorIso [Nontrivial k] (n i : ℕ)
    (M : ModuleCat.{u} (MvPolynomial (Fin n) k)) :
    polynomialTor n i M ≅
      (coefficientComplex (List.ofFn (X : Fin n → MvPolynomial (Fin n) k)) M).homology i :=
  (polynomialResolution (k := k) n).isoLeftDerivedObj
    ((CategoryTheory.MonoidalCategory.tensoringRight _).obj M) i

end CommAlg.Koszul
