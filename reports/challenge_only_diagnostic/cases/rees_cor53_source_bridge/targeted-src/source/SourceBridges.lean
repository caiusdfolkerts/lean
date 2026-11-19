module
public import Cor53Core
public import Cor53Data

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Classical MvPolynomial CategoryTheory
open scoped BigOperators
attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace PalomarSublatticeCor53
universe u
variable {d : ℕ} (n : Fin d → ℕ) {k : Type u} [Field k]

/-- The actual ideal and chosen initial ideal are the retained literal ones. -/
private theorem ideal_eq_source (E : Finset (FiniteTuple n)) :
    sublatticeIdeal n (k := k) E = FourPapers.Sublattice.finiteSublatticeIdeal n E := rfl
private theorem powerFamily_ideal (E : Finset (FiniteTuple n)) (s : ℕ) :
    CommAlg.Polymatroid.monomialIdeal k
      (FourPapers.Sublattice.exponentPowerFamily (FourPapers.Sublattice.finiteRowFamily n E) s) =
        (sublatticeIdeal n (k := k) E)^s := by
  rw [ideal_eq_source]
  exact FourPapers.Sublattice.finitePowerFamily_ideal n E s

/-- Literal homogeneous Koszul homology agrees with the original genuine
integer derived-Tor component via its existing proved comparison. -/
private theorem idealBetti_bridge (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k)) (E : Finset (FiniteTuple n))
    (hE : finiteLatticeClosed n E) (hinit : initialIdeal o J = sublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ)))) (s p : ℕ) (q : ℤ) :
    Koszul.betti (J^s) p q = FourPapers.Sublattice.sublatticeIntegerPowerBettiNumber
      n o J E hE hinit hJ s p q := by
  change PalomarSublatticeCor53Core.Koszul.betti (J^s) p q = _
  exact PalomarSublatticeCor53Core.Koszul.betti_eq_derivedTor
    (FourPapers.Sublattice.sublatticePowerQuotientData n o J E hE hinit s)
    (FourPapers.Sublattice.homogeneousIdealPower n J hJ s) p q

private theorem monomialBetti_bridge (o : MonomialOrder (FiniteVariable.{u} n))
    (E : Finset (FiniteTuple n)) (s p : ℕ) (q : ℤ) :
    Koszul.betti ((sublatticeIdeal n (k := k) E)^s) p q =
      FourPapers.Sublattice.integerMonomialTorBettiNumber (K := k) o
        (FourPapers.Sublattice.exponentPowerFamily (FourPapers.Sublattice.finiteRowFamily n E) s)
        p q := by
  rw [← powerFamily_ideal n E s]
  change PalomarSublatticeCor53Core.Koszul.betti _ p q = _
  exact PalomarSublatticeCor53Core.Koszul.betti_eq_derivedTor
    (FourPapers.Sublattice.canonicalQuotientGroebnerData o
      (CommAlg.Polymatroid.monomialIdeal k
        (FourPapers.Sublattice.exponentPowerFamily (FourPapers.Sublattice.finiteRowFamily n E) s)))
    (FourPapers.Sublattice.monomialIdeal_isOrdinaryHomogeneous
      (FourPapers.Sublattice.exponentPowerFamily (FourPapers.Sublattice.finiteRowFamily n E) s)) p q

/-- No extra first-power comparison or signed-degree hypothesis is assumed. -/
theorem firstPower_bridge (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k)) (E : Finset (FiniteTuple n))
    (hE : finiteLatticeClosed n E) (hinit : initialIdeal o J = sublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ p q : ℕ, Koszul.betti J p (q : ℤ) =
      Koszul.betti (sublatticeIdeal n (k := k) E) p (q : ℤ)) :
    ∀ p q, FourPapers.Sublattice.sublatticePowerBettiNumber n o J E hE hinit hJ 1 p q =
      FourPapers.Sublattice.sublatticeMonomialPowerBettiNumber (K := k) n E 1 p q := by
  intro p q
  have h1 : Koszul.betti (J^1) p (q : ℤ) =
      Koszul.betti ((sublatticeIdeal n (k := k) E)^1) p (q : ℤ) := by
    simpa only [pow_one] using hβ p q
  rw [idealBetti_bridge n o J E hE hinit hJ 1 p (q : ℤ),
    monomialBetti_bridge n o E 1 p (q : ℤ)] at h1
  simpa only [FourPapers.Sublattice.sublatticeIntegerPowerBettiNumber_nat,
    FourPapers.Sublattice.integerMonomialTorBettiNumber_nat,
    FourPapers.Sublattice.sublatticeMonomialPowerBettiNumber] using h1

/-- The monomial first-occurrence conclusion in the exact independent model. -/
theorem corollary53_first_occurrence {E : Finset (FiniteTuple n)}
    (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (h : Koszul.betti ((sublatticeIdeal n (k := k) E)^m) p ((m*d : ℕ)+q) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ p ∧
      Koszul.betti ((sublatticeIdeal n (k := k) E)^r) p ((r*d : ℕ)+q) ≠ 0 := by
  let o : MonomialOrder (FiniteVariable.{u} n) :=
    @MonomialOrder.degLex (FiniteVariable.{u} n) (finiteVariableLinearOrder n)
      (@Finite.to_wellFoundedGT (FiniteVariable.{u} n) (inferInstance)
        (finiteVariableLinearOrder n).toPreorder)
  rw [monomialBetti_bridge n o E m p] at h
  obtain ⟨r,hr,hrp,hn⟩ :=
    FourPapers.Sublattice.corollary53_integer_first_occurrence o hE m hm p hp q h
  refine ⟨r,hr,hrp,?_⟩
  rwa [monomialBetti_bridge n o E r p]

/-- Actual first-power ordinary Betti equality transfers the first occurrence,
without changing any quantified degree or strengthening the comparison premise. -/
theorem corollary53_first_occurrence_transfer
    (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hβ : ∀ p q : ℕ, Koszul.betti J p (q : ℤ) =
      Koszul.betti (sublatticeIdeal n (k := k) E) p (q : ℤ))
    (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : 0 < p) (q : ℤ)
    (h : Koszul.betti (J^m) p ((m*d : ℕ)+q) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ p ∧ Koszul.betti (J^r) p ((r*d : ℕ)+q) ≠ 0 := by
  have hs := firstPower_bridge n o J E hE hinit hJ hβ
  rw [idealBetti_bridge n o J E hE hinit hJ m p] at h
  obtain ⟨r,hr,hrp,hn⟩ :=
    FourPapers.Sublattice.corollary53_integer_first_occurrence_transfer
      o J hE hinit hJ hs m hm p hp q h
  refine ⟨r,hr,hrp,?_⟩
  rwa [idealBetti_bridge n o J E hE hinit hJ r p]

end PalomarSublatticeCor53

namespace PalomarSublatticeCor53
open CategoryTheory
universe u
variable {V k : Type u} [Field k]

/-- Identity on the actual polynomials identifies the native ideal-power
module with its original scalar-restricted coefficient presentation. -/
private def powerCoefficientEquiv (J : Ideal (MvPolynomial V k)) (s : ℕ) :
    ↥(J^s) ≃ₗ[MvPolynomial V k] FourPapers.Sublattice.idealPowerPiece J s where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private def powerCoefficientIso (J : Ideal (MvPolynomial V k)) (s : ℕ) :
    ModuleCat.of (MvPolynomial V k) ↥(J^s) ≅
      ModuleCat.of (MvPolynomial V k) (FourPapers.Sublattice.idealPowerPiece J s) :=
  (powerCoefficientEquiv J s).toModuleIso

/-- The square concerns the supplied polynomial f itself, with identity
coefficient transports; no arbitrary injective map replaces multiplication. -/
private theorem multiplication_naturality (J : Ideal (MvPolynomial V k))
    (f : MvPolynomial V k) (hf : f ∈ J) (s : ℕ) :
    multiplication J f hf s ≫ (powerCoefficientIso J (s+1)).hom =
      (powerCoefficientIso J s).hom ≫ FourPapers.Sublattice.idealPowerMultiplication J f hf s := by
  ext x
  apply Subtype.ext
  simp only [ModuleCat.comp_apply, multiplication, ModuleCat.ofHom_apply,
    LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, LinearMap.mulLeft_apply,
    powerCoefficientIso, powerCoefficientEquiv,
    FourPapers.Sublattice.idealPowerMultiplication]
  rfl

variable {d : ℕ} (n : Fin d → ℕ)
/-- The retained non-monic theorem transfers to the exact independent
Mathlib Tor map through its genuine coefficient-module isomorphisms. -/
theorem chosen_generator_actualTor_injective
    (o : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) k))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal o J = sublatticeIdeal n E) (μ : E)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k
      (fun _ : FiniteVariable.{u} n => (1 : ℕ))))
    (hμ : ∀ a : E, μ.val ≤ a.val)
    (hβ : ∀ p q : ℕ, Koszul.betti J p (q : ℤ) =
      Koszul.betti (sublatticeIdeal n (k := k) E) p (q : ℤ))
    (f : MvPolynomial (FiniteVariable.{u} n) k) (hf : f ∈ J) (hf0 : f ≠ 0)
    (hdegree : o.degree f = finiteRowExponent n μ.val)
    (hhom : f.IsWeightedHomogeneous (fun _ : FiniteVariable.{u} n => (1 : ℕ)) d)
    (s p : ℕ) : Function.Injective (torMap J f hf s p) := by
  have hβsource := firstPower_bridge n o J E hE hinit hJ hβ
  let T : ModuleCat (MvPolynomial (FiniteVariable.{u} n) k) ⥤
      ModuleCat (MvPolynomial (FiniteVariable.{u} n) k) :=
    (Functor.flip (CategoryTheory.Tor (ModuleCat (MvPolynomial (FiniteVariable.{u} n) k)) p)).obj
      (residueModule (V := FiniteVariable.{u} n) (k := k))
  have hinj : Function.Injective
      (T.map (FourPapers.Sublattice.idealPowerMultiplication J f hf s)) := by
    change Function.Injective (FourPapers.PolynomialTorNaturality.paperTorMap p
      (FourPapers.Sublattice.idealPowerMultiplication J f hf s))
    exact (FourPapers.Sublattice.corollary53_chosenMinimumGenerator_paperTor
      n o J E hE hinit μ hJ hμ hβsource f hf hf0 hdegree hhom s p).1
  have hc : T.map (multiplication J f hf s) ≫ T.map (powerCoefficientIso J (s+1)).hom =
      T.map (powerCoefficientIso J s).hom ≫
        T.map (FourPapers.Sublattice.idealPowerMultiplication J f hf s) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg T.map (multiplication_naturality J f hf s)
  intro x y h
  change T.map (multiplication J f hf s) x = T.map (multiplication J f hf s) y at h
  apply (ModuleCat.mono_iff_injective (T.map (powerCoefficientIso J s).hom)).mp inferInstance
  apply hinj
  have hx := congrArg (fun a => ModuleCat.Hom.hom a x) hc
  have hy := congrArg (fun a => ModuleCat.Hom.hom a y) hc
  simp only [ModuleCat.comp_apply] at hx hy
  exact hx.symm.trans ((congrArg (T.map (powerCoefficientIso J (s+1)).hom) h).trans hy)

end PalomarSublatticeCor53
