module
public import graph_foundation.part013
public import shared_results.part018_closed_graph_parameter_powers

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedIntegerTor -/
section

/-! # Corollary 7.2 in every integer fine degree

The target is the literal finite direct sum over all chains with the
prescribed colors. Negative residual degrees are included as proved zero
submodules of genuine derived Tor. The empty mixed product is included.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d r : ℕ} {n : Fin d → ℕ} {E : Fin r → Finset (FiniteTuple n)}
variable {k : Type u} [CommRing k]

/-- Every colored multichain with exactly the prescribed color count.
No residual-degree restriction is built into this index type. -/
abbrev MixedColorChain (m : ULift.{u} (Fin r) →₀ ℕ) :=
  {w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m.degree //
    chainColorCount E w=m}

instance mixedColorChainFintype (m : ULift.{u} (Fin r) →₀ ℕ) :
    Fintype (MixedColorChain (E := E) m) := by unfold MixedColorChain; infer_instance

def mixedNaturalIndexEquiv (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    MixedAdmissibleChain (E := E) m a ≃
      {w : MixedColorChain (E := E) m // chainBaseShift E w.val≤a} where
  toFun w := ⟨⟨w.val,w.property.1⟩,w.property.2⟩
  invFun w := ⟨w.val.val,w.val.property,w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The index change is the literal value-preserving map between the
nested subtype presentations; no large Tor definition is normalized. -/
def mixedNaturalPiEquiv (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n))
    (Q : MixedColorChain (E := E) m → Type u)
    [∀ w,AddCommGroup (Q w)] [∀ w,Module k (Q w)] :
    (∀w : MixedAdmissibleChain (E := E) m a,Q ⟨w.val,w.property.1⟩) ≃ₗ[k]
      (∀w : {w : MixedColorChain (E := E) m // chainBaseShift E w.val≤a},Q w.val) where
  toFun f w := f ⟨w.val.val,w.val.property,w.property⟩
  invFun f w := f ⟨⟨w.val,w.property.1⟩,w.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Regrading the actual derived-Tor submodule, with the basis-degree
interpretation justified in IntegralIntegerKoszulStrands. -/
abbrev mixedProductIntegerGradedTor (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : FiniteVariable.{u} n→₀ℤ) (p : ℕ) :=
  paperIntegerGradedTor (k := k) (mixedRowPowerFamily n E m) a p

def mixedIntegerFullIndexNatIso (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ModuleCat.of k (mixedProductIntegerGradedTor (E := E) (k := k) m (integerExponent a) p) ≅
      ModuleCat.of k (∀w : MixedColorChain (E := E) m,
        quotientPaperIntegerGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
          (integerExponent a-integerExponent (chainBaseShift E w.val)) p) := by
  let Q : MixedColorChain (E := E) m → Type u := fun w =>
    quotientPaperIntegerGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
      (integerExponent a-integerExponent (chainBaseShift E w.val)) p
  let e₁ := LinearEquiv.ofEq _ _
    (paperIntegerGradedTor_nat (k := k) (mixedRowPowerFamily n E m) a p)
  let e₂ : (∀w : MixedAdmissibleChain (E := E) m a,
      quotientPaperGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
        (a-chainBaseShift E w.val) p) ≃ₗ[k]
      (∀w : MixedAdmissibleChain (E := E) m a,Q ⟨w.val,w.property.1⟩) :=
    LinearEquiv.piCongrRight (fun w : MixedAdmissibleChain (E := E) m a =>
    (LinearEquiv.ofEq _ _ (quotientPaperIntegerGradedTor_shift (k := k)
      (sameColorChainCoefficientFamily E w.val) a (chainBaseShift E w.val) w.property.2 p)).symm)
  let e₃ : (∀w : MixedAdmissibleChain (E := E) m a,Q ⟨w.val,w.property.1⟩) ≃ₗ[k]
      (∀w : {w : MixedColorChain (E := E) m // chainBaseShift E w.val≤a},Q w.val) :=
    mixedNaturalPiEquiv (k := k) m a Q
  let e₄ := piZeroExtension (k := k) (M := Q)
    (fun w : MixedColorChain (E := E) m => chainBaseShift E w.val≤a) (by
      intro w hw
      dsimp [Q]
      rw [quotientPaperIntegerGradedTor_shift_zero _ _ _ hw]
      infer_instance)
  exact e₁.toModuleIso ≪≫ corollary72_natural hE m a p ≪≫ e₂.toModuleIso ≪≫
    e₃.toModuleIso ≪≫ e₄.toModuleIso

/-- **Corollary 7.2, full statement.** Every commutative coefficient ring,
every mixed exponent including zero, every homological degree, and every
integer fine degree. The RHS is an actual finite direct sum of actual
quotient Tor submodules, retaining integral torsion. -/
def corollary72 (hE : ColoredLatticeClosed n E)
    (m : ULift.{u} (Fin r) →₀ ℕ) (a : FiniteVariable.{u} n→₀ℤ) (p : ℕ) :
    ModuleCat.of k (mixedProductIntegerGradedTor (E := E) (k := k) m a p) ≅
      ModuleCat.of k (Π₀w : MixedColorChain (E := E) m,
        quotientPaperIntegerGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
          (a-integerExponent (chainBaseShift E w.val)) p) := by
  by_cases ha : ∀v,0≤a v
  · let hex := (integerExponent_exists_iff a).mpr ha
    let b := Classical.choose hex
    have hb : integerExponent b=a := Classical.choose_spec hex
    rw [←hb]
    exact mixedIntegerFullIndexNatIso hE m b p ≪≫
      (DFinsupp.linearEquivFunOnFintype (R := k)
        (M := fun w : MixedColorChain (E := E) m =>
          quotientPaperIntegerGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
            (integerExponent b-integerExponent (chainBaseShift E w.val)) p)).symm.toModuleIso
  · have hex : ∃v,a v<0 := by simpa only [not_forall,not_le] using ha
    let v := Classical.choose hex
    have hv : a v<0 := Classical.choose_spec hex
    letI : Subsingleton (mixedProductIntegerGradedTor (E := E) (k := k) m a p) := by
      change Subsingleton (paperIntegerGradedTor (k := k) (mixedRowPowerFamily n E m) a p)
      rw [paperIntegerGradedTor_negative _ _ _ hv]
      infer_instance
    letI (w : MixedColorChain (E := E) m) : Subsingleton
        (quotientPaperIntegerGradedTor (k := k) (sameColorChainCoefficientFamily E w.val)
          (a-integerExponent (chainBaseShift E w.val)) p) := by
      have hn : (a-integerExponent (chainBaseShift E w.val)) v<0 :=
        (sub_le_self _ (integerExponent_nonneg _ _)).trans_lt hv
      rw [quotientPaperIntegerGradedTor_negative _ _ _ hn]
      infer_instance
    exact (LinearEquiv.ofSubsingleton (R := k) _ _).toModuleIso

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.corollary72

end
end
end


end
