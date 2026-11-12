module

public import ToricPower.BoundedNatModuleComparison
public import ToricPower.QuasiIsoToSingleEpi
public import ToricPower.FiniteFunctorTotalKernelComparison
public import ToricPower.FiniteTotalEvaluationCriterion

/-!
# From the original rank-one augmentation to the full unbounded total

An exact, coproduct-preserving bounded coefficient complex can be
compared with a single exact coefficient functor by its actual
augmentation. A rank-one quasi-isomorphism determines that augmentation
on every module. Its genuine kernel then gives the comparison on the
finite signed total of every unbounded input complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower.FunctorTotal

variable (R k : Type) [CommRing R] [CommRing k]
  (Φ : ModuleCat.{0} R ⥤ CochainComplex (ModuleCat.{0} k) ℕ) [Φ.Additive]
  (H : ModuleCat.{0} R ⥤ ModuleCat.{0} k) [H.Additive]
  (n : ℕ) (τ : Φ ⟶ singleCoefficient H n)
  (exactΦ : ∀ S : ShortComplex (ModuleCat.{0} R),
    S.ShortExact → (S.map Φ).ShortExact)
  (exactH : ∀ S : ShortComplex (ModuleCat.{0} R),
    S.ShortExact → (S.map H).ShortExact)
  (preservesΦ : ∀ I : Type,
    PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) Φ)
  (preservesH : ∀ I : Type,
    PreservesColimit (Discrete.functor (fun _ : I => ModuleCat.of R R)) H)
  (above : ∀ (M : ModuleCat.{0} R) (q : ℕ), n < q → IsZero ((Φ.obj M).X q))
  (rankOne : QuasiIso (τ.app (ModuleCat.of R R)))

include exactΦ exactH preservesΦ preservesH above rankOne in
/-- Every actual coefficient module satisfies the original augmentation. -/
theorem moduleTopAugmentation_quasiIso (M : ModuleCat.{0} R) :
    QuasiIso (τ.app M) := by
  apply naturalComparison_nat_quasiIso_of_bounded_exact_rankOne R k τ
    exactΦ (fun S h => (exactH S h).map_of_exact
      (HomologicalComplex.single (ModuleCat.{0} k) (.up ℕ) n))
    preservesΦ _ n above _ rankOne M
  · intro I
    letI := preservesH I
    infer_instance
  · intro N q high
    exact isZero_single_obj_X (.up ℕ) n (H.obj N) q (ne_of_gt high)

include exactΦ exactH preservesΦ preservesH above rankOne in
/-- Epimorphy follows from the proved quasi-isomorphism of the original
map, not from a replacement augmentation. -/
theorem moduleTopAugmentation_epi (M : ModuleCat.{0} R) : Epi (τ.app M) := by
  letI := moduleTopAugmentation_quasiIso R k Φ H n τ
    exactΦ exactH preservesΦ preservesH above rankOne M
  exact quasiIso_to_single_epi (.up ℕ) (H.obj M) n (τ.app M)

include exactΦ exactH preservesΦ preservesH above rankOne in
/-- Finite horizontal width, with no bound on the input complex,
gives the quasi-isomorphism of the literal totalized comparison. -/
theorem moduleTopCoefficientMap_quasiIso (width : ℕ) (retained : n < width)
    (K : CochainComplex (ModuleCat.{0} R) ℤ) :
    QuasiIso (coefficientMap τ width K) := by
  exact mapped_coefficientMap_quasiIso_of_epi τ width K (𝟭 (ModuleCat.{0} k))
    (fun a => moduleTopAugmentation_epi R k Φ H n τ
      exactΦ exactH preservesΦ preservesH above rankOne (K.X a))
    (fun a => moduleTopAugmentation_quasiIso R k Φ H n τ
      exactΦ exactH preservesΦ preservesH above rankOne (K.X a))
    (fun a => above (K.X a) width retained)

include exactΦ exactH preservesΦ preservesH above rankOne in
/-- The actual augmentation followed by the canonical single-row
identification computes `H(K)[-n]` for every unbounded `K`. -/
theorem moduleTopComparison_quasiIso (width : ℕ) (retained : n < width)
    (K : CochainComplex (ModuleCat.{0} R) ℤ) :
    QuasiIso ((topComparison Φ H n width retained τ).app K) := by
  letI := moduleTopCoefficientMap_quasiIso R k Φ H n τ
    exactΦ exactH preservesΦ preservesH above rankOne width retained K
  change QuasiIso (coefficientMap τ width K ≫ (singleTotalIso H n K retained).hom)
  infer_instance

end ToricPower.FunctorTotal
end
