module

public import ToricPower.FiniteModuleEvaluationComparison
public import ToricPower.JointShapeHomologyDetection

/-! # Rank-one reconstruction through exact affine detectors

The actual augmentation is extended to arbitrary modules, then to the
finite total of every unbounded complex. Colimit preservation is only
required after the exact detectors, which is the natural geometric
statement for affine direct images.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace ToricPower

/-- Naturality transports the actual comparison along an isomorphism
of inputs without changing the comparison map. -/
theorem reconstructionNatTrans_quasiIso_of_iso
    {C B : Type*} [Category* C] [Category* B] [Abelian B]
    {J : Type*} {shape : ComplexShape J}
    {F G : C ⥤ HomologicalComplex B shape} (τ : F ⟶ G)
    {M N : C} (e : M ≅ N) [QuasiIso (τ.app N)] : QuasiIso (τ.app M) := by
  haveI : QuasiIso (τ.app M ≫ G.map e.hom) := by
    rw [← τ.naturality e.hom]
    infer_instance
  exact quasiIso_of_comp_right (τ.app M) (G.map e.hom)

end ToricPower

namespace ToricPower.FunctorTotal

universe v t

variable (R k : Type) [CommRing R] [CommRing k]
  {B : Type v} [Category.{0} B] [Abelian B] [HasFiniteBiproducts B]
  (Φ : ModuleCat.{0} R ⥤ CochainComplex B ℕ) [Φ.Additive]
  (H : ModuleCat.{0} R ⥤ B) [H.Additive]
  (n : ℕ) (τ : Φ ⟶ singleCoefficient H n)
  {I : Type t} (detectors : I → B ⥤ ModuleCat.{0} k)
  [∀ i, (detectors i).Additive]
  [∀ i, PreservesFiniteLimits (detectors i)]
  [∀ i, PreservesFiniteColimits (detectors i)]
  (detect : ∀ M : B, (∀ i, IsZero ((detectors i).obj M)) → IsZero M)
  (exactΦ : ∀ S : ShortComplex (ModuleCat.{0} R), S.ShortExact → (S.map Φ).ShortExact)
  (exactH : ∀ S : ShortComplex (ModuleCat.{0} R), S.ShortExact → (S.map H).ShortExact)
  (preservesΦ : ∀ (i : I) (J : Type),
    PreservesColimit (Discrete.functor (fun _ : J => ModuleCat.of R R))
      (Φ ⋙ (detectors i).mapHomologicalComplex (.up ℕ)))
  (preservesH : ∀ (i : I) (J : Type),
    PreservesColimit (Discrete.functor (fun _ : J => ModuleCat.of R R)) (H ⋙ detectors i))
  (above : ∀ (M : ModuleCat.{0} R) (q : ℕ), n < q → IsZero ((Φ.obj M).X q))
  (rankOne : QuasiIso (τ.app (ModuleCat.of R R)))

include exactΦ exactH preservesΦ preservesH above rankOne in
/-- The genuine augmentation is a quasi-isomorphism after every
specified detector, on every module including unrestricted free sums. -/
theorem reconstructionModule_mapped_quasiIso (M : ModuleCat.{0} R) (i : I) :
    QuasiIso (((detectors i).mapHomologicalComplex (.up ℕ)).map (τ.app M)) := by
  let F := detectors i
  let FC := F.mapHomologicalComplex (.up ℕ)
  let τ' : Φ ⋙ FC ⟶ singleCoefficient (H ⋙ F) n :=
    Functor.whiskerRight τ FC ≫
      Functor.whiskerLeft H (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom
  haveI first : QuasiIso (τ'.app (ModuleCat.of R R)) := by
    letI := rankOne
    change QuasiIso (FC.map (τ.app (ModuleCat.of R R)) ≫ _)
    infer_instance
  haveI result : QuasiIso (τ'.app M) :=
    moduleTopAugmentation_quasiIso R k (Φ ⋙ FC) (H ⋙ F) n τ'
      (fun S h => (exactΦ S h).map_of_exact FC)
      (fun S h => (exactH S h).map_of_exact F)
      (preservesΦ i) (preservesH i)
      (fun N q high => F.map_isZero (above N q high)) first M
  haveI actualResult : QuasiIso (FC.map (τ.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app (H.obj M)) :=
    result
  exact quasiIso_of_comp_right (FC.map (τ.app M))
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) n).hom.app (H.obj M))

include detect exactΦ exactH preservesΦ preservesH above rankOne in
/-- The same specified augmentation is a quasi-isomorphism in the
original coefficient category, as detected by the affine tests. -/
theorem reconstructionModule_quasiIso (M : ModuleCat.{0} R) : QuasiIso (τ.app M) := by
  apply quasiIso_of_jointly_detect_zero_shape detectors detect
  intro i
  exact reconstructionModule_mapped_quasiIso R k Φ H n τ detectors
    exactΦ exactH preservesΦ preservesH above rankOne M i

include detect exactΦ exactH preservesΦ preservesH above rankOne in
/-- Its original natural kernel gives the literal finite-total
comparison on every unbounded coefficient complex. -/
theorem reconstructionModule_topComparison_quasiIso
    (width : ℕ) (retained : n < width) (K : CochainComplex (ModuleCat.{0} R) ℤ) :
    QuasiIso ((topComparison Φ H n width retained τ).app K) := by
  have epi (a : ℤ) : Epi (τ.app (K.X a)) := by
    letI := reconstructionModule_quasiIso R k Φ H n τ detectors detect
      exactΦ exactH preservesΦ preservesH above rankOne (K.X a)
    exact quasiIso_to_single_epi (.up ℕ) (H.obj (K.X a)) n (τ.app (K.X a))
  haveI : QuasiIso (coefficientMap τ width K) :=
    coefficientMap_quasiIso_of_epi_detectors τ width K detectors detect epi
      (fun i a => reconstructionModule_mapped_quasiIso R k Φ H n τ detectors
        exactΦ exactH preservesΦ preservesH above rankOne (K.X a) i)
      (fun a => above (K.X a) width retained)
  change QuasiIso (coefficientMap τ width K ≫ (singleTotalIso H n K retained).hom)
  infer_instance

end ToricPower.FunctorTotal

end
