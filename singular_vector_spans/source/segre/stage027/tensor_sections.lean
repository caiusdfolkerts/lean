module
public import SegreVerified.Stage025.ChartCoordinates
import all Lean.Util.CollectAxioms

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreCriticalBundleGeometry

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.TensorSections"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.FiniteTensor

open CategoryTheory MonoidalCategory

universe v w
variable {C : Type v} [Category.{w} C] [MonoidalCategory C] [BraidedCategory C]

/-- Interchange in the full finite tensor, including its terminal unit. -/
def tensorPointwiseIso : {k : ℕ} → (M N : Fin k → C) →
    (tensorObj M ⊗ tensorObj N ≅ tensorObj (fun i => M i ⊗ N i))
  | 0, _, _ => λ_ (𝟙_ C)
  | k + 1, M, N =>
      { hom := tensorμ (M 0) (tensorObj (fun i : Fin k => M i.succ))
          (N 0) (tensorObj (fun i : Fin k => N i.succ))
        inv := tensorδ (M 0) (tensorObj (fun i : Fin k => M i.succ))
          (N 0) (tensorObj (fun i : Fin k => N i.succ))
        hom_inv_id := tensorμ_tensorδ _ _ _ _
        inv_hom_id := tensorδ_tensorμ _ _ _ _ } ≪≫
      (Iso.refl (M 0 ⊗ N 0) ⊗ᵢ
        tensorPointwiseIso (fun i : Fin k => M i.succ) (fun i => N i.succ))

/-- The finite tensor of structure units is canonically the structure unit. -/
def tensorUnitsIso : (k : ℕ) → (tensorObj (fun _ : Fin k => 𝟙_ C) ≅ 𝟙_ C)
  | 0 => Iso.refl _
  | k + 1 => (Iso.refl _ ⊗ᵢ tensorUnitsIso k) ≪≫ λ_ (𝟙_ C)

end PaperVerification.Segre.FiniteTensor


section SegreFiniteTensorSections

/-!
# Canonical sections of the full finite tensor

All formulas retain the monoidal unit at the end of the finite tensor.
They compute the actual interchange and factorwise maps on the actual
sheaf tensor sections, as required for product line trivializations.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.FiniteTensorSections

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)
open SheafCoefficientContraction SheafCoefficientComplex FixedProductProjections
open scoped TensorProduct

universe u
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
set_option quotPrecheck false in local notation "Sh" => SheafOfModules.{u} (ringCatSheaf R)

/-- The actual left unitor on all tensor sections. -/
theorem tensorSection_leftUnitor (M : Sh) (U : Cᵒᵖ)
    (a : R.obj.obj U) (m : M.val.obj U) :
    (λ_ M).hom.val.app U (tensorSection R (𝟙_ Sh) M U a m) = a • m := by
  have h := Functor.LaxMonoidal.left_unitality
    (SheafOfModules.forget (ringCatSheaf R)) M
  erw [TauCeti.SheafOfModules.forget_ε, id_whiskerRight, Category.id_comp] at h
  calc
    (λ_ M).hom.val.app U (tensorSection R (𝟙_ Sh) M U a m) =
        (λ_ M.val).hom.app U (a ⊗ₜ[R.obj.obj U] m) :=
      (congrArg (β := M.val.obj U)
        (fun g : (𝟙_ (PresheafOfModules.{u} (ringCatSheaf R).obj)) ⊗ M.val ⟶ M.val =>
          g.app U (a ⊗ₜ[R.obj.obj U] m)) h).symm
    _ = a • m := by
      let MU : ModuleCat.{u} (R.obj.obj U) :=
        PresheafOfModulesOfCommRing.obj (R := R.obj) M.val U
      have hcomponent := congrArg (β := M.val.obj U)
        (fun g : (𝟙_ (ModuleCat.{u} (R.obj.obj U))) ⊗ MU ⟶ MU =>
          g (a ⊗ₜ[R.obj.obj U] m))
        (PresheafOfModulesOfCommRing.leftUnitor_hom_app (R := R.obj) M.val U)
      exact hcomponent.trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply a m)

/-- The actual right unitor on all tensor sections. -/
theorem tensorSection_rightUnitor (M : Sh) (U : Cᵒᵖ)
    (m : M.val.obj U) (a : R.obj.obj U) :
    (ρ_ M).hom.val.app U (tensorSection R M (𝟙_ Sh) U m a) = a • m := by
  have h := Functor.LaxMonoidal.right_unitality
    (SheafOfModules.forget (ringCatSheaf R)) M
  erw [TauCeti.SheafOfModules.forget_ε, whiskerLeft_id, Category.id_comp] at h
  calc
    (ρ_ M).hom.val.app U (tensorSection R M (𝟙_ Sh) U m a) =
        (ρ_ M.val).hom.app U (m ⊗ₜ[R.obj.obj U] a) :=
      (congrArg (β := M.val.obj U)
        (fun g : M.val ⊗ (𝟙_ (PresheafOfModules.{u} (ringCatSheaf R).obj)) ⟶ M.val =>
          g.app U (m ⊗ₜ[R.obj.obj U] a)) h).symm
    _ = a • m := by
      let MU : ModuleCat.{u} (R.obj.obj U) :=
        PresheafOfModulesOfCommRing.obj (R := R.obj) M.val U
      have hcomponent := congrArg (β := M.val.obj U)
        (fun g : MU ⊗ (𝟙_ (ModuleCat.{u} (R.obj.obj U))) ⟶ MU =>
          g (m ⊗ₜ[R.obj.obj U] a))
        (PresheafOfModulesOfCommRing.rightUnitor_hom_app (R := R.obj) M.val U)
      exact hcomponent.trans
        (ModuleCat.MonoidalCategory.rightUnitor_hom_apply (R := R.obj.obj U) (M := MU) m a)

/-- The inverse left unitor inserts the actual unit section. -/
theorem leftUnitor_inv_section (M : Sh) (U : Cᵒᵖ) (m : M.val.obj U) :
    (λ_ M).inv.val.app U m=tensorSection R (𝟙_ Sh) M U (1 : R.obj.obj U) m := by
  have h := tensorSection_leftUnitor R M U (1 : R.obj.obj U) m
  rw [one_smul] at h
  calc
    (λ_ M).inv.val.app U m =
        (λ_ M).inv.val.app U ((λ_ M).hom.val.app U
          (tensorSection R (𝟙_ Sh) M U (1 : R.obj.obj U) m)) :=
      congrArg (fun z : M.val.obj U => (λ_ M).inv.val.app U z) h.symm
    _ = tensorSection R (𝟙_ Sh) M U (1 : R.obj.obj U) m := by
      have hi := congrArg
        (fun g : (𝟙_ Sh) ⊗ M ⟶ (𝟙_ Sh) ⊗ M =>
          g.val.app U (tensorSection R (𝟙_ Sh) M U (1 : R.obj.obj U) m))
        (λ_ M).hom_inv_id
      simpa only [SheafOfModules.comp_val, SheafOfModules.id_val,
        PresheafOfModules.comp_app, PresheafOfModules.id_app,
        ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using hi


/-- The inverse associator on actual section tensors. -/
theorem tensorSection_assoc_inv (M N P : Sh) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) (p : P.val.obj U) :
    (α_ M N P).inv.val.app U
      (tensorSection R M (N ⊗ P) U m (tensorSection R N P U n p)) =
      tensorSection R (M ⊗ N) P U (tensorSection R M N U m n) p := by
  rw [← tensorSection_assoc]
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => g.val.app U) (α_ M N P).hom_inv_id) _

/-- Middle-factor interchange has the expected formula on every four
actual local sections. -/
theorem tensorSection_tensorμ (M N P Q : Sh) (U : Cᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U)
    (p : P.val.obj U) (q : Q.val.obj U) :
    (tensorμ M N P Q).val.app U
      (tensorSection R (M ⊗ N) (P ⊗ Q) U
        (tensorSection R M N U m n) (tensorSection R P Q U p q)) =
      tensorSection R (M ⊗ P) (N ⊗ Q) U
        (tensorSection R M P U m p) (tensorSection R N Q U n q) := by
  simp only [tensorμ, ← id_tensorHom, ← tensorHom_id,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    tensorSection_assoc, tensorSection_assoc_inv, tensorSection_map,
    SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply, tensorSection_braiding]

/-- The actual pure section of a full finite sheaf tensor. -/
def finiteTensorSection : {k : ℕ} → (M : Fin k → Sh) → (U : Cᵒᵖ) →
    (∀ i, (M i).val.obj U) → (FiniteTensor.tensorObj M).val.obj U
  | 0, _, U, _ => (1 : R.obj.obj U)
  | k + 1, M, U, m =>
      tensorSection R (M 0) (FiniteTensor.tensorObj (fun i : Fin k => M i.succ)) U
        (m 0) (finiteTensorSection (fun i : Fin k => M i.succ) U (fun i => m i.succ))

/-- The actual finite section morphism evaluates to the actual finite tensor
of the local sections, including its terminal unit. -/
theorem sectionMap_one {k : ℕ} (M : Fin k → Sh)
    (s : ∀ i,𝟙_ Sh ⟶ M i) (U : Cᵒᵖ) :
    (FiniteTensor.sectionMap M s).val.app U (1 : R.obj.obj U)=
      finiteTensorSection R M U (fun i => (s i).val.app U (1 : R.obj.obj U)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [FiniteTensor.sectionMap, SheafOfModules.comp_val,
        PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
        leftUnitor_inv_section, finiteTensorSection]
      erw [tensorSection_map R, ih]

/-- The full finite factorwise comparison acts on every actual pure section. -/
theorem tensorFamilyIso_section {k : ℕ} {M N : Fin k → Sh}
    (e : ∀ i, M i ≅ N i) (U : Cᵒᵖ) (m : ∀ i, (M i).val.obj U) :
    (tensorFamilyIso e).hom.val.app U (finiteTensorSection R M U m) =
      finiteTensorSection R N U (fun i => (e i).hom.val.app U (m i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [tensorFamilyIso, tensorIso_hom, finiteTensorSection]
      erw [tensorSection_map R, ih]

/-- The full finite interchange comparison pairs precisely corresponding
factors; it does not reorder the actual projective factors. -/
theorem tensorPointwiseIso_section {k : ℕ} (M N : Fin k → Sh) (U : Cᵒᵖ)
    (m : ∀ i, (M i).val.obj U) (n : ∀ i, (N i).val.obj U) :
    (FiniteTensor.tensorPointwiseIso M N).hom.val.app U
      (tensorSection R (FiniteTensor.tensorObj M) (FiniteTensor.tensorObj N) U
        (finiteTensorSection R M U m) (finiteTensorSection R N U n)) =
      finiteTensorSection R (fun i => M i ⊗ N i) U
        (fun i => tensorSection R (M i) (N i) U (m i) (n i)) := by
  induction k with
  | zero =>
      simpa only [FiniteTensor.tensorPointwiseIso, FiniteTensor.tensorObj,
        finiteTensorSection, one_smul] using
        tensorSection_leftUnitor R (𝟙_ Sh) U (1 : R.obj.obj U) (1 : R.obj.obj U)
  | succ k ih =>
      simp only [FiniteTensor.tensorPointwiseIso, Iso.trans_hom,
        SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ConcreteCategory.comp_apply, FiniteTensor.tensorObj,
        finiteTensorSection, tensorIso_hom, Iso.refl_hom]
      erw [tensorSection_tensorμ R, tensorSection_map R]
      simp only [SheafOfModules.id_val, PresheafOfModules.id_app,
        ConcreteCategory.id_apply]
      erw [ih]


/-- The actual tensor of unit sections is the unit section after the
canonical finite-unit comparison. -/
theorem tensorUnitsIso_section (k : ℕ) (U : Cᵒᵖ) :
    (FiniteTensor.tensorUnitsIso (C := Sh) k).hom.val.app U
      (finiteTensorSection R (fun _ : Fin k => 𝟙_ Sh) U
        (fun _ => (1 : R.obj.obj U))) = (1 : R.obj.obj U) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [FiniteTensor.tensorUnitsIso, Iso.trans_hom, tensorIso_hom,
        SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ConcreteCategory.comp_apply, finiteTensorSection, Iso.refl_hom]
      erw [tensorSection_map R]
      simp only [SheafOfModules.id_val, PresheafOfModules.id_app,
        ConcreteCategory.id_apply]
      erw [ih]
      simpa only [one_smul] using
        tensorSection_leftUnitor R (𝟙_ Sh) U (1 : R.obj.obj U) (1 : R.obj.obj U)


end PaperVerification.Segre.FiniteTensorSections

end SegreFiniteTensorSections


section SegrePullbackTensorSections

/-!
# Actual tensor sections under pullback

The canonical oplax tensor comparison of pullback sends each pulled tensor
section to the tensor of the two pulled sections. This follows from its
definition as the adjoint of the actual pushforward tensor map. Restriction
gives the same identity on every contained source open.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.PullbackTensorSections

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open SheafCoefficientContraction SheafCoefficientComplex
open scoped TensorProduct

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A module-sheaf morphism commutes with restriction in the ordinary
abelian-group presentation of its sections. -/
theorem app_restrict {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (i : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app U m) := by
  have h := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) m
  simpa only [mapPresheaf_app, ConcreteCategory.comp_apply] using h

set_option backward.isDefEq.respectTransparency false in
/-- Actual tensor sections commute with the restriction map of the
tensor sheaf. -/
theorem tensorSection_restrict (M N : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (m : Γ(M, U)) (n : Γ(N, U)) :
    (M ⊗ N).presheaf.map i.op (tensorSection X.sheaf M N (op U) m n) =
      tensorSection X.sheaf M N (op V)
        (M.presheaf.map i.op m) (N.presheaf.map i.op n) := by
  have h := PresheafOfModules.naturality_apply
    (Functor.LaxMonoidal.μ (SheafOfModules.forget X.ringCatSheaf) M N)
    i.op (m ⊗ₜ[Γ(X, U)] n)
  erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul] at h
  exact h.symm

/-- The defining adjunction identity of the actual pullback tensor map. -/
@[reassoc] theorem pullbackTensor_adjunction (M N : Y.Modules) :
    (pullbackPushforwardAdjunction f).unit.app (M ⊗ N) ≫
      (pushforward f).map (Functor.OplaxMonoidal.δ (pullback f) M N) =
    ((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
      (pullbackPushforwardAdjunction f).unit.app N) ≫
      Functor.LaxMonoidal.μ (pushforward f) _ _ := by
  rw [pullback_δ]
  exact ((pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of a genuine tensor section, under the actual tensor
comparison, is the tensor of the pulled sections. -/
theorem pullbackTensor_section (M N : Y.Modules) (U : Y.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) :
    (Functor.OplaxMonoidal.δ (pullback f) M N).app (f ⁻¹ᵁ U)
      (f.pullbackSections (M ⊗ N) U (tensorSection Y.sheaf M N (op U) m n)) =
      tensorSection X.sheaf ((pullback f).obj M) ((pullback f).obj N)
        (op (f ⁻¹ᵁ U)) (f.pullbackSections M U m) (f.pullbackSections N U n) := by
  have h := congrArg
    (β := Γ((pullback f).obj M ⊗ (pullback f).obj N, f ⁻¹ᵁ U))
    (fun g : M ⊗ N ⟶ (pushforward f).obj
        ((pullback f).obj M ⊗ (pullback f).obj N) =>
      g.app U (tensorSection Y.sheaf M N (op U) m n))
    (pullbackTensor_adjunction f M N)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app] at h
  simp only [Scheme.Hom.pullbackSections_apply]
  erw [h]
  erw [tensorSection_map Y.sheaf]
  exact TauCeti.SheafOfModules.pushforward_μ_app_tmul f.toRingCatSheafHom
    ((pullback f).obj M) ((pullback f).obj N) (op U)
    (((pullbackPushforwardAdjunction f).unit.app M).app U m)
    (((pullbackPushforwardAdjunction f).unit.app N).app U n)


set_option backward.isDefEq.respectTransparency false in
/-- The pullback tensor-section identity on any smaller source open. -/
theorem pullbackTensor_sectionLE (M N : Y.Modules)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (m : Γ(M, U)) (n : Γ(N, U)) :
    (Functor.OplaxMonoidal.δ (pullback f) M N).app V
      (f.pullbackSectionsLE (M ⊗ N) U V h
        (tensorSection Y.sheaf M N (op U) m n)) =
      tensorSection X.sheaf ((pullback f).obj M) ((pullback f).obj N) (op V)
        (f.pullbackSectionsLE M U V h m) (f.pullbackSectionsLE N U V h n) := by
  have hn := app_restrict
    (Functor.OplaxMonoidal.δ (pullback f) M N) (homOfLE h)
    (f.pullbackSections (M ⊗ N) U (tensorSection Y.sheaf M N (op U) m n))
  simpa only [Scheme.Hom.pullbackSectionsLE_apply] using
    hn.trans ((congrArg
      (((pullback f).obj M ⊗ (pullback f).obj N).presheaf.map (homOfLE h).op)
      (pullbackTensor_section f M N U m n)).trans
        (tensorSection_restrict ((pullback f).obj M) ((pullback f).obj N)
          (homOfLE h) (f.pullbackSections M U m) (f.pullbackSections N U n)))

/-- The inverse tensor comparison retains the same concrete formula for
quasicoherent factors. -/
theorem pullbackTensor_inv_sectionLE (M N : Y.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (m : Γ(M, U)) (n : Γ(N, U)) :
    (asIso (Functor.OplaxMonoidal.δ (pullback f) M N)).inv.app V
      (tensorSection X.sheaf ((pullback f).obj M) ((pullback f).obj N) (op V)
        (f.pullbackSectionsLE M U V h m) (f.pullbackSectionsLE N U V h n)) =
      f.pullbackSectionsLE (M ⊗ N) U V h
        (tensorSection Y.sheaf M N (op U) m n) := by
  rw [← pullbackTensor_sectionLE f M N U V h m n]
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => g.app V)
      (asIso (Functor.OplaxMonoidal.δ (pullback f) M N)).hom_inv_id) _

set_option backward.isDefEq.respectTransparency false in
/-- The pullback unit comparison sends the actual pulled regular function
to its actual image under the structure-ring map. -/
theorem pullbackUnit_section (U : Y.Opens) (a : Γ(Y, U)) :
    (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
      (f.pullbackSections (𝟙_ Y.Modules) U a) = (f.app U) a := by
  have h := pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom f
  rw [Adjunction.homEquiv_unit] at h
  have hv := congrArg (β := Γ(𝟙_ X.Modules, f ⁻¹ᵁ U))
    (fun g : (𝟙_ Y.Modules) ⟶ (pushforward f).obj (𝟙_ X.Modules) =>
      g.app U a) h
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    pushforward_map_app] at hv
  have hu : Scheme.Modules.Hom.app (X := Y)
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) U a = (f.app U) a :=
    SheafOfModules.unitToPushforwardObjUnit_val_app_apply f.toRingCatSheafHom a
  calc
    (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
        (f.pullbackSections (𝟙_ Y.Modules) U a) =
      (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules)).app U a) :=
      congrArg
        (fun s : Γ((pullback f).obj (𝟙_ Y.Modules), f ⁻¹ᵁ U) =>
          (pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U) s)
        (Scheme.Hom.pullbackSections_apply f (𝟙_ Y.Modules) U a)
    _ = (f.app U) a := hv.trans hu

set_option backward.isDefEq.respectTransparency false in
/-- The same unit formula holds after restriction to every contained open. -/
theorem pullbackUnit_sectionLE (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)) :
    (pullbackObjUnitIso f).hom.app V
      (f.pullbackSectionsLE (𝟙_ Y.Modules) U V h a) = (f.appLE U V h) a := by
  calc
    (pullbackObjUnitIso f).hom.app V
        (f.pullbackSectionsLE (𝟙_ Y.Modules) U V h a) =
      (pullbackObjUnitIso f).hom.app V
        (((pullback f).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE h).op
          (f.pullbackSections (𝟙_ Y.Modules) U a)) :=
      congrArg
        (fun s : Γ((pullback f).obj (𝟙_ Y.Modules), V) =>
          (pullbackObjUnitIso f).hom.app V s)
        (Scheme.Hom.pullbackSectionsLE_apply f (𝟙_ Y.Modules) U V h a)
    _ = (𝟙_ X.Modules).presheaf.map (homOfLE h).op
        ((pullbackObjUnitIso f).hom.app (f ⁻¹ᵁ U)
          (f.pullbackSections (𝟙_ Y.Modules) U a)) :=
      app_restrict (pullbackObjUnitIso f).hom (homOfLE h)
        (f.pullbackSections (𝟙_ Y.Modules) U a)
    _ = (𝟙_ X.Modules).presheaf.map (homOfLE h).op ((f.app U) a) :=
      congrArg ((𝟙_ X.Modules).presheaf.map (homOfLE h).op)
        (pullbackUnit_section f U a)
    _ = (f.appLE U V h) a := rfl

end PaperVerification.Segre.PullbackTensorSections

end SegrePullbackTensorSections


end SegreCriticalBundleGeometry

end
end
end ProbeLayer391


/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
