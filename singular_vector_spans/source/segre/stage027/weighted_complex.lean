module
public import SegreVerified.Stage027.ProductFrames
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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.WeightedComplex"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreAffineSheafFrames

/-!
# Canonical sheaf frames from actual affine section frames

A linear equivalence with the sections of a quasicoherent sheaf on an affine
open determines an actual sheaf isomorphism on its spectrum chart. The map is
the genuine tilde/global-sections counit. Its naturality promotes a checked
equation on the original affine sections to an equality of entire sheaf maps.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.AffineSheafFrames

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u
variable {X : Scheme.{u}} {U : X.Opens}
variable (M : X.Modules) (hU : IsAffineOpen U)
variable {V : Type u} [AddCommGroup V] [Module Γ(X,U) V]

/-- The supplied frame followed by the actual affine restriction of sections. -/
def sectionFrame (e : V ≃ₗ[Γ(X,U)] Γ(M,U)) :
    ModuleCat.of Γ(X,U) V ≅
      (moduleSpecΓFunctor (R := Γ(X,U))).obj (M.restrict hU.fromSpec) :=
  (e.trans (M.fromSpecSectionsEquiv hU)).toModuleIso

/-- The associated sheaf isomorphism uses the original quasicoherent sheaf
and the genuine affine counit, so its target is the literal restriction. -/
def sheafFrame [M.IsQuasicoherent] (e : V ≃ₗ[Γ(X,U)] Γ(M,U)) :
    tilde (ModuleCat.of Γ(X,U) V) ≅ M.restrict hU.fromSpec :=
  (tilde.functor Γ(X,U)).mapIso (sectionFrame M hU e) ≪≫
    @asIso _ _ _ _ (M.restrict hU.fromSpec).fromTildeΓ
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent
        (R := Γ(X,U)) (M.restrict hU.fromSpec))

/-- The canonical sheaf frame sends an associated global section to the
actual restriction of the original affine section. -/
theorem sheafFrame_app_toOpen [M.IsQuasicoherent]
    (e : V ≃ₗ[Γ(X,U)] Γ(M,U)) (v : V) :
    (sheafFrame M hU e).hom.app ⊤
      (tilde.toOpen (ModuleCat.of Γ(X,U) V) ⊤ v) =
      M.fromSpecSectionsEquiv hU (e v) := by
  change (M.restrict hU.fromSpec).fromTildeΓ.val.app (op ⊤)
    ((tilde.map (sectionFrame M hU e).hom).val.app (op ⊤)
      (tilde.toOpen (ModuleCat.of Γ(X,U) V) ⊤ v)) = _
  rw [TauCeti.AlgebraicGeometry.tilde_map_val_app_toOpen,
    Scheme.Modules.fromTildeΓ_val_app_toOpen_top]
  rfl

/-- The associated section of one in the scalar module is literally one
in the structure sheaf, including its actual localization definition. -/
theorem tildeSelf_toOpen_one (R : CommRingCat.{u}) :
    tilde.toOpen (ModuleCat.of R R) ⊤ (1 : R) =
      (1 : Γ(Spec R,⊤)) := by
  change StructureSheaf.const (1 : R) (1 : R) ⊤ (by simp) = 1
  exact StructureSheaf.const_one _

/-- A rank-one affine frame with the actual structure sheaf as target. -/
def unitFrame [M.IsQuasicoherent] (e : Γ(X,U) ≃ₗ[Γ(X,U)] Γ(M,U)) :
    M.restrict hU.fromSpec ≅ SheafOfModules.unit (Spec Γ(X,U)).ringCatSheaf :=
  (sheafFrame M hU e).symm ≪≫ tildeSelf

/-- The inverse unit frame sends one to the literal restricted generator. -/
theorem unitFrame_inv_top_one [M.IsQuasicoherent]
    (e : Γ(X,U) ≃ₗ[Γ(X,U)] Γ(M,U)) :
    (unitFrame M hU e).inv.app ⊤ (1 : Γ(Spec Γ(X,U),⊤)) =
      M.fromSpecSectionsEquiv hU (e 1) := by
  change (sheafFrame M hU e).hom.app ⊤
    (1 : Γ(Spec Γ(X,U),⊤)) = _
  rw [← tildeSelf_toOpen_one,sheafFrame_app_toOpen]

/-- Conversely the literal restricted generator has unit coordinate one. -/
theorem unitFrame_top_one [M.IsQuasicoherent]
    (e : Γ(X,U) ≃ₗ[Γ(X,U)] Γ(M,U)) :
    (unitFrame M hU e).hom.app ⊤ (M.fromSpecSectionsEquiv hU (e 1)) =
      (1 : Γ(Spec Γ(X,U),⊤)) := by
  rw [← unitFrame_inv_top_one]
  exact congrArg (fun f => f.app ⊤ (1 : Γ(Spec Γ(X,U),⊤)))
    (unitFrame M hU e).inv_hom_id

variable {N : X.Modules}
variable {W : Type u} [AddCommGroup W] [Module Γ(X,U) W]

/-- Naturality of the actual affine section frame, as a module morphism. -/
theorem sectionFrame_naturality
    (eM : V ≃ₗ[Γ(X,U)] Γ(M,U)) (eN : W ≃ₗ[Γ(X,U)] Γ(N,U))
    (f : M ⟶ N) (g : V →ₗ[Γ(X,U)] W)
    (h : ∀ v, f.app U (eM v)=eN (g v)) :
    (sectionFrame M hU eM).hom ≫
      (moduleSpecΓFunctor (R := Γ(X,U))).map
        ((restrictFunctor hU.fromSpec).map f) =
      ModuleCat.ofHom g ≫ (sectionFrame N hU eN).hom := by
  ext v
  change ((restrictFunctor hU.fromSpec).map f).app ⊤
      (M.fromSpecSectionsEquiv hU (eM v)) =
    N.fromSpecSectionsEquiv hU (eN (g v))
  rw [Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality,h v]

/-- Equality of the true chart-section formulas gives equality of the
entire restricted sheaf morphisms under the canonical sheaf frames. -/
theorem sheafFrame_naturality [M.IsQuasicoherent] [N.IsQuasicoherent]
    (eM : V ≃ₗ[Γ(X,U)] Γ(M,U)) (eN : W ≃ₗ[Γ(X,U)] Γ(N,U))
    (f : M ⟶ N) (g : V →ₗ[Γ(X,U)] W)
    (h : ∀ v, f.app U (eM v)=eN (g v)) :
    (sheafFrame M hU eM).hom ≫ (restrictFunctor hU.fromSpec).map f =
      tilde.map (ModuleCat.ofHom g) ≫ (sheafFrame N hU eN).hom := by
  let f' := (restrictFunctor hU.fromSpec).map f
  have hn := (tilde.adjunction (R := Γ(X,U))).counit.naturality f'
  change (tilde.functor Γ(X,U)).map
      ((moduleSpecΓFunctor (R := Γ(X,U))).map f') ≫
        (N.restrict hU.fromSpec).fromTildeΓ =
      (M.restrict hU.fromSpec).fromTildeΓ ≫ f' at hn
  simp only [sheafFrame,Iso.trans_hom,Functor.mapIso_hom,asIso_hom]
  rw [Category.assoc,← hn,← Category.assoc,← Functor.map_comp,
    sectionFrame_naturality M hU eM eN f g h,Functor.map_comp,Category.assoc] <;> rfl

/-- The conjugated morphism is exactly tilde of the specified linear map. -/
theorem sheafFrame_conjugate [M.IsQuasicoherent] [N.IsQuasicoherent]
    (eM : V ≃ₗ[Γ(X,U)] Γ(M,U)) (eN : W ≃ₗ[Γ(X,U)] Γ(N,U))
    (f : M ⟶ N) (g : V →ₗ[Γ(X,U)] W)
    (h : ∀ v, f.app U (eM v)=eN (g v)) :
    (sheafFrame M hU eM).hom ≫ (restrictFunctor hU.fromSpec).map f ≫
      (sheafFrame N hU eN).inv = tilde.map (ModuleCat.ofHom g) := by
  rw [← Category.assoc,sheafFrame_naturality M hU eM eN f g h,
    Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- Affine sections detect maps between the original quasicoherent sheaves
after restriction to the actual spectrum chart. -/
theorem restrict_map_eq_of_app [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f g : M ⟶ N) (h : ∀ s : Γ(M,U),f.app U s=g.app U s) :
    (restrictFunctor hU.fromSpec).map f = (restrictFunctor hU.fromSpec).map g := by
  let eM := LinearEquiv.refl Γ(X,U) Γ(M,U)
  let eN := LinearEquiv.refl Γ(X,U) Γ(N,U)
  let a : Γ(M,U) →ₗ[Γ(X,U)] Γ(N,U) := (f.val.app (op U)).hom
  have hf := sheafFrame_naturality M hU eM eN f a (fun _ => rfl)
  have hg := sheafFrame_naturality M hU eM eN g a (fun s => (h s).symm)
  apply (cancel_epi (sheafFrame M hU eM).hom).mp
  exact hf.trans hg.symm

end PaperVerification.Segre.AffineSheafFrames

namespace PaperVerification.Segre.AffineSheafFrames

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false in
/-- A map out of the actual structure sheaf is determined by its value
on the global unit section. This uses naturality on every open. -/
theorem unit_hom_ext_top_one {Y : Scheme.{u}} {N : Y.Modules}
    (f g : SheafOfModules.unit Y.ringCatSheaf ⟶ N)
    (h : Scheme.Modules.Hom.app (X := Y) f ⊤ (1 : Γ(Y,⊤)) =
      Scheme.Modules.Hom.app (X := Y) g ⊤ (1 : Γ(Y,⊤))) : f=g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  let r' : Γ(Y,U) := r
  change Scheme.Modules.Hom.app (X := Y) f U r' =
    Scheme.Modules.Hom.app (X := Y) g U r'
  have hn (a : SheafOfModules.unit Y.ringCatSheaf ⟶ N) :
      Scheme.Modules.Hom.app (X := Y) a U (1 : Γ(Y,U)) =
        N.presheaf.map U.leTop.op
          (Scheme.Modules.Hom.app (X := Y) a ⊤ (1 : Γ(Y,⊤))) := by
    have ha := PresheafOfModules.naturality_apply a.val U.leTop.op
      (1 : Γ(Y,⊤))
    change Scheme.Modules.Hom.app (X := Y) a U
      ((Y.presheaf.map U.leTop.op) 1) =
        N.presheaf.map U.leTop.op
          (Scheme.Modules.Hom.app (X := Y) a ⊤ (1 : Γ(Y,⊤))) at ha
    simpa only [map_one] using ha
  have he : Scheme.Modules.Hom.app (X := Y) f U (1 : Γ(Y,U)) =
      Scheme.Modules.Hom.app (X := Y) g U (1 : Γ(Y,U)) := by
    rw [hn f,hn g,h]
  calc
    Scheme.Modules.Hom.app (X := Y) f U r' =
        r' • Scheme.Modules.Hom.app (X := Y) f U (1 : Γ(Y,U)) := by
      rw [← Scheme.Modules.Hom.app_smul]; simp
    _ = r' • Scheme.Modules.Hom.app (X := Y) g U (1 : Γ(Y,U)) :=
      congrArg (r' • ·) he
    _ = Scheme.Modules.Hom.app (X := Y) g U r' := by
      rw [← Scheme.Modules.Hom.app_smul]; simp

end PaperVerification.Segre.AffineSheafFrames

end SegreAffineSheafFrames

section SegreActualProductSheafFrames

/-!
# Actual source and line sheaf frames on every product chart

The canonical polynomial-coordinate bases constructed on affine sections are
promoted to genuine isomorphisms of the restricted quasicoherent sheaves.
The comparison with a specified coordinate functional is an equality of
entire sheaf maps and therefore remains valid on all smaller opens.

-/

set_option autoImplicit false
open scoped Classical

namespace PaperVerification.Segre.ActualProductSheafFrames

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualProductChartFrames AffineSheafFrames

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

instance line_quasicoherent (t : ℤ) : (line K I t).IsQuasicoherent := by
  unfold line
  exact finiteTensor_quasicoherent _ (fun _ => inferInstance)

/-- The canonical actual source frame as an isomorphism of sheaves. -/
def sourceSheafFrame (p : ∀ i,I i) :
    tilde (ModuleCat.of Γ(X,chart K I p)
      (FrameIndex I p → Γ(X,chart K I p))) ≅
        (source K I).restrict (chart_affine K I p).fromSpec :=
  sheafFrame (source K I) (chart_affine K I p) (sourceFrame K I p)

/-- The canonical actual line frame as an isomorphism of sheaves. -/
def lineSheafFrame (p : ∀ i,I i) (t : ℤ) :
    tilde (ModuleCat.of Γ(X,chart K I p) Γ(X,chart K I p)) ≅
      (line K I t).restrict (chart_affine K I p).fromSpec :=
  sheafFrame (line K I t) (chart_affine K I p) (lineFrame K I p t).symm

/-- The same line frame with the literal structure sheaf as its target. -/
def lineUnitFrame (p : ∀ i,I i) (t : ℤ) :
    (line K I t).restrict (chart_affine K I p).fromSpec ≅
      SheafOfModules.unit (Spec Γ(X,chart K I p)).ringCatSheaf :=
  (lineSheafFrame K I p t).symm ≪≫ tildeSelf

/-- An exact computation on canonical chart sections yields the full
coordinate-functional identity on the actual restricted source and line. -/
theorem functional_under_sheaf_frames (p : ∀ i,I i) (d : ℤ)
    (φ : source K I ⟶ line K I d)
    (ψ : (FrameIndex I p → Γ(X,chart K I p)) →ₗ[Γ(X,chart K I p)]
      Γ(X,chart K I p))
    (hφ : ∀ v,lineFrame K I p d
      (φ.app (chart K I p) (sourceFrame K I p v))=ψ v) :
    (sourceSheafFrame K I p).hom ≫
      (restrictFunctor (chart_affine K I p).fromSpec).map φ ≫
        (lineSheafFrame K I p d).inv = tilde.map (ModuleCat.ofHom ψ) := by
  apply sheafFrame_conjugate (source K I) (chart_affine K I p)
    (sourceFrame K I p) (lineFrame K I p d).symm φ ψ
  intro v
  apply (lineFrame K I p d).injective
  rw [LinearEquiv.apply_symm_apply]
  exact hφ v

/-- The same full functional identity in the structure-unit convention
used by the ordinary sheaf Koszul complex. -/
theorem functional_under_unit_frames (p : ∀ i,I i) (d : ℤ)
    (φ : source K I ⟶ line K I d)
    (ψ : (FrameIndex I p → Γ(X,chart K I p)) →ₗ[Γ(X,chart K I p)]
      Γ(X,chart K I p))
    (hφ : ∀ v,lineFrame K I p d
      (φ.app (chart K I p) (sourceFrame K I p v))=ψ v) :
    (sourceSheafFrame K I p).inv ≫
      (tilde.map (ModuleCat.ofHom ψ) ≫ tildeSelf.hom) =
      (restrictFunctor (chart_affine K I p).fromSpec).map φ ≫
        (lineUnitFrame K I p d).hom := by
  rw [← functional_under_sheaf_frames K I p d φ ψ hφ]
  simp only [lineUnitFrame,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    Iso.inv_hom_id_assoc]

end PaperVerification.Segre.ActualProductSheafFrames

end SegreActualProductSheafFrames

section SegreProductWeightedComplex

/-!
# The actual product weighted Koszul complex, without commutation premises

On every genuine affine chart the coefficient line has its canonical
frame. Rank one makes the two successive coefficient actions commute,
even without a chosen multiplication trivialization. This equality
descends over the actual chart cover and proves square zero for all
actual global weighted differentials.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.WeightedKoszulLocalCommutation

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)
open WeightedSheafKoszul WeightedKoszulFrames

universe u
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
set_option quotPrecheck false in local notation "Sh" => SheafOfModules.{u} (ringCatSheaf R)

/-- A genuine line frame alone proves commutation of arbitrary successive
bilinear coefficient actions; there is no characteristic restriction. -/
theorem coefficientsCommute_of_line_frame (L : Sh) (Q : ℕ → Sh)
    (μ : ∀ n, L ⊗ Q (n + 1) ⟶ Q n) (eL : L ≅ 𝟙_ Sh) :
    CoefficientsCommute R L Q μ := by
  intro n U a b q
  exact WeightedContraction.actions_commute_of_line_frame
    (frameAt R eL U) (multiplicationAt R (μ (n + 1)) U)
    (multiplicationAt R (μ n) U) a b q

end PaperVerification.Segre.WeightedKoszulLocalCommutation

namespace PaperVerification.Segre.WeightedKoszulFrames

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)
open SheafCoefficientContraction SheafCoefficientComplex FiniteTensorSections
open WeightedSheafKoszul

universe u
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
set_option quotPrecheck false in local notation "Sh" => SheafOfModules.{u} (ringCatSheaf R)

/-- A full sheaf-map identity under the actual line frames proves the
required multiplication formula on every open and every pair of sections. -/
theorem compatible_of_map {L Q P : Sh} (μ : L ⊗ Q ⟶ P)
    (eL : L ≅ 𝟙_ Sh) (eQ : Q ≅ 𝟙_ Sh) (eP : P ≅ 𝟙_ Sh)
    (h : μ ≫ eP.hom = (eL.hom ⊗ₘ eQ.hom) ≫ (λ_ (𝟙_ Sh)).hom) :
    MultiplicationCompatible R μ eL eQ eP := by
  intro U a q
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app U) h) (tensorSection R L Q U a q)
  change eP.hom.val.app U (μ.val.app U (tensorSection R L Q U a q)) =
    (λ_ (𝟙_ Sh)).hom.val.app U
      ((eL.hom ⊗ₘ eQ.hom).val.app U (tensorSection R L Q U a q)) at hh
  erw [tensorSection_map R, tensorSection_leftUnitor R] at hh
  simpa only [smul_eq_mul, frameAt_apply, multiplicationAt_apply] using hh

end PaperVerification.Segre.WeightedKoszulFrames

namespace PaperVerification.Segre.ProductWeightedKoszul

open CategoryTheory MonoidalCategory AlgebraicGeometry
open ActualProductKoszulTerms ActualProductChartFrames ActualProductSheafFrames

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k + 1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The actual coefficient actions of the product line sequence commute
globally, proved from the canonical frames on a genuine covering. -/
theorem coefficientsCommute (d : ℤ) : CoefficientsCommute K I d := by
  apply WeightedKoszulLocalCommutation.coefficientsCommute_of_openImmersion_cover
    (line K I d) (coefficientFamily K I d) (coefficientMultiplication K I d)
    (fun p : ∀ i, I i => (chart_affine K I p).fromSpec)
  · simpa only [IsAffineOpen.opensRange_fromSpec] using chart_cover K I
  · intro p
    exact WeightedKoszulLocalCommutation.coefficientsCommute_of_line_frame
      (Spec Γ(X, chart K I p)).sheaf _ _ _ (lineUnitFrame K I p d)

/-- The full actual global weighted differential squares to zero without
any extra commutation or local-regularity hypothesis. -/
theorem differential_squared_unconditional (d : ℤ)
    (φ : source K I ⟶ line K I d) (r : ℕ) :
    differential K I d φ (r + 1) ≫ differential K I d φ r = 0 :=
  differential_squared K I d φ (coefficientsCommute K I d) r

/-- The actual complete product weighted Koszul chain complex. -/
def complex (d : ℤ) (φ : source K I ⟶ line K I d) :
    ChainComplex (X).Modules ℕ :=
  WeightedSheafKoszul.complex (X).sheaf (source K I) (line K I d)
    (coefficientFamily K I d) φ (coefficientMultiplication K I d)
    (coefficientsCommute K I d)

/-- The actual consecutive weighted maps, with their proved zero
composite, in the format used by the global cohomology argument. -/
def shortComplex (d : ℤ) (φ : source K I ⟶ line K I d) (r : ℕ) :
    ShortComplex (X).Modules :=
  WeightedSheafKoszul.shortComplex (X).sheaf (source K I) (line K I d)
    (coefficientFamily K I d) φ (coefficientMultiplication K I d)
    (coefficientsCommute K I d) r

end PaperVerification.Segre.ProductWeightedKoszul

end SegreProductWeightedComplex

section SegreProductSheafMultiplication

/-!
# The actual product coefficient maps in genuine sheaf line frames

The canonical affine section frames determine actual sheaf isomorphisms.
The generator multiplication already proved on the original product chart
then gives an equality of full sheaf maps, hence compatibility on every
smaller open for the complete weighted Koszul complex.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.AffineSheafMultiplication

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open SheafCoefficientContraction SheafCoefficientComplex FiniteTensorSections
open AffineSheafFrames
open scoped TensorProduct

universe u
variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine restriction tensor map carries the two restricted chart
sections to the restriction of their actual tensor section. -/
theorem fromSpec_tensor_section (M N : X.Modules) (m : Γ(M,U)) (n : Γ(N,U)) :
    (Functor.LaxMonoidal.μ (restrictFunctor hU.fromSpec) M N).app ⊤
      (tensorSection (Spec Γ(X,U)).sheaf (M.restrict hU.fromSpec)
        (N.restrict hU.fromSpec) (op ⊤)
        (M.fromSpecSectionsEquiv hU m) (N.fromSpecSectionsEquiv hU n)) =
      (M ⊗ N).fromSpecSectionsEquiv hU
        (tensorSection X.sheaf M N (op U) m n) := by
  have ht := TauCeti.SheafOfModules.pushforward_μ_app_tmul
    (restrictRingCatSheafHom hU.fromSpec) M N (op ⊤)
    (M.fromSpecSectionsEquiv hU m) (N.fromSpecSectionsEquiv hU n)
  erw [ht]
  simp only [fromSpecSectionsEquiv_apply,restrictAppIso,Iso.refl_inv,
    ConcreteCategory.id_apply,tensorSection]
  exact PresheafOfModulesOfCommRing.naturality_apply
    (Functor.LaxMonoidal.μ (ExternalSections.forgetModules (X := X)) M N)
    (homOfLE (show hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X,U)).Opens) ≤ U by
      rw [Scheme.Hom.image_top_eq_opensRange,hU.opensRange_fromSpec])).op
    (m ⊗ₜ[Γ(X,U)] n)

variable (M N P : X.Modules)
variable [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent]
variable (eM : Γ(X,U) ≃ₗ[Γ(X,U)] Γ(M,U))
variable (eN : Γ(X,U) ≃ₗ[Γ(X,U)] Γ(N,U))
variable (eP : Γ(X,U) ≃ₗ[Γ(X,U)] Γ(P,U))
variable (μ : M ⊗ N ⟶ P)

/-- Correct multiplication on the actual chart generators forces the
full sheaf-map identity in the canonical line frames. -/
theorem unitFrame_multiplication
    (hμ : μ.app U (tensorSection X.sheaf M N (op U) (eM 1) (eN 1))=eP 1) :
    (Functor.LaxMonoidal.μ (restrictFunctor hU.fromSpec) M N ≫
      (restrictFunctor hU.fromSpec).map μ) ≫ (unitFrame P hU eP).hom =
    ((unitFrame M hU eM).hom ⊗ₘ (unitFrame N hU eN).hom) ≫
      (λ_ (𝟙_ (Spec Γ(X,U)).Modules)).hom := by
  let h : (𝟙_ (Spec Γ(X,U)).Modules) ⟶
      M.restrict hU.fromSpec ⊗ N.restrict hU.fromSpec :=
    (λ_ (𝟙_ (Spec Γ(X,U)).Modules)).inv ≫
      ((unitFrame M hU eM).inv ⊗ₘ (unitFrame N hU eN).inv)
  letI : IsIso h := by dsimp [h]; infer_instance
  apply (cancel_epi h).mp
  have hr : h ≫ (((unitFrame M hU eM).hom ⊗ₘ (unitFrame N hU eN).hom) ≫
      (λ_ (𝟙_ (Spec Γ(X,U)).Modules)).hom) = 𝟙 _ := by
    simp only [h, Category.assoc, tensorHom_comp_tensorHom_assoc,
      Iso.inv_hom_id, id_tensorHom_id, Category.id_comp]
  rw [hr]
  apply unit_hom_ext_top_one
  simp only [h, Category.assoc, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  erw [leftUnitor_inv_section (Spec Γ(X,U)).sheaf,
    tensorSection_map (Spec Γ(X,U)).sheaf]
  change (unitFrame P hU eP).hom.app ⊤
    (((restrictFunctor hU.fromSpec).map μ).app ⊤
      ((Functor.LaxMonoidal.μ (restrictFunctor hU.fromSpec) M N).app ⊤
        (tensorSection (Spec Γ(X,U)).sheaf _ _ (op ⊤)
          ((unitFrame M hU eM).inv.app ⊤ (1 : Γ(Spec Γ(X,U),⊤)))
          ((unitFrame N hU eN).inv.app ⊤ (1 : Γ(Spec Γ(X,U),⊤)))))) =
    (1 : Γ(Spec Γ(X,U),⊤))
  rw [unitFrame_inv_top_one, unitFrame_inv_top_one, fromSpec_tensor_section,
    Scheme.Modules.Hom.fromSpecSectionsEquiv_naturality, hμ, unitFrame_top_one]

end PaperVerification.Segre.AffineSheafMultiplication

namespace PaperVerification.Segre.ProductSheafMultiplication

open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualProductChartFrames ActualProductSheafFrames
open ProductWeightedKoszul ProductLineMultiplication WeightedKoszulRestriction
open AffineSheafFrames AffineSheafMultiplication

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]
set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The actual restricted coefficient multiplication agrees as an entire
sheaf morphism with multiplication in the original structure sheaf. -/
theorem coefficientMultiplication_under_unit_frames (p : ∀ i,I i) (d : ℤ) (r : ℕ) :
    restrictMultiplication (chart_affine K I p).fromSpec
      (line K I d) (coefficientFamily K I d) (coefficientMultiplication K I d) r ≫
        (lineUnitFrame K I p (d*(1-(r : ℤ)))).hom =
      ((lineUnitFrame K I p d).hom ⊗ₘ
        (lineUnitFrame K I p (d*(1-((r+1 : ℕ) : ℤ)))).hom) ≫
        (λ_ (𝟙_ (Spec Γ(X,chart K I p)).Modules)).hom := by
  apply unitFrame_multiplication (chart_affine K I p)
    (line K I d) (coefficientFamily K I d (r+1)) (coefficientFamily K I d r)
    (lineFrame K I p d).symm (lineFrame K I p (d*(1-((r+1 : ℕ) : ℤ)))).symm
    (lineFrame K I p (d*(1-(r : ℤ)))).symm
    (coefficientMultiplication K I d r)
  apply (lineFrame K I p (d*(1-(r : ℤ)))).injective
  have h := coefficientMultiplication_frame K I p d r
    ((lineFrame K I p d).symm 1)
    ((lineFrame K I p (d*(1-((r+1 : ℕ) : ℤ)))).symm 1)
  change lineFrame K I p (d * (1 - (r : ℤ)))
    (WeightedSheafKoszul.multiplicationAt (X).sheaf (coefficientMultiplication K I d r)
      (Opposite.op (chart K I p)) ((lineFrame K I p d).symm 1)
      ((lineFrame K I p (d * (1 - ((r + 1 : ℕ) : ℤ)))).symm 1)) =
    lineFrame K I p (d * (1 - (r : ℤ)))
      ((lineFrame K I p (d * (1 - (r : ℤ)))).symm 1)
  simpa only [LinearEquiv.apply_symm_apply, mul_one] using h

/-- Compatibility on all opens of every actual affine chart follows from
the full sheaf-map identity. This discharges the final multiplication
premise of the actual scalar-Koszul comparison. -/
theorem coefficientMultiplication_compatible (p : ∀ i,I i) (d : ℤ) (r : ℕ) :
    WeightedKoszulFrames.MultiplicationCompatible.{u} (Spec Γ(X,chart K I p)).sheaf
      (restrictMultiplication (chart_affine K I p).fromSpec
        (line K I d) (coefficientFamily K I d) (coefficientMultiplication K I d) r)
      (lineUnitFrame K I p d)
      (lineUnitFrame K I p (d*(1-((r+1 : ℕ) : ℤ))))
      (lineUnitFrame K I p (d*(1-(r : ℤ)))) :=
  WeightedKoszulFrames.compatible_of_map.{u} _ _ _ _ _
    (coefficientMultiplication_under_unit_frames K I p d r)

end PaperVerification.Segre.ProductSheafMultiplication

end SegreProductSheafMultiplication

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
