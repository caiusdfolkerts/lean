module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part11
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricModuleSectionMultiplication



/-!
# The ordinary tensor multiplication of sections of arbitrary module sheaves

This map is defined before choosing any fractional Cartier presentation.
It sends a pure tensor of global sections to the corresponding section of
the actual tensor sheaf. The base scalars come from the structural morphism.
For Cartier sheaves it is identified with the rational-product construction.
Actual sheaf isomorphisms preserve its surjectivity.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct BaseSections

variable (k : Type u) [CommRing k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))]

def moduleSectionProductOver (M N : X.Modules) :
    Γ(M,⊤) →ₗ[k] Γ(N,⊤) →ₗ[k] Γ(tensorSheaf M N,⊤) := by
  letI : Module Γ(X,⊤) Γ(tensorSheaf M N,⊤) :=
    ModuleCat.isModule ((tensorSheaf M N).val.obj (op ⊤))
  let unitMap : Γ(M,⊤) ⊗[Γ(X,⊤)] Γ(N,⊤) →ₗ[Γ(X,⊤)] Γ(tensorSheaf M N,⊤) :=
    ((tensorSheafUnit M N).app (op ⊤)).hom
  let product : Γ(M,⊤) →ₗ[Γ(X,⊤)] Γ(N,⊤) →ₗ[Γ(X,⊤)] Γ(tensorSheaf M N,⊤) :=
    (TensorProduct.mk Γ(X,⊤) Γ(M,⊤) Γ(N,⊤)).compr₂
      (R := Γ(X,⊤)) (A := Γ(X,⊤)) unitMap
  exact product.restrictScalars₁₂ k k

/-- The usual base-linear multiplication into the genuine tensor sheaf. -/
def moduleSectionMultiplicationOver (M N : X.Modules) :
    Γ(M,⊤) ⊗[k] Γ(N,⊤) →ₗ[k] Γ(tensorSheaf M N,⊤) :=
  TensorProduct.lift (moduleSectionProductOver k M N)

@[simp] theorem moduleSectionMultiplicationOver_tmul (M N : X.Modules)
    (s : Γ(M,⊤)) (t : Γ(N,⊤)) :
    moduleSectionMultiplicationOver k M N (s⊗ₜ[k]t) =
      (tensorSheafUnit M N).app (op ⊤) (s⊗ₜ[Γ(X,⊤)]t) := rfl

theorem moduleSectionMultiplicationOver_sheafIso
    {M M' N N' : X.Modules} (F : M≅M') (G : N≅N') :
    (BaseSections.globalSectionsIso k (tensorSheafIso F G)).toLinearMap.comp
        (moduleSectionMultiplicationOver k M N) =
      (moduleSectionMultiplicationOver k M' N').comp
        (TensorProduct.map (BaseSections.globalSectionsIso k F).toLinearMap
          (BaseSections.globalSectionsIso k G).toLinearMap) := by
  apply TensorProduct.ext'
  intro s t
  change (tensorSheafIso F G).hom.app ⊤
      ((tensorSheafUnit M N).app (op ⊤) (s ⊗ₜ[Γ(X,⊤)] t)) =
    (tensorSheafUnit M' N').app (op ⊤)
      (F.hom.app ⊤ s ⊗ₜ[Γ(X,⊤)] G.hom.app ⊤ t)
  exact tensorSheafIso_pure_sections F G ⊤ s t

/-- This is an invariant of the actual module sheaves, independently
of frames, divisors, fans, or rational embeddings. -/
theorem moduleSectionMultiplicationOver_surjective_iff_sheafIso
    {M M' N N' : X.Modules} (F : M≅M') (G : N≅N') :
    Function.Surjective (moduleSectionMultiplicationOver k M N) ↔
      Function.Surjective (moduleSectionMultiplicationOver k M' N') := by
  let es := TensorProduct.congr (BaseSections.globalSectionsIso k F)
    (BaseSections.globalSectionsIso k G)
  let et := BaseSections.globalSectionsIso k (tensorSheafIso F G)
  have he (z) : et (moduleSectionMultiplicationOver k M N z) =
      moduleSectionMultiplicationOver k M' N' (es z) :=
    congrArg (fun h=>h z) (moduleSectionMultiplicationOver_sheafIso k F G)
  constructor
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨es z,(he z).symm.trans (by rw [hz,ht])⟩
  · intro h t
    obtain ⟨y,hy⟩ := h (et t)
    obtain ⟨z,hz⟩ := es.surjective y
    exact ⟨z,et.injective (by rw [he,hz,hy])⟩

namespace CartierData

variable [IsIntegral X] (D E : CartierData X)

/-- Multiplication in the function field is precisely the ordinary
tensor-sheaf section map, followed by the actual O(D)⊗O(E)≅O(D+E). -/
theorem sectionMultiplicationOver_eq_moduleSectionMultiplicationOver :
    (BaseSections.globalSectionsIso k (D.tensorSheafAddIso E)).toLinearMap.comp
      (moduleSectionMultiplicationOver k D.sheaf E.sheaf) =
        D.sectionMultiplicationOver k E := by
  apply TensorProduct.ext'
  intro s t
  change (D.tensorSheafAddIso E).hom.app ⊤
      ((tensorSheafUnit D.sheaf E.sheaf).app (op ⊤) (s ⊗ₜ[Γ(X,⊤)] t)) =
    D.sectionProduct E ⊤ s t
  exact D.tensorSheafAddIso_pure_sections E ⊤ s t

theorem sectionMultiplicationOver_surjective_iff_moduleSectionMultiplicationOver :
    Function.Surjective (D.sectionMultiplicationOver k E) ↔
      Function.Surjective (moduleSectionMultiplicationOver k D.sheaf E.sheaf) := by
  let et := BaseSections.globalSectionsIso k (D.tensorSheafAddIso E)
  have he (z) : et (moduleSectionMultiplicationOver k D.sheaf E.sheaf z) =
      D.sectionMultiplicationOver k E z :=
    congrArg (fun h=>h z)
      (D.sectionMultiplicationOver_eq_moduleSectionMultiplicationOver k E)
  constructor
  · intro h t
    obtain ⟨z,hz⟩ := h (et t)
    exact ⟨z,et.injective (by rw [he,hz])⟩
  · intro h y
    obtain ⟨t,ht⟩ := et.surjective y
    obtain ⟨z,hz⟩ := h t
    exact ⟨z,(he z).symm.trans (by rw [hz,ht])⟩

/-- Any actual presentation of a canonical line bundle can be removed
from the final multiplication statement. -/
theorem moduleSectionMultiplicationOver_adjoint_of_cartier
    (K : CartierData X) (ω : X.Modules) (F : K.sheaf≅ω)
    (h : Function.Surjective (D.sectionMultiplicationOver k (E.add K))) :
    Function.Surjective
      (moduleSectionMultiplicationOver k D.sheaf (tensorSheaf E.sheaf ω)) := by
  let G : (E.add K).sheaf≅tensorSheaf E.sheaf ω :=
    (E.tensorSheafAddIso K).symm ≪≫ tensorSheafIso (Iso.refl E.sheaf) F
  exact (moduleSectionMultiplicationOver_surjective_iff_sheafIso k
    (Iso.refl D.sheaf) G).mp
      ((D.sectionMultiplicationOver_surjective_iff_moduleSectionMultiplicationOver k
        (E.add K)).mp h)

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.moduleSectionMultiplicationOver_surjective_iff_sheafIso
#print axioms PaperVerification.ToricSchemes.CartierData.moduleSectionMultiplicationOver_adjoint_of_cartier
end
-- END PaperVerification.ToricModuleSectionMultiplication
end

section
-- BEGIN PaperVerification.ToricCartierTensorPowers



/-!
# Cartier powers are actual tensor powers

The power of the rational local equations is identified with the
recursively formed genuine tensor power of the sheaf. The transition
between the common cover for a tensor product and the original cover
is justified by the regular-unit transition equations.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X : Scheme.{u}}

/-- Actual iterated tensor powers, with the structure sheaf in degree zero. -/
def tensorSheafPower (F : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n+1 => tensorSheaf (tensorSheafPower F n) F

def tensorSheafPowerIso {F G : X.Modules} (e : F ≅ G) :
    ∀ n, tensorSheafPower F n ≅ tensorSheafPower G n
  | 0 => Iso.refl _
  | n+1 => tensorSheafIso (tensorSheafPowerIso e n) e

variable [IsIntegral X]

namespace RationalCartierCocycle

variable (C D : RationalCartierCocycle X)

/-- Equal actual fractional-section predicates give the identity
isomorphism on their rational values. -/
def sectionEquivOfIff (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s)
    (U : X.Opens) : Γ(C.sheaf,U) ≃ₗ[Γ(X,U)] Γ(D.sheaf,U) where
  toFun s := ⟨s.val,(h U s.val).mp s.property⟩
  invFun s := ⟨s.val,(h U s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sheafIsoOfIsSectionIff (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s) :
    C.sheaf ≅ D.sheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (C.sectionEquivOfIff D h U.unop).toModuleIso)
      (by intro U V f; ext s; rfl)

@[simp] theorem sheafIsoOfIsSectionIff_value
    (h : ∀ U s, C.IsSection U s ↔ D.IsSection U s)
    (U : X.Opens) (s : Γ(C.sheaf,U)) :
    ((C.sheafIsoOfIsSectionIff D h).hom.app U s).val = s.val := rfl

/-- A globally principal fractional sheaf is the actual rank-one
structure module. The frame coordinates supply the natural isomorphism. -/
def principalSheafIsoUnit (q : X.functionFieldˣ) :
    (principal (X := X) q).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => ((principal (X := X) q).localCoordinates PUnit.unit U.unop le_top).toModuleIso)
      (by
        intro U V f
        ext s
        exact (principal (X := X) q).localCoordinates_restrict PUnit.unit
          f.unop le_top le_top s)

theorem pow_zero_isSection_iff (U : X.Opens) (s : Γ(rationalFunctions X,U)) :
    (C.pow 0).IsSection U s ↔ (principal (X := X) 1).IsSection U s := by
  constructor
  · intro hs i x hx
    obtain ⟨j,hj⟩ := C.covers x.val
    simpa only [pow, principal, Units.val_pow_eq_pow_val, pow_zero, Units.val_one] using hs j x hj
  · intro hs i x hx
    simpa only [pow, principal, Units.val_pow_eq_pow_val, pow_zero, Units.val_one] using
      hs PUnit.unit x trivial

/-- Passing to the common product cover preserves the power sheaf. -/
theorem pow_succ_isSection_iff (n : ℕ) (U : X.Opens)
    (s : Γ(rationalFunctions X,U)) :
    (C.pow (n+1)).IsSection U s ↔ ((C.pow n).mul C).IsSection U s := by
  constructor
  · intro hs ij x hx
    have hpow := hs ij.1 x hx.1
    have htransition := C.transition ij.1 ij.2 x.val hx.1 hx.2
    have h := (regularAtSubring X x.val).mul_mem hpow htransition
    change rationalValueAt X U x s /
      ((C.generator ij.1 : X.functionField)^n*(C.generator ij.2 : X.functionField)) ∈ _
    have he : (rationalValueAt X U x s /
        (C.generator ij.1 : X.functionField)^(n+1)) *
        ((C.generator ij.1 : X.functionField)/(C.generator ij.2 : X.functionField)) =
      rationalValueAt X U x s /
        ((C.generator ij.1 : X.functionField)^n*(C.generator ij.2 : X.functionField)) := by
      rw [pow_succ]
      field_simp [Units.ne_zero]
      <;> ring
    simpa only [pow, Units.val_pow_eq_pow_val, he] using h
  · intro hs i x hx
    have h := hs (i,i) x ⟨hx,hx⟩
    simpa only [pow, mul, Units.val_mul, Units.val_pow_eq_pow_val, pow_succ] using h

def powZeroSheafIso : (C.pow 0).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (C.pow 0).sheafIsoOfIsSectionIff (principal (X := X) 1) C.pow_zero_isSection_iff ≪≫
    principalSheafIsoUnit (X := X) 1

def powSuccSheafIso (n : ℕ) :
    (C.pow (n+1)).sheaf ≅ ((C.pow n).mul C).sheaf :=
  (C.pow (n+1)).sheafIsoOfIsSectionIff ((C.pow n).mul C) (C.pow_succ_isSection_iff n)

/-- Every natural Cartier power is the full ordinary tensor power of
the actual sheaf, including degree zero. -/
def tensorSheafPowerIso : ∀ n, tensorSheafPower C.sheaf n ≅ (C.pow n).sheaf := by
  intro n
  induction n with
  | zero => exact C.powZeroSheafIso.symm
  | succ n ih =>
    exact tensorSheafIso ih (Iso.refl C.sheaf) ≪≫
      (C.pow n).tensorSheafMulIso C ≪≫ (C.powSuccSheafIso n).symm

end RationalCartierCocycle

namespace CartierData

variable (D : CartierData X)

/-- The n-fold Cartier sum represents the genuine n-fold tensor power,
even when the initial fractional presentation uses arbitrary local frames. -/
def tensorSheafNsmulIso (n : ℕ) :
    tensorSheafPower D.sheaf n ≅ (D.nsmul n).sheaf :=
  tensorSheafPowerIso D.presentationIso n ≪≫
    D.localCocycle.tensorSheafPowerIso n

end CartierData

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.tensorSheafPowerIso
#print axioms PaperVerification.ToricSchemes.CartierData.tensorSheafNsmulIso
end
-- END PaperVerification.ToricCartierTensorPowers
end

section
-- BEGIN PaperVerification.ToricModuleFrameGluing



/-!
# Morphisms of genuine rank-one sheaves from compatible local frame images

This is a sheaf-theoretic gluing lemma. The source and target are actual
module sheaves, and every compatibility assertion uses their actual
restriction maps. It is independent of rational functions or dominance.
-/

noncomputable section

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}}

abbrev moduleRes (M : X.Modules) {U V : X.Opens} (h : V≤U)
    (s : Γ(M,U)) : Γ(M,V) := M.presheaf.map (homOfLE h).op s

abbrev regularRes {U V : X.Opens} (h : V≤U) (a : Γ(X,U)) : Γ(X,V) :=
  X.presheaf.map (homOfLE h).op a

@[simp] theorem moduleRes_trans (M : X.Modules) {U V W : X.Opens}
    (hUV : V≤U) (hVW : W≤V) (s : Γ(M,U)) :
    moduleRes M hVW (moduleRes M hUV s) = moduleRes M (hVW.trans hUV) s := by
  simp only [moduleRes,← ConcreteCategory.comp_apply,← Functor.map_comp]
  rfl

@[simp] theorem moduleRes_smul (M : X.Modules) {U V : X.Opens}
    (h : V≤U) (a : Γ(X,U)) (s : Γ(M,U)) :
    moduleRes M h (a • s) = regularRes h a • moduleRes M h s :=
  M.map_smul (homOfLE h) a s

abbrev ModuleFrame (M : X.Modules) (U : X.Opens) :=
  M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)

namespace ModuleFrame

variable {M : X.Modules} {U : X.Opens} (e : ModuleFrame M U)

def coordinates (V : X.Opens) (hV : V≤U) : Γ(M,V) ≃ₗ[Γ(X,V)] Γ(X,V) :=
  ((PresheafOfModules.evaluation (X.ringCatSheaf.over U).obj
    (op (Over.mk (homOfLE hV)))).mapIso
      ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

def generator (V : X.Opens) (hV : V≤U) : Γ(M,V) :=
  (e.coordinates V hV).symm 1

@[simp] theorem coordinates_generator (V : X.Opens) (hV : V≤U) :
    e.coordinates V hV (e.generator V hV)=1 :=
  (e.coordinates V hV).apply_symm_apply 1

theorem section_eq (V : X.Opens) (hV : V≤U) (s : Γ(M,V)) :
    s = e.coordinates V hV s • e.generator V hV := by
  apply (e.coordinates V hV).injective
  simp only [map_smul,coordinates_generator,smul_eq_mul,mul_one]

theorem coordinates_res {V W : X.Opens} (hV : V≤U) (hWV : W≤V)
    (s : Γ(M,V)) :
    e.coordinates W (hWV.trans hV) (moduleRes M hWV s) =
      regularRes hWV (e.coordinates V hV s) := by
  let a : Over.mk (homOfLE (hWV.trans hV)) ⟶ Over.mk (homOfLE hV) :=
    Over.homMk (homOfLE hWV) (by subsingleton)
  exact PresheafOfModules.naturality_apply e.hom.val a.op s

@[simp] theorem generator_res {V W : X.Opens} (hV : V≤U) (hWV : W≤V) :
    moduleRes M hWV (e.generator V hV)=e.generator W (hWV.trans hV) := by
  apply (e.coordinates W (hWV.trans hV)).injective
  rw [e.coordinates_res hV hWV,coordinates_generator,coordinates_generator]
  simp only [regularRes,map_one]

theorem coordinates_change {V W : X.Opens} (d : ModuleFrame M V)
    (hWU : W≤U) (hWV : W≤V) (s : Γ(M,W)) :
    d.coordinates W hWV s = e.coordinates W hWU s *
      d.coordinates W hWV (e.generator W hWU) := by
  conv_lhs => rw [e.section_eq W hWU s]
  rw [map_smul,smul_eq_mul]

end ModuleFrame

/-- Sections of a sheaf are determined by their restrictions to any
actual open cover, also after intersecting the cover with a smaller open. -/
theorem module_sections_ext_cover (M : X.Modules) {ι : Type v}
    (U : ι→X.Opens) (hcover : ∀ x : X,∃ i,x∈U i)
    (W : X.Opens) (s t : Γ(M,W))
    (h : ∀ i,moduleRes M (show W⊓U i≤W from inf_le_left) s =
      moduleRes M inf_le_left t) : s=t := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf,M.isSheaf⟩
  apply F.eq_of_locally_eq' (fun i=>W⊓U i) W
    (fun _=>homOfLE inf_le_left) _ s t h
  intro x hx
  obtain ⟨i,hi⟩ := hcover x
  exact Opens.mem_iSup.mpr ⟨i,hx,hi⟩

theorem moduleSections_subsingleton_of_empty (M : X.Modules)
    (U : X.Opens) (hU : U=⊥) : Subsingleton Γ(M,U) := by
  refine ⟨fun s t=>?_⟩
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf,M.isSheaf⟩
  apply F.eq_of_locally_eq' (fun _ : Empty=> (⊥ : X.Opens)) U
    (fun i=>nomatch i) (by simp [hU]) s t
  intro i
  exact Empty.elim i

namespace ModuleFrameGluing

variable {M N : X.Modules} {ι : Type v}
    (U : ι→X.Opens) (hcover : ∀ x : X,∃ i,x∈U i)
    (e : ∀ i,ModuleFrame M (U i)) (s : ∀ i,Γ(N,U i))

/-- The frame images respect the actual change of coordinates on every
smaller common open. -/
def Compatible : Prop :=
  ∀ i j (V : X.Opens) (hi : V≤U i) (hj : V≤U j),
    moduleRes N hi (s i) =
      (e j).coordinates V hj ((e i).generator V hi) • moduleRes N hj (s j)

def localImage (i : ι) (V : X.Opens) (hi : V≤U i) (t : Γ(M,V)) : Γ(N,V) :=
  (e i).coordinates V hi t • moduleRes N hi (s i)

theorem localImage_res (i : ι) {V W : X.Opens} (hi : V≤U i) (hWV : W≤V)
    (t : Γ(M,V)) :
    moduleRes N hWV (localImage U e s i V hi t) =
      localImage U e s i W (hWV.trans hi) (moduleRes M hWV t) := by
  rw [localImage,moduleRes_smul,moduleRes_trans,localImage,ModuleFrame.coordinates_res]

theorem localImage_eq (hs : Compatible U e s)
    (i j : ι) (V : X.Opens) (hi : V≤U i) (hj : V≤U j) (t : Γ(M,V)) :
    localImage U e s i V hi t = localImage U e s j V hj t := by
  unfold localImage
  rw [hs i j V hi hj,smul_smul,← (e i).coordinates_change (e j) hi hj t]

include hcover in
theorem exists_gluedSection (hs : Compatible U e s) (W : X.Opens) (t : Γ(M,W)) :
    ∃ g : Γ(N,W),∀ i,moduleRes N (show W⊓U i≤W from inf_le_left) g =
      localImage U e s i (W⊓U i) inf_le_right (moduleRes M inf_le_left t) := by
  let V (i : ι) := W⊓U i
  let a (i : ι) : Γ(N,V i) :=
    localImage U e s i (V i) inf_le_right (moduleRes M inf_le_left t)
  have ha : N.presheaf.IsCompatible V a := by
    intro i j
    change moduleRes N inf_le_left (a i) = moduleRes N inf_le_right (a j)
    dsimp only [a]
    rw [localImage_res,localImage_res,moduleRes_trans,moduleRes_trans]
    exact localImage_eq U e s hs i j (V i⊓V j) _ _ _
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf,N.isSheaf⟩
  obtain ⟨g,hg,-⟩ := F.existsUnique_gluing' V W
    (fun _=>homOfLE inf_le_left) (by
      intro x hx
      obtain ⟨i,hi⟩ := hcover x
      exact Opens.mem_iSup.mpr ⟨i,hx,hi⟩) a ha
  exact ⟨g,hg⟩

def gluedSection (hs : Compatible U e s) (W : X.Opens) (t : Γ(M,W)) : Γ(N,W) :=
  (exists_gluedSection U hcover e s hs W t).choose

theorem gluedSection_res (hs : Compatible U e s) (W : X.Opens)
    (t : Γ(M,W)) (i : ι) :
    moduleRes N (show W⊓U i≤W from inf_le_left) (gluedSection U hcover e s hs W t) =
      localImage U e s i (W⊓U i) inf_le_right (moduleRes M inf_le_left t) :=
  (exists_gluedSection U hcover e s hs W t).choose_spec i

theorem gluedSection_res_local (hs : Compatible U e s) (W : X.Opens)
    (t : Γ(M,W)) (i : ι) (V : X.Opens) (hVW : V≤W) (hVi : V≤U i) :
    moduleRes N hVW (gluedSection U hcover e s hs W t) =
      localImage U e s i V hVi (moduleRes M hVW t) := by
  have hV : V≤W⊓U i := le_inf hVW hVi
  have h := congrArg (moduleRes N hV) (gluedSection_res U hcover e s hs W t i)
  simpa only [moduleRes_trans,localImage_res] using h

theorem gluedSection_add (hs : Compatible U e s) (W : X.Opens) (t v : Γ(M,W)) :
    gluedSection U hcover e s hs W (t+v) =
      gluedSection U hcover e s hs W t + gluedSection U hcover e s hs W v := by
  apply module_sections_ext_cover N U hcover W
  intro i
  simp only [gluedSection_res,map_add,localImage,map_add,add_smul]

theorem gluedSection_smul (hs : Compatible U e s) (W : X.Opens)
    (a : Γ(X,W)) (t : Γ(M,W)) :
    gluedSection U hcover e s hs W (a • t) =
      a • gluedSection U hcover e s hs W t := by
  apply module_sections_ext_cover N U hcover W
  intro i
  simp only [gluedSection_res,moduleRes_smul,localImage,map_smul,smul_eq_mul,smul_smul]

theorem gluedSection_natural (hs : Compatible U e s) {W V : X.Opens}
    (hVW : V≤W) (t : Γ(M,W)) :
    moduleRes N hVW (gluedSection U hcover e s hs W t) =
      gluedSection U hcover e s hs V (moduleRes M hVW t) := by
  apply module_sections_ext_cover N U hcover V
  intro i
  rw [moduleRes_trans,gluedSection_res_local U hcover e s hs W t i
    (V⊓U i) (inf_le_left.trans hVW) inf_le_right,
    gluedSection_res,moduleRes_trans]

/-- The actual sheaf morphism supplied by compatible images of a local
basis. It is built by the ordinary structure sheaf gluing axiom. -/
def hom (hs : Compatible U e s) : M ⟶ N where
  val.app W := ModuleCat.ofHom
    { toFun := gluedSection U hcover e s hs W.unop
      map_add' := gluedSection_add U hcover e s hs W.unop
      map_smul' := gluedSection_smul U hcover e s hs W.unop }
  val.naturality a := by
    ext t
    exact (gluedSection_natural U hcover e s hs a.unop.le t).symm

theorem hom_generator (hs : Compatible U e s) (i : ι) :
    (hom U hcover e s hs).app (U i) ((e i).generator (U i) le_rfl) = s i := by
  have h := gluedSection_res_local U hcover e s hs (U i)
    ((e i).generator (U i) le_rfl) i (U i) le_rfl le_rfl
  change gluedSection U hcover e s hs (U i) ((e i).generator (U i) le_rfl) = s i
  simpa only [moduleRes,homOfLE_refl,op_id,
    M.presheaf.map_id (op (U i)),N.presheaf.map_id (op (U i)),
    ConcreteCategory.id_apply,localImage,ModuleFrame.coordinates_generator,one_smul] using h

include hcover in
/-- An actual sheaf morphism is determined by the images of all local
frame generators on a cover. -/
theorem hom_ext (φ ψ : M ⟶ N)
    (h : ∀ i,φ.app (U i) ((e i).generator (U i) le_rfl) =
      ψ.app (U i) ((e i).generator (U i) le_rfl)) : φ=ψ := by
  apply Scheme.Modules.hom_ext
  intro W
  ext t
  apply module_sections_ext_cover N U hcover W
  intro i
  have hloc (φ : M ⟶ N) :
      moduleRes N (show W⊓U i≤W from inf_le_left) (φ.app W t) =
        (e i).coordinates (W⊓U i) inf_le_right (moduleRes M inf_le_left t) •
          moduleRes N inf_le_right (φ.app (U i) ((e i).generator (U i) le_rfl)) := by
    have hres :
        moduleRes N (show W⊓U i≤W from inf_le_left) (φ.app W t) =
          φ.app (W⊓U i) (moduleRes M inf_le_left t) :=
      (PresheafOfModules.naturality_apply φ.val
        (homOfLE (show W⊓U i≤W from inf_le_left)).op t).symm
    rw [hres]
    conv_lhs => rw [(e i).section_eq (W⊓U i) inf_le_right (moduleRes M inf_le_left t)]
    rw [Scheme.Modules.Hom.app_smul]
    congr 1
    rw [← ModuleFrame.generator_res (e i) (V := U i) (W := W⊓U i)
      le_rfl inf_le_right]
    exact PresheafOfModules.naturality_apply φ.val
      (homOfLE (show W⊓U i≤U i from inf_le_right)).op
      ((e i).generator (U i) le_rfl)
  rw [hloc φ,hloc ψ,h i]

theorem hom_unique (hs : Compatible U e s) (φ : M ⟶ N)
    (h : ∀ i,φ.app (U i) ((e i).generator (U i) le_rfl) = s i) :
    φ=hom U hcover e s hs :=
  hom_ext U hcover e φ (hom U hcover e s hs)
    (fun i=>(h i).trans (hom_generator U hcover e s hs i).symm)

end ModuleFrameGluing

end PaperVerification.ToricSchemes
end
-- END PaperVerification.ToricModuleFrameGluing
end

section
-- BEGIN PaperVerification.ToricInvertibleFractionalPresentation



/-!
# Every actual invertible sheaf has a fractional Cartier presentation

A frame near the generic point identifies sections on a nonempty open
with rational functions by restriction to the overlap. Local freeness
and injectivity of regular functions into the function field make this
map injective. The construction keeps the original module sheaf itself;
only an embedding into the genuine rational-function sheaf is chosen.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules}

/-- Restriction of a locally rank-one sheaf to any nonempty smaller
open is injective on actual sections of an integral scheme. -/
theorem invertibleModule_restriction_injective (hM : IsInvertibleModule M)
    {U V : X.Opens} [Nonempty V] (hVU : V≤U) :
    Function.Injective (moduleRes M hVU) := by
  intro s t hst
  let A := invertibleOpen hM
  have hcover : ∀ x : X,∃ i,x∈A i :=
    fun x=>⟨x,mem_invertibleOpen hM x⟩
  apply module_sections_ext_cover M A hcover U
  intro i
  let W := U⊓A i
  by_cases hW : Nonempty W
  · letI := hW
    let Z := V⊓W
    letI : Nonempty Z := ⟨⟨genericPoint X,
      genericPoint_mem_open X V,genericPoint_mem_open X W⟩⟩
    let e : ModuleFrame M (A i) := invertibleFrame hM i
    apply (e.coordinates W inf_le_right).injective
    apply X.germToFunctionField_injective W
    have hZ := congrArg (moduleRes M (show Z≤V from inf_le_left)) hst
    have hZ' : moduleRes M (show Z≤W from inf_le_right)
        (moduleRes M (show W≤U from inf_le_left) s) =
      moduleRes M (show Z≤W from inf_le_right)
        (moduleRes M (show W≤U from inf_le_left) t) := by
      simpa only [moduleRes_trans] using hZ
    have hc := congrArg (e.coordinates Z (inf_le_right.trans inf_le_right)) hZ'
    have hr : regularRes (show Z≤W from inf_le_right)
        (e.coordinates W inf_le_right (moduleRes M (show W≤U from inf_le_left) s)) =
      regularRes (show Z≤W from inf_le_right)
        (e.coordinates W inf_le_right (moduleRes M (show W≤U from inf_le_left) t)) :=
      (e.coordinates_res (V := W) inf_le_right (show Z≤W from inf_le_right)
        (moduleRes M (show W≤U from inf_le_left) s)).symm.trans
          (hc.trans (e.coordinates_res (V := W) inf_le_right (show Z≤W from inf_le_right)
            (moduleRes M (show W≤U from inf_le_left) t)))
    have hg := congrArg (X.germToFunctionField Z) hr
    exact (germToFunctionField_restrict X (homOfLE (show Z≤W from inf_le_right)) _).symm.trans
      (hg.trans (germToFunctionField_restrict X (homOfLE (show Z≤W from inf_le_right)) _))
  · have hbot : W=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hW ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty M W hbot
    exact Subsingleton.elim _ _

section GenericFrame

variable {U₀ : X.Opens} [Nonempty U₀] (e : ModuleFrame M U₀)

/-- The rational coordinate obtained by restricting to a fixed frame
near the generic point. Every nonempty overlap contains that point. -/
def genericFrameValue (V : X.Opens) [Nonempty V] (s : Γ(M,V)) :
    X.functionField :=
  letI : Nonempty (V⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X V,genericPoint_mem_open X U₀⟩⟩
  X.germToFunctionField (V⊓U₀)
    (e.coordinates (V⊓U₀) inf_le_right (moduleRes M inf_le_left s))

@[simp] theorem genericFrameValue_add (V : X.Opens) [Nonempty V]
    (s t : Γ(M,V)) :
    genericFrameValue e V (s+t)=genericFrameValue e V s+genericFrameValue e V t := by
  simp only [genericFrameValue,moduleRes,map_add]

theorem genericFrameValue_smul (V : X.Opens) [Nonempty V]
    (a : Γ(X,V)) (s : Γ(M,V)) :
    genericFrameValue e V (a • s) =
      X.germToFunctionField V a * genericFrameValue e V s := by
  dsimp only [genericFrameValue]
  rw [moduleRes_smul,map_smul,smul_eq_mul,map_mul]
  rw [regularRes,germToFunctionField_restrict]

theorem genericFrameValue_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (hVU : V≤U) (s : Γ(M,U)) :
    genericFrameValue e V (moduleRes M hVU s)=genericFrameValue e U s := by
  letI : Nonempty (U⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X U,genericPoint_mem_open X U₀⟩⟩
  letI : Nonempty (V⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X V,genericPoint_mem_open X U₀⟩⟩
  have hW : V⊓U₀≤U⊓U₀ := inf_le_inf hVU le_rfl
  have hc := e.coordinates_res (V := U⊓U₀) inf_le_right hW
    (moduleRes M inf_le_left s)
  have hc' : e.coordinates (V⊓U₀) inf_le_right
      (moduleRes M inf_le_left (moduleRes M hVU s)) =
    regularRes hW (e.coordinates (U⊓U₀) inf_le_right
      (moduleRes M inf_le_left s)) := by
    simpa only [moduleRes_trans] using hc
  dsimp only [genericFrameValue]
  rw [hc',regularRes,germToFunctionField_restrict]

theorem genericFrameValue_injective (hM : IsInvertibleModule M)
    (V : X.Opens) [Nonempty V] : Function.Injective (genericFrameValue e V) := by
  letI : Nonempty (V⊓U₀ : X.Opens) := ⟨⟨genericPoint X,
    genericPoint_mem_open X V,genericPoint_mem_open X U₀⟩⟩
  intro s t hst
  apply invertibleModule_restriction_injective hM
    (show V⊓U₀≤V from inf_le_left)
  apply (e.coordinates (V⊓U₀) inf_le_right).injective
  exact X.germToFunctionField_injective (V⊓U₀) hst

/-- The actual rational-function section; the empty open is handled by
the zero section, as required by the sheaf axioms. -/
def genericFrameSection (V : X.Opens) (s : Γ(M,V)) : Γ(rationalFunctions X,V) :=
  if hV : Nonempty V then
    letI := hV
    (rationalValue X V).symm (genericFrameValue e V s)
  else 0

@[simp] theorem genericFrameSection_value (V : X.Opens) [Nonempty V]
    (s : Γ(M,V)) :
    rationalValue X V (genericFrameSection e V s)=genericFrameValue e V s := by
  simp only [genericFrameSection,dif_pos (show Nonempty V from inferInstance),
    AddEquiv.apply_symm_apply]

theorem genericFrameSection_add (V : X.Opens) (s t : Γ(M,V)) :
    genericFrameSection e V (s+t)=genericFrameSection e V s+genericFrameSection e V t := by
  by_cases hV : Nonempty V
  · letI := hV
    apply (rationalValue X V).injective
    rw [rationalValue_add,genericFrameSection_value,genericFrameSection_value,
      genericFrameSection_value,genericFrameValue_add]
  · simp only [genericFrameSection,dif_neg hV,zero_add]

theorem genericFrameSection_smul (V : X.Opens) (a : Γ(X,V)) (s : Γ(M,V)) :
    genericFrameSection e V (a • s)=a • genericFrameSection e V s := by
  by_cases hV : Nonempty V
  · letI := hV
    apply (rationalValue X V).injective
    rw [rationalValue_smul,genericFrameSection_value,genericFrameSection_value,
      genericFrameValue_smul]
  · simp only [genericFrameSection,dif_neg hV,smul_zero]

theorem genericFrameSection_restrict {U V : X.Opens} (hVU : V≤U) (s : Γ(M,U)) :
    moduleRes (rationalFunctions X) hVU (genericFrameSection e U s)=
      genericFrameSection e V (moduleRes M hVU s) := by
  by_cases hV : Nonempty V
  · letI := hV
    letI : Nonempty U := ⟨⟨(Classical.choice hV).val,
      hVU (Classical.choice hV).property⟩⟩
    apply (rationalValue X V).injective
    rw [moduleRes,rationalValue_restrict,genericFrameSection_value,
      genericFrameSection_value,genericFrameValue_restrict]
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty (rationalFunctions X) V hbot
    exact Subsingleton.elim _ _

/-- An actual module-sheaf morphism into the actual rational sheaf. -/
def genericFrameInclusion : M ⟶ rationalFunctions X where
  val.app V := ModuleCat.ofHom (X := M.val.obj V)
    (Y := (rationalFunctions X).val.obj V)
    { toFun := genericFrameSection e V.unop
      map_add' := genericFrameSection_add e V.unop
      map_smul' := genericFrameSection_smul e V.unop }
  val.naturality i := by
    ext s
    exact (genericFrameSection_restrict e i.unop.le s).symm

theorem genericFrameInclusion_injective (hM : IsInvertibleModule M) (V : X.Opens) :
    Function.Injective ((genericFrameInclusion e).app V) := by
  by_cases hV : Nonempty V
  · letI := hV
    intro s t hst
    apply genericFrameValue_injective e hM V
    change genericFrameSection e V s = genericFrameSection e V t at hst
    exact (genericFrameSection_value e V s).symm.trans
      ((congrArg (rationalValue X V) hst).trans (genericFrameSection_value e V t))
  · have hbot : V=⊥ := by
      apply le_antisymm
      · intro x hx
        exact False.elim (hV ⟨⟨x,hx⟩⟩)
      · exact bot_le
    letI := moduleSections_subsingleton_of_empty M V hbot
    exact fun _ _ _=>Subsingleton.elim _ _

end GenericFrame

/-- A fractional Cartier presentation of the original invertible sheaf.
The underlying sheaf is unchanged; its rational embedding is constructed. -/
def invertibleFractionalPresentation (M : X.Modules) (hM : IsInvertibleModule M) :
    CartierData X := by
  let U := invertibleOpen hM (genericPoint X)
  letI : Nonempty U := ⟨⟨genericPoint X,mem_invertibleOpen hM (genericPoint X)⟩⟩
  let e : ModuleFrame M U := invertibleFrame hM (genericPoint X)
  exact
    { sheaf := M
      inclusion := genericFrameInclusion e
      inclusion_injective := genericFrameInclusion_injective e hM
      locallyFree := hM }

@[simp] theorem invertibleFractionalPresentation_sheaf
    (M : X.Modules) (hM : IsInvertibleModule M) :
    (invertibleFractionalPresentation M hM).sheaf=M := rfl

/-- Every ordinary actual invertible sheaf is represented by genuine
fractional Cartier data on an integral scheme. -/
theorem exists_cartierData_of_isInvertibleModule
    (M : X.Modules) (hM : IsInvertibleModule M) :
    ∃ D : CartierData X,Nonempty (M≅D.sheaf) :=
  ⟨invertibleFractionalPresentation M hM,⟨Iso.refl M⟩⟩

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.exists_cartierData_of_isInvertibleModule
end
-- END PaperVerification.ToricInvertibleFractionalPresentation
end

#eval "TORIC_DICTIONARY_PART_12_EOF"
