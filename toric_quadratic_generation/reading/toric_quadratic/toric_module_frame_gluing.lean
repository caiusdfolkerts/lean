module

public import PaperVerification.ToricCartierSheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section

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
