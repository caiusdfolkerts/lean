module

public import ToricPower.CechMeetInjectiveAssembly
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Global sections and the actual constant-chart Hom functor

The rank-one constant diagram used by the tuple resolution represents
compatible chart sections. Actual sheaf gluing identifies these with
global sections, over the actual base field. The forward map is literal
restriction to each chart, and is natural in every coefficient map.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ToricPower.FiniteCech

variable {B : Type} [SemilatticeInf B] (k : Type) [Field k]
  {T : TopCat.{0}} (opens : B ⥤ Opens T)

@[simp]
theorem tupleConstant_map_generator {b c : Bᵒᵖ} (f : b ⟶ c) :
    (tupleAugmented k (B := B)).right.map f (ModuleCat.freeMk PUnit.unit) =
      ModuleCat.freeMk PUnit.unit :=
  ModuleCat.free_map_apply _ _

/-- A natural map out of the actual constant free rank-one diagram
has exactly compatible values on its actual generator. -/
theorem tupleConstant_hom_restrict (F : TopCat.Presheaf (ModuleCat.{0} k) T)
    (φ : (tupleAugmented k (B := B)).right ⟶ opens.op ⋙ F)
    {b c : B} (h : c ≤ b) :
    F.map (opens.map (homOfLE h)).op (φ.app (op b) (ModuleCat.freeMk PUnit.unit)) =
      φ.app (op c) (ModuleCat.freeMk PUnit.unit) := by
  have eq := ConcreteCategory.congr_hom (φ.naturality (homOfLE h).op)
    (ModuleCat.freeMk PUnit.unit)
  change φ.app (op c)
      ((ModuleCat.free k).map (↾fun x : PUnit => x) (ModuleCat.freeMk PUnit.unit)) = _ at eq
  rw [ModuleCat.free_map_apply] at eq
  exact eq.symm

/-- Restriction of an actual section over the union to the constant
rank-one chart diagram, as a base-field linear map. -/
def unionTupleSectionsMap (F : TopCat.Presheaf (ModuleCat.{0} k) T) :
    F.obj (op (iSup opens.obj)) →ₗ[k]
      ((tupleAugmented k (B := B)).right ⟶ opens.op ⋙ F) where
  toFun x :=
    { app b := ModuleCat.freeDesc (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj b.unop).op x)
      naturality {b c} f := by
        apply ModuleCat.free_hom_ext
        intro p
        cases p
        change ModuleCat.freeDesc
            (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj c.unop).op x)
            ((tupleAugmented k (B := B)).right.map f (ModuleCat.freeMk PUnit.unit)) =
          F.map (opens.map f.unop).op (ModuleCat.freeDesc
            (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj b.unop).op x)
              (ModuleCat.freeMk PUnit.unit))
        rw [tupleConstant_map_generator, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        change F.map (Opens.leSupr opens.obj c.unop).op x =
          F.map (opens.map f.unop).op (F.map (Opens.leSupr opens.obj b.unop).op x)
        rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp]
        congr 2 }
  map_add' x y := by
    apply NatTrans.ext
    funext b
    apply ModuleCat.free_hom_ext
    intro p
    change ModuleCat.freeDesc
      (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj b.unop).op (x+y)) (ModuleCat.freeMk p) =
      ModuleCat.freeDesc (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj b.unop).op x)
        (ModuleCat.freeMk p) +
      ModuleCat.freeDesc (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj b.unop).op y)
        (ModuleCat.freeMk p)
    simp only [ModuleCat.freeDesc_apply, map_add]
    rfl
  map_smul' r x := by
    apply NatTrans.ext
    funext b
    apply ModuleCat.free_hom_ext
    intro p
    change ModuleCat.freeDesc
      (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj b.unop).op (r • x)) (ModuleCat.freeMk p) =
      r • ModuleCat.freeDesc (↾fun _ : PUnit => F.map (Opens.leSupr opens.obj b.unop).op x)
        (ModuleCat.freeMk p)
    simp only [ModuleCat.freeDesc_apply, map_smul, RingHom.id_apply]
    rfl

@[simp]
theorem unionTupleSectionsMap_generator (F : TopCat.Presheaf (ModuleCat.{0} k) T)
    (x : F.obj (op (iSup opens.obj))) (b : B) :
    (unionTupleSectionsMap k opens F x).app (op b) (ModuleCat.freeMk PUnit.unit) =
      F.map (Opens.leSupr opens.obj b).op x := by
  change ModuleCat.freeDesc (↾fun _ : PUnit =>
    F.map (Opens.leSupr opens.obj b).op x) (ModuleCat.freeMk PUnit.unit) = _
  exact ModuleCat.freeDesc_apply _ _

variable (infEq : ∀ b c, opens.obj (b ⊓ c) = opens.obj b ⊓ opens.obj c)

include infEq in
/-- The actual chart values agree on the literal open intersections. -/
theorem tupleConstant_hom_compatible (F : TopCat.Presheaf (ModuleCat.{0} k) T)
    (φ : (tupleAugmented k (B := B)).right ⟶ opens.op ⋙ F) :
    TopCat.Presheaf.IsCompatible F opens.obj
      (fun b => φ.app (op b) (ModuleCat.freeMk PUnit.unit)) := by
  intro b c
  have hb := tupleConstant_hom_restrict k opens F φ (show b ⊓ c ≤ b from inf_le_left)
  have hc := tupleConstant_hom_restrict k opens F φ (show b ⊓ c ≤ c from inf_le_right)
  have eq := congrArg (fun x => F.map (eqToHom (infEq b c).symm).op x) (hb.trans hc.symm)
  have leftMap : F.map (opens.map (homOfLE (show b ⊓ c ≤ b from inf_le_left))).op ≫
      F.map (eqToHom (infEq b c).symm).op =
        F.map ((opens.obj b).infLELeft (opens.obj c)).op := by
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
  have rightMap : F.map (opens.map (homOfLE (show b ⊓ c ≤ c from inf_le_right))).op ≫
      F.map (eqToHom (infEq b c).symm).op =
        F.map ((opens.obj b).infLERight (opens.obj c)).op := by
    rw [← CategoryTheory.Functor.map_comp]
    congr 1
  change (F.map (opens.map (homOfLE (show b ⊓ c ≤ b from inf_le_left))).op ≫
      F.map (eqToHom (infEq b c).symm).op) _ =
    (F.map (opens.map (homOfLE (show b ⊓ c ≤ c from inf_le_right))).op ≫
      F.map (eqToHom (infEq b c).symm).op) _ at eq
  rw [leftMap, rightMap] at eq
  exact eq

include infEq in
/-- Unique gluing proves bijectivity of the actual scalar-linear restriction map. -/
theorem unionTupleSectionsMap_bijective (F : TopCat.Sheaf (ModuleCat.{0} k) T) :
    Function.Bijective (unionTupleSectionsMap k opens F.obj) := by
  constructor
  · intro x y h
    apply F.eq_of_locally_eq opens.obj
    intro b
    have e := congrArg (fun φ => φ.app (op b) (ModuleCat.freeMk PUnit.unit)) h
    simpa only [unionTupleSectionsMap_generator] using e
  · intro φ
    obtain ⟨x, hx, _⟩ := F.existsUnique_gluing opens.obj
      (fun b => φ.app (op b) (ModuleCat.freeMk PUnit.unit))
      (tupleConstant_hom_compatible k opens infEq F.obj φ)
    refine ⟨x, ?_⟩
    apply NatTrans.ext
    funext b
    apply ModuleCat.free_hom_ext
    intro p
    cases p
    exact (unionTupleSectionsMap_generator k opens F.obj x b.unop).trans (hx b.unop)

/-- A genuine scalar-linear isomorphism, supplied by actual sheaf gluing. -/
def unionTupleSectionsIso (F : TopCat.Sheaf (ModuleCat.{0} k) T) :
    F.obj.obj (op (iSup opens.obj)) ≅
      ModuleCat.of k ((tupleAugmented k (B := B)).right ⟶ opens.op ⋙ F.obj) :=
  (LinearEquiv.ofBijective (unionTupleSectionsMap k opens F.obj)
    (unionTupleSectionsMap_bijective k opens infEq F)).toModuleIso

variable (X : Scheme) [X.Over (Spec (.of k))] (charts : B ⥤ X.Opens)
  (chartsInf : ∀ b c, charts.obj (b ⊓ c) = charts.obj b ⊓ charts.obj c)
  (cover : iSup charts.obj = ⊤)

/-- Actual global sections are the actual constant-chart Hom module. -/
def globalTupleSectionsIso (M : X.Modules) :
    (FiniteCover.schemeBaseSections k X ⊤).obj M ≅
      ModuleCat.of k ((tupleAugmented k (B := B)).right ⟶
        (meetChartSectionsFunctor k X charts).obj M) :=
  ((FiniteCover.schemeBaseSheaf k X).obj M).obj.mapIso (eqToIso cover).op ≪≫
    unionTupleSectionsIso k charts chartsInf ((FiniteCover.schemeBaseSheaf k X).obj M)

/-- Forward evaluation is literal restriction from the whole scheme. -/
theorem globalTupleSectionsIso_generator (M : X.Modules)
    (x : (FiniteCover.schemeBaseSections k X ⊤).obj M) (b : B) :
    ((globalTupleSectionsIso k X charts chartsInf cover M).hom x).app (op b)
        (ModuleCat.freeMk PUnit.unit) =
      M.presheaf.map (homOfLE (show charts.obj b ≤ ⊤ from le_top)).op x := by
  change (unionTupleSectionsMap k charts _
    (((FiniteCover.schemeBaseSheaf k X).obj M).obj.map (eqToHom cover).op x)).app
      (op b) (ModuleCat.freeMk PUnit.unit) = _
  rw [unionTupleSectionsMap_generator, ← ModuleCat.comp_apply,
    ← CategoryTheory.Functor.map_comp]
  rfl

/-- Every coefficient map commutes with the actual global-section comparison. -/
theorem globalTupleSectionsIso_naturality {M N : X.Modules} (f : M ⟶ N) :
    (FiniteCover.schemeBaseSections k X ⊤).map f ≫
        (globalTupleSectionsIso k X charts chartsInf cover N).hom =
      (globalTupleSectionsIso k X charts chartsInf cover M).hom ≫
        ((linearCoyoneda k (Bᵒᵖ ⥤ ModuleCat k)).obj (op (tupleAugmented k).right)).map
          ((meetChartSectionsFunctor k X charts).map f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply NatTrans.ext
  funext b
  apply ModuleCat.free_hom_ext
  intro p
  cases p
  change (((globalTupleSectionsIso k X charts chartsInf cover N).hom
    ((FiniteCover.schemeBaseSections k X ⊤).map f x)).app b) _ =
      ((meetChartSectionsFunctor k X charts).map f).app b
        ((((globalTupleSectionsIso k X charts chartsInf cover M).hom x).app b) _)
  rw [globalTupleSectionsIso_generator, globalTupleSectionsIso_generator]
  exact (ConcreteCategory.congr_hom
    (f.val.naturality (homOfLE (show charts.obj b.unop ≤ ⊤ from le_top)).op) x).symm

end ToricPower.FiniteCech
