module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing actual morphisms of module sheaves

Local linear morphisms which agree on overlaps glue to a unique global
linear morphism. The underlying additive morphism is obtained from the
ordinary sheaf of homomorphisms; linearity is checked on the same cover.
This is the descent step needed to compare Cartier frames under morphisms
which need not be dominant.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace ToricPower.SheafModuleGluing

universe u v

variable {X : Scheme.{u}} {Index : Type v}
  (opens : Index → X.Opens) (covers : IsOpenCover opens) {M N : X.Modules}

/-- The ordinary sheaf of additive homomorphisms on open subsets. -/
def additiveHomSheaf (M N : X.Modules) : TopCat.Sheaf (Type _) X :=
  ⟨CategoryTheory.presheafHom M.presheaf N.presheaf,
    N.isSheaf.hom M.presheaf⟩

/-- A module morphism on an open set is a section of the additive hom sheaf. -/
def localHomSection {U : X.Opens} (mapping : M.over U ⟶ N.over U) :
    (CategoryTheory.presheafHom M.presheaf N.presheaf).obj (op U) :=
  (PresheafOfModules.toPresheaf _).map mapping.val

variable (maps : ∀ index, M.over (opens index) ⟶ N.over (opens index))

/-- Compatibility means equality of the actual additive morphisms on each
overlap, throughout all of its smaller open subsets. -/
def Compatible : Prop :=
  TopCat.Presheaf.IsCompatible
    (CategoryTheory.presheafHom M.presheaf N.presheaf) opens
      (fun index => localHomSection (M := M) (N := N) (maps index))

variable (compatible : Compatible opens maps)

include covers compatible in
theorem existsUnique_gluedOverTop :
    ∃! sectionValue : (CategoryTheory.presheafHom M.presheaf N.presheaf).obj (op ⊤),
      ∀ index, (CategoryTheory.presheafHom M.presheaf N.presheaf).map
        (homOfLE (le_top : opens index ≤ ⊤)).op sectionValue =
          localHomSection (M := M) (N := N) (maps index) := by
  exact (additiveHomSheaf M N).existsUnique_gluing' opens ⊤
    (fun _ => homOfLE le_top) (by rw [covers.iSup_eq_top])
    (fun index => localHomSection (M := M) (N := N) (maps index))
    (by change Compatible opens maps; exact compatible)

def gluedOverTop :
    (CategoryTheory.presheafHom M.presheaf N.presheaf).obj (op ⊤) :=
  (existsUnique_gluedOverTop opens covers maps compatible).exists.choose

theorem gluedOverTop_restrict (index : Index) :
    (CategoryTheory.presheafHom M.presheaf N.presheaf).map
      (homOfLE (le_top : opens index ≤ ⊤)).op
        (gluedOverTop opens covers maps compatible) = localHomSection (M := M) (N := N) (maps index) :=
  (existsUnique_gluedOverTop opens covers maps compatible).exists.choose_spec index

/-- The global additive morphism represented by the glued section over the
terminal open set. -/
def gluedAdditiveHom : M.presheaf ⟶ N.presheaf where
  app U := (gluedOverTop opens covers maps compatible).app
    (op (Over.mk (homOfLE (le_top : U.unop ≤ ⊤))))
  naturality {U V} f := by
    exact (gluedOverTop opens covers maps compatible).naturality
      (Over.homMk f.unop :
        Over.mk (homOfLE (le_top : V.unop ≤ ⊤)) ⟶
          Over.mk (homOfLE (le_top : U.unop ≤ ⊤))).op

theorem gluedAdditiveHom_local (index : Index) (U : X.Opens) (included : U ≤ opens index) :
    (gluedAdditiveHom opens covers maps compatible).app (op U) =
      (localHomSection (M := M) (N := N) (maps index)).app (op (Over.mk (homOfLE included))) := by
  have same := congrArg
    (fun mapping => mapping.app (op (Over.mk (homOfLE included))))
    (gluedOverTop_restrict opens covers maps compatible index)
  exact same

theorem gluedAdditiveHom_smul (U : X.Opens) (r : Γ(X, U)) (sectionValue : Γ(M, U)) :
    (gluedAdditiveHom opens covers maps compatible).app (op U) (r • sectionValue) =
      r • (gluedAdditiveHom opens covers maps compatible).app (op U) sectionValue := by
  let coefficientSheaf : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  apply coefficientSheaf.eq_of_locally_eq'
    (fun index => U ⊓ opens index) U (fun _ => homOfLE inf_le_left)
    (by
      intro point present
      obtain ⟨index, contained⟩ := covers.exists_mem point
      exact Opens.mem_iSup.mpr ⟨index, present, contained⟩)
  intro index
  let inclusion : U ⊓ opens index ⟶ U := homOfLE inf_le_left
  have naturality := (gluedAdditiveHom opens covers maps compatible).naturality inclusion.op
  have on_scalar := ConcreteCategory.congr_hom naturality (r • sectionValue)
  have on_section := ConcreteCategory.congr_hom naturality sectionValue
  simp only [ConcreteCategory.comp_apply] at on_scalar on_section
  change N.presheaf.map inclusion.op
      ((gluedAdditiveHom opens covers maps compatible).app (op U) (r • sectionValue)) =
    N.presheaf.map inclusion.op
      (r • (gluedAdditiveHom opens covers maps compatible).app (op U) sectionValue)
  rw [← on_scalar, M.map_smul, N.map_smul, ← on_section,
    gluedAdditiveHom_local opens covers maps compatible index (U ⊓ opens index) inf_le_right]
  exact ((maps index).val.app (op (Over.mk (homOfLE inf_le_right)))).hom.map_smul _ _

/-- The glued map is an actual morphism of module sheaves. -/
def glueHom : M ⟶ N :=
  ⟨PresheafOfModules.homMk (gluedAdditiveHom opens covers maps compatible)
    (fun U => gluedAdditiveHom_smul opens covers maps compatible U.unop)⟩

/-- Restriction of the glued morphism recovers the prescribed local map. -/
theorem glueHom_over (index : Index) :
    (glueHom opens covers maps compatible).over (opens index) = maps index := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  exact ConcreteCategory.congr_hom
    (gluedAdditiveHom_local opens covers maps compatible index U.unop.left U.unop.hom.le) value

include covers in
/-- Equality of module morphisms is detected on an arbitrary open cover. -/
theorem hom_ext_of_cover (first second : M ⟶ N)
    (localEquality : ∀ index, first.over (opens index) = second.over (opens index)) :
    first = second := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  change first.mapPresheaf.app U value = second.mapPresheaf.app U value
  let coefficientSheaf : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  apply coefficientSheaf.eq_of_locally_eq'
    (fun index => U.unop ⊓ opens index) U.unop (fun _ => homOfLE inf_le_left)
    (by
      intro point present
      obtain ⟨index, contained⟩ := covers.exists_mem point
      exact Opens.mem_iSup.mpr ⟨index, present, contained⟩)
  intro index
  let inclusion : U.unop ⊓ opens index ⟶ U.unop := homOfLE inf_le_left
  have firstNatural := ConcreteCategory.congr_hom
    (first.mapPresheaf.naturality inclusion.op) value
  have secondNatural := ConcreteCategory.congr_hom
    (second.mapPresheaf.naturality inclusion.op) value
  simp only [ConcreteCategory.comp_apply] at firstNatural secondNatural
  change N.presheaf.map inclusion.op (first.mapPresheaf.app U value) =
    N.presheaf.map inclusion.op (second.mapPresheaf.app U value)
  rw [← firstNatural, ← secondNatural]
  exact congrArg
    (fun morphism => morphism.val.app
      (op (Over.mk (homOfLE (inf_le_right : U.unop ⊓ opens index ≤ opens index))))
      (M.presheaf.map inclusion.op value)) (localEquality index)

/-- The gluing is unique among actual module morphisms. -/
theorem glueHom_unique (morphism : M ⟶ N)
    (localEquality : ∀ index, morphism.over (opens index) = maps index) :
    glueHom opens covers maps compatible = morphism := by
  apply hom_ext_of_cover opens covers
  intro index
  exact (glueHom_over opens covers maps compatible index).trans (localEquality index).symm

def localAdditiveIso {U : X.Opens} (equivalence : M.over U ≅ N.over U) :
    (Over.forget U).op ⋙ M.presheaf ≅ (Over.forget U).op ⋙ N.presheaf where
  hom := localHomSection (M := M) (N := N) equivalence.hom
  inv := localHomSection (M := N) (N := M) equivalence.inv
  hom_inv_id := by
    ext V value
    exact congrArg (fun morphism => morphism.val.app V value) equivalence.hom_inv_id
  inv_hom_id := by
    ext V value
    exact congrArg (fun morphism => morphism.val.app V value) equivalence.inv_hom_id

/-- Compatibility of local isomorphisms automatically implies compatibility
of their inverses; no extra descent premise is introduced. -/
theorem compatible_iso_inv (equivalences : ∀ index, M.over (opens index) ≅ N.over (opens index))
    (compatibleHom : Compatible opens (fun index => (equivalences index).hom)) :
    Compatible opens (fun index => (equivalences index).inv) := by
  intro first second
  let left := CategoryTheory.Functor.isoWhiskerLeft
    (Over.map (Opens.infLELeft (opens first) (opens second))).op
      (localAdditiveIso (M := M) (N := N) (equivalences first))
  let right := CategoryTheory.Functor.isoWhiskerLeft
    (Over.map (Opens.infLERight (opens first) (opens second))).op
      (localAdditiveIso (M := M) (N := N) (equivalences second))
  have same : left.hom = right.hom := compatibleHom first second
  exact congrArg Iso.inv (Iso.ext same)

/-- Compatible local isomorphisms glue to a genuine global isomorphism. -/
def glueIso (equivalences : ∀ index, M.over (opens index) ≅ N.over (opens index))
    (compatibleHom : Compatible opens (fun index => (equivalences index).hom)) : M ≅ N where
  hom := glueHom opens covers (fun index => (equivalences index).hom) compatibleHom
  inv := glueHom opens covers (fun index => (equivalences index).inv)
    (compatible_iso_inv opens equivalences compatibleHom)
  hom_inv_id := by
    apply hom_ext_of_cover opens covers
    intro index
    change (glueHom opens covers (fun index => (equivalences index).hom) compatibleHom).over
        (opens index) ≫
      (glueHom opens covers (fun index => (equivalences index).inv)
        (compatible_iso_inv opens equivalences compatibleHom)).over (opens index) = 𝟙 _
    exact (congrArg₂ (fun first second => first ≫ second)
      (glueHom_over opens covers (fun index => (equivalences index).hom) compatibleHom index)
      (glueHom_over opens covers (fun index => (equivalences index).inv)
        (compatible_iso_inv opens equivalences compatibleHom) index)).trans
      (equivalences index).hom_inv_id
  inv_hom_id := by
    apply hom_ext_of_cover opens covers
    intro index
    change (glueHom opens covers (fun index => (equivalences index).inv)
        (compatible_iso_inv opens equivalences compatibleHom)).over (opens index) ≫
      (glueHom opens covers (fun index => (equivalences index).hom) compatibleHom).over
        (opens index) = 𝟙 _
    exact (congrArg₂ (fun first second => first ≫ second)
      (glueHom_over opens covers (fun index => (equivalences index).inv)
        (compatible_iso_inv opens equivalences compatibleHom) index)
      (glueHom_over opens covers (fun index => (equivalences index).hom) compatibleHom index)).trans
      (equivalences index).inv_hom_id

end ToricPower.SheafModuleGluing
