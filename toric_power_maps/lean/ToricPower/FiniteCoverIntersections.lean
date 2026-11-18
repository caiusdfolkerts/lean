module

public import ToricPower.CellularConeResolution
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Data.Fintype.Powerset

/-!
# The actual finite intersection category of an open cover

Objects are nonempty finite subsets of the cover index set, and arrows
are inclusions.  Their section diagram uses the literal restriction
maps on the corresponding intersections.  The finite grade is cardinality;
in particular, this construction does not confuse normalization of the
all-tuples Čech complex with a bounded ordered Čech complex.

The ordinary global-sections comparison below is proved by actual sheaf
gluing.  The finite projective resolution is a resolution in this actual
diagram category.  A comparison of its derived limit with unbounded sheaf
hypercohomology is a further theorem, not a hypothesis of these definitions.

Candidate source pending checking by the pinned Lean compiler.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace ToricPower.FiniteCover

universe u

/-- The actual intersection category, with its inherited inclusion order. -/
abbrev Index (I : Type u) := { S : Finset I // S.Nonempty }

instance index_finite (I : Type u) [Finite I] : Finite (Index I) := by
  letI := Fintype.ofFinite I
  exact Finite.of_injective Subtype.val Subtype.val_injective

variable {I : Type u} [DecidableEq I]

def singleton (i : I) : Index I := ⟨{i}, by simp⟩

def pair (i j : I) : Index I := ⟨{i, j}, by simp⟩

def grade (S : Index I) : ℕ := S.val.card

theorem grade_le {S T : Index I} (f : S ⟶ T) : grade S ≤ grade T :=
  Finset.card_le_card (leOfHom f)

theorem eq_of_grade_eq {S T : Index I} (f : S ⟶ T)
    (h : grade S = grade T) : S = T := by
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le (leOfHom f) h.ge

theorem grade_bound [Fintype I] (S : Index I) : grade S ≤ Fintype.card I :=
  Finset.card_le_univ S.val

/-- The literal open intersection belonging to a finite nonempty subset. -/
def intersection {X : TopCat.{u}} (U : I → Opens X) (S : Index I) : Opens X :=
  ⨅ i ∈ S.val, U i

theorem intersection_le {X : TopCat.{u}} (U : I → Opens X)
    (S : Index I) (i : I) (hi : i ∈ S.val) : intersection U S ≤ U i :=
  iInf_le_of_le i (iInf_le _ hi)

theorem intersection_antitone {X : TopCat.{u}} (U : I → Opens X)
    {S T : Index I} (h : S ≤ T) : intersection U T ≤ intersection U S := by
  apply le_iInf
  intro i
  apply le_iInf
  intro hi
  exact intersection_le U T i (h hi)

theorem intersection_le_union {X : TopCat.{u}} (U : I → Opens X)
    (S : Index I) : intersection U S ≤ iSup U := by
  obtain ⟨i, hi⟩ := S.property
  exact (intersection_le U S i hi).trans (le_iSup U i)

@[simp]
theorem intersection_singleton {X : TopCat.{u}} (U : I → Opens X) (i : I) :
    intersection U (singleton i) = U i := by
  simp [intersection, singleton]

@[simp]
theorem intersection_pair {X : TopCat.{u}} (U : I → Opens X) (i j : I) :
    intersection U (pair i j) = U i ⊓ U j := by
  simp [intersection, pair, iInf_or, iInf_inf_eq]

/-- The intersection functor is contravariant on actual opens. -/
def intersectionFunctor {X : TopCat.{u}} (U : I → Opens X) :
    Index I ⥤ (Opens X)ᵒᵖ where
  obj S := op (intersection U S)
  map f := (homOfLE (intersection_antitone U (leOfHom f))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable {k : Type u} [Field k] {X : TopCat.{u}} (U : I → Opens X)

/-- Restriction of the actual vector presheaf to finite intersections. -/
abbrev sectionsDiagram (F : TopCat.Presheaf (ModuleCat.{u} k) X) :
    Index I ⥤ ModuleCat.{u} k := intersectionFunctor U ⋙ F

/-- The actual sections on the union, with their actual restrictions. -/
def sectionsCone (F : TopCat.Presheaf (ModuleCat.{u} k) X) :
    Cone (sectionsDiagram U F) where
  pt := F.obj (op (iSup U))
  π :=
    { app := fun S => F.map (homOfLE (intersection_le_union U S)).op
      naturality := by
        intro S T f
        simp only [Functor.const_obj_map, Category.id_comp, Functor.comp_map]
        rw [← F.map_comp]
        congr 1 }

/-- A cone's singleton component, transported to its literal cover open. -/
def singletonSection (F : TopCat.Presheaf (ModuleCat.{u} k) X)
    (c : Cone (sectionsDiagram U F)) (i : I) : c.pt ⟶ F.obj (op (U i)) :=
  c.π.app (singleton i) ≫ F.map (eqToHom (intersection_singleton U i).symm).op

/-- Cone compatibility identifies the restriction of a singleton
component with every larger finite-intersection component. -/
theorem singletonSection_restrict
    (F : TopCat.Presheaf (ModuleCat.{u} k) X)
    (c : Cone (sectionsDiagram U F)) (S : Index I) (i : I) (hi : i ∈ S.val) :
    singletonSection U F c i ≫ F.map (homOfLE (intersection_le U S i hi)).op =
      c.π.app S := by
  let f : singleton i ⟶ S := homOfLE (show ({i} : Finset I) ⊆ S.val from
    Finset.singleton_subset_iff.mpr hi)
  rw [singletonSection, Category.assoc, ← F.map_comp]
  have hmap : (eqToHom (intersection_singleton U i).symm).op ≫
      (homOfLE (intersection_le U S i hi)).op = (intersectionFunctor U).map f :=
    Subsingleton.elim _ _
  rw [hmap]
  exact c.w f

theorem singletonSection_compatible
    (F : TopCat.Presheaf (ModuleCat.{u} k) X)
    (c : Cone (sectionsDiagram U F)) (x : c.pt) :
    TopCat.Presheaf.IsCompatible F U (fun i => singletonSection U F c i x) := by
  intro i j
  let S := pair i j
  have hi := singletonSection_restrict U F c S i (by simp [S, pair])
  have hj := singletonSection_restrict U F c S j (by simp [S, pair])
  have h := hi.trans hj.symm
  have he : intersection U S = U i ⊓ U j := intersection_pair U i j
  have h' := congrArg (fun f => f ≫ F.map (eqToHom he.symm).op) h
  simp only [Category.assoc, ← F.map_comp] at h'
  exact ConcreteCategory.congr_hom h' x

/-- The actual unique gluing of the singleton components of a cone. -/
def coneGluing (F : TopCat.Sheaf (ModuleCat.{u} k) X)
    (c : Cone (sectionsDiagram U F.obj)) (x : c.pt) : F.obj.obj (op (iSup U)) :=
  (F.existsUnique_gluing U (fun i => singletonSection U F.obj c i x)
    (singletonSection_compatible U F.obj c x)).choose

theorem coneGluing_restrict_singleton (F : TopCat.Sheaf (ModuleCat.{u} k) X)
    (c : Cone (sectionsDiagram U F.obj)) (x : c.pt) (i : I) :
    F.obj.map (Opens.leSupr U i).op (coneGluing U F c x) =
      singletonSection U F.obj c i x :=
  (F.existsUnique_gluing U (fun i => singletonSection U F.obj c i x)
    (singletonSection_compatible U F.obj c x)).choose_spec.1 i

theorem coneGluing_restrict (F : TopCat.Sheaf (ModuleCat.{u} k) X)
    (c : Cone (sectionsDiagram U F.obj)) (x : c.pt) (S : Index I) :
    F.obj.map (homOfLE (intersection_le_union U S)).op (coneGluing U F c x) =
      c.π.app S x := by
  obtain ⟨i, hi⟩ := S.property
  have hmap : F.obj.map (homOfLE (intersection_le_union U S)).op =
      F.obj.map (Opens.leSupr U i).op ≫
        F.obj.map (homOfLE (intersection_le U S i hi)).op := by
    rw [← F.obj.map_comp]
    congr 1
  rw [hmap, ModuleCat.comp_apply, coneGluing_restrict_singleton]
  exact ConcreteCategory.congr_hom (singletonSection_restrict U F.obj c S i hi) x

/-- Gluing is linear because restriction and the original cone are linear,
and actual sheaf separatedness detects equality of sections. -/
def coneGluingHom (F : TopCat.Sheaf (ModuleCat.{u} k) X)
    (c : Cone (sectionsDiagram U F.obj)) : c.pt ⟶ F.obj.obj (op (iSup U)) :=
  ModuleCat.ofHom
    { toFun := coneGluing U F c
      map_add' := by
        intro x y
        apply F.eq_of_locally_eq U
        intro i
        simp only [coneGluing_restrict_singleton, map_add]
      map_smul' := by
        intro r x
        apply F.eq_of_locally_eq U
        intro i
        simp only [coneGluing_restrict_singleton, map_smul, RingHom.id_apply] }

/-- Ordinary sections over the union are the actual categorical limit
of the full finite-intersection diagram. -/
def sectionsConeIsLimit (F : TopCat.Sheaf (ModuleCat.{u} k) X) :
    IsLimit (sectionsCone U F.obj) where
  lift c := coneGluingHom U F c
  fac c S := by
    ext x
    exact coneGluing_restrict U F c x S
  uniq c m hm := by
    ext x
    apply F.eq_of_locally_eq U
    intro i
    change F.obj.map (Opens.leSupr U i).op (m x) =
      F.obj.map (Opens.leSupr U i).op (coneGluing U F c x)
    rw [coneGluing_restrict_singleton]
    have h := congrArg (fun f => f ≫
      F.obj.map (eqToHom (intersection_singleton U i).symm).op) (hm (singleton i))
    simp only [sectionsCone, Category.assoc, ← F.obj.map_comp] at h
    exact ConcreteCategory.congr_hom h x

/-- The comparison is an actual isomorphism, obtained from the proved
limit cone rather than from a postulated descent equivalence. -/
def globalSectionsLimitIso (F : TopCat.Sheaf (ModuleCat.{u} k) X) :
    F.obj.obj (op (iSup U)) ≅ limit (sectionsDiagram U F.obj) :=
  IsLimit.conePointUniqueUpToIso (sectionsConeIsLimit U F)
    (limit.isLimit (sectionsDiagram U F.obj))

section Finite

variable [Fintype I]

/-- Every diagram on the literal finite intersection category has a
finite projective resolution.  No bound is imposed on its vector spaces. -/
theorem diagramSyzygy_isZero (F : Index I ⥤ ModuleCat.{u} k) :
    IsZero ((Cellular.diagramSyzygyIterate k (Fintype.card I + 1)).obj F) :=
  Cellular.diagramSyzygyIterate_isZero k grade
    (fun f => grade_le f) (fun f h => eq_of_grade_eq f h) F
    (Fintype.card I) (fun S => grade_bound S)

/-- The actual finite-cone replacement works for arbitrary unbounded
complexes of these intersection diagrams. -/
theorem finiteConeResolution_quasiIso
    (K : CochainComplex (Index I ⥤ ModuleCat.{u} k) ℤ) :
    QuasiIso ((Cellular.finiteConeResolution k (Fintype.card I + 1)).augmentation.app K) :=
  Cellular.finiteConeResolution_augmentation_quasiIso k grade
    (fun f => grade_le f) (fun f h => eq_of_grade_eq f h)
    (Fintype.card I) (fun S => grade_bound S) K

end Finite

end ToricPower.FiniteCover

end
