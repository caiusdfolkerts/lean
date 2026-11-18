module

public import ToricPower.CellularVectorCover
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Finite projective resolutions for the actual incidence category

The natural vector cover is an isomorphism at a lowest nonzero stratum.
Its actual kernel therefore loses that stratum. Iterating the construction
gives a functorial projective resolution, and the genuine dimension bound
of the arrangement makes that resolution finite. No incidence is erased
and no boundedness condition is placed on the coefficient vector spaces.

This is a construction in the actual abelian diagram category. Passing
from this objectwise finite resolution to a functor on the unbounded
derived category requires a separate finite-totalization argument.

-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ToricPower.Cellular

universe u

variable (k : Type u) [Field k] {C : Type u} [Category.{u} C]

/-- The actual generators of a vector cover also jointly detect maps
after evaluating at an individual object. Evaluation preserves the two
coproducts used in the construction. -/
theorem diagramVectorCover_app_hom_ext (F : C ⥤ ModuleCat.{u} k) (d : C)
    {T : ModuleCat.{u} k}
    {f g : (diagramVectorCoverObj k F).obj d ⟶ T}
    (h : ∀ (c : C) (x : F.obj c) (a : c ⟶ d),
      f ((diagramVectorCoverInclusion k F c x).app d (ModuleCat.freeMk a)) =
        g ((diagramVectorCoverInclusion k F c x).app d (ModuleCat.freeMk a))) :
    f = g := by
  let E := (evaluation C (ModuleCat.{u} k)).obj d
  apply (isColimitOfHasCoproductOfPreservesColimit E
    (fun c : C => vectorCopower k (representable k c) (F.obj c))).hom_ext
  rintro ⟨c⟩
  change (Sigma.ι (fun c : C => vectorCopower k (representable k c) (F.obj c)) c).app d ≫ f =
    (Sigma.ι (fun c : C => vectorCopower k (representable k c) (F.obj c)) c).app d ≫ g
  apply (isColimitOfHasCoproductOfPreservesColimit E
    (fun _ : Module.Free.ChooseBasisIndex k (F.obj c) => representable k c)).hom_ext
  rintro ⟨i⟩
  apply ModuleCat.free_hom_ext
  intro a
  have h' := h c (Module.Free.chooseBasis k (F.obj c) i) a
  simp only [diagramVectorCoverInclusion, vectorCopowerInclusion_basis,
    NatTrans.comp_app, ModuleCat.comp_apply] at h'
  exact h'

/-- The identity-incidence summand gives an actual linear section at
each object. It need not be natural in that object. -/
def diagramVectorCoverSection (F : C ⥤ ModuleCat.{u} k) (d : C) :
    F.obj d ⟶ (diagramVectorCoverObj k F).obj d :=
  ModuleCat.ofHom ((representableHomLinearEquiv k (diagramVectorCoverObj k F) d).toLinearMap.comp
    ((Linear.rightComp k (representable k d)
      (Sigma.ι (fun c : C => vectorCopower k (representable k c) (F.obj c)) d)).comp
      (vectorCopowerInclusion k (representable k d) (F.obj d))))

@[simp]
theorem diagramVectorCoverSection_apply (F : C ⥤ ModuleCat.{u} k) (d : C)
    (x : F.obj d) :
    diagramVectorCoverSection k F d x =
      (diagramVectorCoverInclusion k F d x).app d (ModuleCat.freeMk (𝟙 d)) := rfl

@[reassoc (attr := simp)]
theorem diagramVectorCoverSection_map (F : C ⥤ ModuleCat.{u} k) (d : C) :
    diagramVectorCoverSection k F d ≫ (diagramVectorCoverMap k F).app d = 𝟙 _ := by
  ext x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (diagramVectorCoverInclusion_map k F d x) d)
    (ModuleCat.freeMk (𝟙 d))
  simpa only [ModuleCat.comp_apply, diagramVectorCoverSection_apply,
    NatTrans.comp_app, fromValue_app_freeMk,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply] using h

section Direct

variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  [∀ c : C, Subsingleton (c ⟶ c)]

include grade_le eq_of_grade_eq

/-- At a lowest nonzero stratum, the vector cover is exactly the value
of the original diagram. The proof uses actual incidence generators;
the unique identity incidence supplies the inverse. -/
theorem diagramVectorCoverMap_isIso_at_lowest
    (F : C ⥤ ModuleCat.{u} k) (d : C)
    (hvanish : ∀ c : C, grade c < grade d → IsZero (F.obj c)) :
    IsIso ((diagramVectorCoverMap k F).app d) := by
  refine ⟨⟨diagramVectorCoverSection k F d, ?_, diagramVectorCoverSection_map k F d⟩⟩
  apply diagramVectorCover_app_hom_ext k F d
  intro c x a
  have hmap := ConcreteCategory.congr_hom
    (NatTrans.congr_app (diagramVectorCoverInclusion_map k F c x) d)
    (ModuleCat.freeMk a)
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at hmap
  have hm : (diagramVectorCoverMap k F).app d
      ((diagramVectorCoverInclusion k F c x).app d (ModuleCat.freeMk a)) = F.map a x :=
    hmap.trans (fromValue_app_freeMk k F c d x a)
  change diagramVectorCoverSection k F d
      ((diagramVectorCoverMap k F).app d
        ((diagramVectorCoverInclusion k F c x).app d (ModuleCat.freeMk a))) =
    (diagramVectorCoverInclusion k F c x).app d (ModuleCat.freeMk a)
  rw [hm]
  by_cases hlt : grade c < grade d
  · letI : Subsingleton (F.obj c) := ModuleCat.subsingleton_of_isZero (hvanish c hlt)
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp [fromValue, diagramVectorCoverInclusion]
  · have heq : c = d := eq_of_grade_eq a (le_antisymm (grade_le a) (Nat.le_of_not_gt hlt))
    subst c
    have ha : a = 𝟙 d := Subsingleton.elim _ _
    subst a
    simp only [fromValue_app_freeMk, CategoryTheory.Functor.map_id,
      ModuleCat.id_apply, diagramVectorCoverSection_apply]

/-- Taking the actual kernel removes every stratum at the current
lowest dimension, not just those at which a chosen scalar happens to
be nonzero. -/
theorem diagramVectorCoverKernel_support_drop
    (F : C ⥤ ModuleCat.{u} k) (m : ℕ)
    (hvanish : ∀ c : C, grade c < m → IsZero (F.obj c))
    (d : C) (hd : grade d ≤ m) :
    IsZero ((kernel (diagramVectorCoverMap k F)).obj d) := by
  letI : IsIso ((diagramVectorCoverMap k F).app d) :=
    diagramVectorCoverMap_isIso_at_lowest k grade grade_le eq_of_grade_eq F d
      (fun c hc => hvanish c (lt_of_lt_of_le hc hd))
  exact (isZero_kernel_of_mono ((diagramVectorCoverMap k F).app d)).of_iso
    (PreservesKernel.iso ((evaluation C (ModuleCat.{u} k)).obj d)
      (diagramVectorCoverMap k F))

end Direct

/-- The actual functorial kernel of the natural vector cover. -/
def diagramSyzygy : (C ⥤ ModuleCat.{u} k) ⥤ C ⥤ ModuleCat.{u} k where
  obj F := kernel (diagramVectorCoverMap k F)
  map {F G} η := kernel.map (diagramVectorCoverMap k F) (diagramVectorCoverMap k G)
    ((diagramVectorCover k).map η) η ((diagramVectorCoverCounit k).naturality η).symm
  map_id F := by
    apply (cancel_mono (kernel.ι (diagramVectorCoverMap k F))).mp
    simp only [kernel.map, kernel.lift_ι, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact Category.comp_id _
  map_comp η θ := by
    apply (cancel_mono (kernel.ι (diagramVectorCoverMap k _))).mp
    simp only [Category.assoc, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc,
      CategoryTheory.Functor.map_comp]

/-- Its inclusion is a genuine natural transformation. -/
def diagramSyzygyInclusion : diagramSyzygy k (C := C) ⟶ diagramVectorCover k where
  app F := kernel.ι (diagramVectorCoverMap k F)
  naturality {_ _} η := by simp only [diagramSyzygy, kernel.map, kernel.lift_ι]

/-- Iterated actual syzygies, retaining their natural functoriality. -/
def diagramSyzygyIterate : ℕ → ((C ⥤ ModuleCat.{u} k) ⥤ C ⥤ ModuleCat.{u} k)
  | 0 => 𝟭 _
  | m + 1 => diagramSyzygyIterate m ⋙ diagramSyzygy k

@[simp]
theorem diagramSyzygyIterate_zero_obj (F : C ⥤ ModuleCat.{u} k) :
    (diagramSyzygyIterate k 0).obj F = F := rfl

@[simp]
theorem diagramSyzygyIterate_succ_obj (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    (diagramSyzygyIterate k (m+1)).obj F =
      kernel (diagramVectorCoverMap k ((diagramSyzygyIterate k m).obj F)) := rfl

/-- Iteration commutes with one further application of the same actual
syzygy functor. This is a genuine equality of the recursively defined objects. -/
theorem diagramSyzygyIterate_commute_obj (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    (diagramSyzygyIterate k m).obj ((diagramSyzygy k).obj F) =
      (diagramSyzygy k).obj ((diagramSyzygyIterate k m).obj F) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (diagramSyzygy k).obj
        ((diagramSyzygyIterate k m).obj ((diagramSyzygy k).obj F)) =
      (diagramSyzygy k).obj ((diagramSyzygy k).obj ((diagramSyzygyIterate k m).obj F))
    rw [ih]

/-- The genuine projective term in degree `m`. -/
def diagramProjectiveTerm (F : C ⥤ ModuleCat.{u} k) (m : ℕ) : C ⥤ ModuleCat.{u} k :=
  diagramVectorCoverObj k ((diagramSyzygyIterate k m).obj F)

instance diagramProjectiveTerm_projective (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    Projective (diagramProjectiveTerm k F m) := by
  unfold diagramProjectiveTerm
  infer_instance

/-- The differential factors through the actual kernel of the preceding
cover, so the chain condition follows from the universal kernel equation. -/
def diagramProjectiveDifferential (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    diagramProjectiveTerm k F (m+1) ⟶ diagramProjectiveTerm k F m :=
  diagramVectorCoverMap k ((diagramSyzygyIterate k (m+1)).obj F) ≫
    kernel.ι (diagramVectorCoverMap k ((diagramSyzygyIterate k m).obj F))

@[reassoc (attr := simp)]
theorem diagramProjectiveDifferential_cover (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    diagramProjectiveDifferential k F m ≫
      diagramVectorCoverMap k ((diagramSyzygyIterate k m).obj F) = 0 := by
  simp only [diagramProjectiveDifferential, Category.assoc, kernel.condition, comp_zero]

@[reassoc (attr := simp)]
theorem diagramProjectiveDifferential_sq (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    diagramProjectiveDifferential k F (m+1) ≫ diagramProjectiveDifferential k F m = 0 := by
  simp only [diagramProjectiveDifferential, Category.assoc,
    kernel.condition_assoc, zero_comp, comp_zero]

/-- Exactness at every projective cover is inherited from the actual
kernel sequence by its explicit epimorphic presentation. -/
theorem diagramProjectiveDifferential_exact_cover (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    (ShortComplex.mk (diagramProjectiveDifferential k F m)
      (diagramVectorCoverMap k ((diagramSyzygyIterate k m).obj F))
      (diagramProjectiveDifferential_cover k F m)).Exact := by
  let ρ := diagramVectorCoverMap k ((diagramSyzygyIterate k m).obj F)
  let α : ShortComplex.mk (diagramProjectiveDifferential k F m) ρ
      (diagramProjectiveDifferential_cover k F m) ⟶ ShortComplex.kernelSequence ρ :=
    { τ₁ := diagramVectorCoverMap k ((diagramSyzygyIterate k (m+1)).obj F)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp only [Category.comp_id, Category.id_comp]; rfl
      comm₂₃ := by simp only [Category.comp_id, Category.id_comp]; rfl }
  letI : Epi α.τ₁ := show Epi
    (diagramVectorCoverMap k ((diagramSyzygyIterate k (m+1)).obj F)) from inferInstance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mpr
    (ShortComplex.kernelSequence_exact ρ)

/-- The actual chain complex, before imposing any finite grade bound. -/
def diagramProjectiveComplex (F : C ⥤ ModuleCat.{u} k) :
    ChainComplex (C ⥤ ModuleCat.{u} k) ℕ :=
  ChainComplex.of (diagramProjectiveTerm k F) (diagramProjectiveDifferential k F)
    (diagramProjectiveDifferential_sq k F)

/-- The explicit resolution is exact at every positive degree. -/
theorem diagramProjectiveComplex_exactAt_succ (F : C ⥤ ModuleCat.{u} k) (m : ℕ) :
    (diagramProjectiveComplex k F).ExactAt (m+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (m+1+1) (m+1) m (by simp) (by simp)]
  dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    diagramProjectiveComplex, ChainComplex.of]
  simp only [ChainComplex.of_d]
  change (ShortComplex.mk (diagramProjectiveDifferential k F (m+1))
    (diagramProjectiveDifferential k F m) (diagramProjectiveDifferential_sq k F m)).Exact
  let α :
      ShortComplex.mk (diagramProjectiveDifferential k F (m+1))
        (diagramVectorCoverMap k ((diagramSyzygyIterate k (m+1)).obj F))
        (diagramProjectiveDifferential_cover k F (m+1)) ⟶
      ShortComplex.mk (diagramProjectiveDifferential k F (m+1))
        (diagramProjectiveDifferential k F m) (diagramProjectiveDifferential_sq k F m) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (diagramVectorCoverMap k ((diagramSyzygyIterate k m).obj F))
      comm₁₂ := by simp only [Category.comp_id, Category.id_comp]
      comm₂₃ := by simp only [Category.id_comp]; rfl }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp
    (diagramProjectiveDifferential_exact_cover k F (m+1))

/-- The genuine chain augmentation to the original diagram. -/
def diagramProjectiveAugmentation (F : C ⥤ ModuleCat.{u} k) :
    diagramProjectiveComplex k F ⟶ (ChainComplex.single₀ (C ⥤ ModuleCat.{u} k)).obj F :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨diagramVectorCoverMap k F, diagramProjectiveDifferential_cover k F 0⟩

/-- The augmentation is an actual quasi-isomorphism. The degree-zero
proof uses the cokernel of the explicit kernel presentation; positive
degrees use the exactness just proved. -/
instance diagramProjectiveAugmentation_quasiIso (F : C ⥤ ModuleCat.{u} k) :
    QuasiIso (diagramProjectiveAugmentation k F) := by
  refine ⟨fun m => ?_⟩
  cases m with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp [diagramProjectiveAugmentation]
      refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨diagramProjectiveDifferential_exact_cover k F 0, by infer_instance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
          exact (ChainComplex.of_d (diagramProjectiveTerm k F)
            (diagramProjectiveDifferential k F) 0).symm) (by simp)
    all_goals rfl
  | succ m =>
    rw [quasiIsoAt_iff_exactAt']
    · exact diagramProjectiveComplex_exactAt_succ k F m
    · apply ChainComplex.exactAt_succ_single_obj

/-- A literal projective resolution, not an abstract existence claim. -/
def diagramProjectiveResolution (F : C ⥤ ModuleCat.{u} k) : ProjectiveResolution F where
  complex := diagramProjectiveComplex k F
  projective m := diagramProjectiveTerm_projective k F m
  π := diagramProjectiveAugmentation k F

section Direct

variable (grade : C → ℕ)
  (grade_le : ∀ {c d : C} (_ : c ⟶ d), grade c ≤ grade d)
  (eq_of_grade_eq : ∀ {c d : C} (_ : c ⟶ d), grade c = grade d → c = d)
  [∀ c : C, Subsingleton (c ⟶ c)]

include grade_le eq_of_grade_eq

/-- The `m`-th actual syzygy vanishes in all dimensions below `m`. -/
theorem diagramSyzygyIterate_support (F : C ⥤ ModuleCat.{u} k) (m : ℕ)
    (c : C) (hc : grade c < m) :
    IsZero (((diagramSyzygyIterate k m).obj F).obj c) := by
  induction m generalizing c with
  | zero => exact (Nat.not_lt_zero _ hc).elim
  | succ m ih =>
    exact diagramVectorCoverKernel_support_drop k grade grade_le eq_of_grade_eq
      ((diagramSyzygyIterate k m).obj F) m (fun c hc => ih c hc) c
      (Nat.le_of_lt_succ hc)

/-- A genuine bound on the dimensions of the entire category terminates
the resolution. This is not a truncation hypothesis on the input diagram. -/
theorem diagramSyzygyIterate_isZero (F : C ⥤ ModuleCat.{u} k) (N : ℕ)
    (hbound : ∀ c : C, grade c ≤ N) :
    IsZero ((diagramSyzygyIterate k (N+1)).obj F) := by
  apply Functor.isZero
  intro c
  exact diagramSyzygyIterate_support k grade grade_le eq_of_grade_eq F (N+1) c
    (Nat.lt_succ_of_le (hbound c))

/-- The actual projective resolution has no nonzero terms above the
largest cell dimension. Nothing is cut out of its construction. -/
theorem diagramProjectiveComplex_isZero_above (F : C ⥤ ModuleCat.{u} k) (N m : ℕ)
    (hbound : ∀ c : C, grade c ≤ N) (hm : N < m) :
    IsZero ((diagramProjectiveComplex k F).X m) := by
  apply (diagramVectorCover k).map_isZero
  apply Functor.isZero
  intro c
  exact diagramSyzygyIterate_support k grade grade_le eq_of_grade_eq F m c
    (lt_of_le_of_lt (hbound c) hm)

end Direct

end ToricPower.Cellular

end
