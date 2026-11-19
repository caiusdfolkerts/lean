module

public import ToricPower.CoherentFoundations

/-!
# Quasi-isomorphisms of module sheaves are local on an actual open cover

Restriction to an open subscheme has both adjoints. It therefore preserves
kernels and cokernels, and the canonical comparison with scheme pullback
makes pullback along an open immersion exact. Isomorphisms are detected on
an open cover by the sheaf condition; the statement for homology follows
from the natural homology comparison for exact functors.

The cover in the final theorem is an actual `Scheme.OpenCover`, and its
functors are the actual `Scheme.Modules.pullback` functors. No hypothesis
asserting exactness, joint conservativity, or a local-to-global principle
is added. The complex shape and indexing type are arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- The homology comparison of an exact functor identifies the image of
the original homology map with the homology map of the image complex. -/
theorem isIso_map_homologyMap_of_quasiIso_map
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {S T : ShortComplex C} (f : S ⟶ T)
    (hf : QuasiIso (F.mapShortComplex.map f)) :
    IsIso (F.map (homologyMap f)) := by
  change IsIso ((homologyFunctor C ⋙ F).map f)
  apply (NatIso.isIso_map_iff (homologyFunctorIso F) f).mp
  exact (quasiIso_iff (F.mapShortComplex.map f)).mp hf

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    {ι : Type*} {c : ComplexShape ι}

/-- Exact functors identify mapped homology isomorphisms with the
quasi-isomorphism condition in the corresponding degree. -/
theorem isIso_map_homologyMap_of_quasiIsoAt_map
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι)
    (hf : QuasiIsoAt ((F.mapHomologicalComplex c).map f) i) :
    IsIso (F.map (homologyMap f i)) := by
  exact ShortComplex.isIso_map_homologyMap_of_quasiIso_map F
    ((shortComplexFunctor C c i).map f)
    ((quasiIsoAt_iff ((F.mapHomologicalComplex c).map f) i).mp hf)

end HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules

universe u v w

variable {X Y : Scheme.{u}}

/-- Pullback along an open immersion preserves finite limits. Restriction
has a left adjoint by the actual sheaf pullback construction, and the
restriction--pullback comparison transports this property. -/
instance pullbackPreservesFiniteLimitsOfIsOpenImmersion
    (j : Y ⟶ X) [IsOpenImmersion j] : PreservesFiniteLimits (pullback j) :=
  preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback j)

/-- Actual pullback along an open immersion preserves homology. Finite
colimits are preserved by its usual pullback--pushforward adjunction. -/
instance pullbackPreservesHomologyOfIsOpenImmersion
    (j : Y ⟶ X) [IsOpenImmersion j] : (pullback j).PreservesHomology :=
  Functor.preservesHomologyOfExact (pullback j)

/-- An isomorphism after pullback to an open-immersion chart is an
isomorphism after pullback to its literal open image. The two charts are
related by the actual `isoOpensRange`, including its inverse. -/
theorem isIso_pullback_opensRange_of_isIso
    (j : Y ⟶ X) [IsOpenImmersion j] {M N : X.Modules} (f : M ⟶ N)
    (hf : IsIso ((pullback j).map f)) :
    IsIso ((pullback j.opensRange.ι).map f) := by
  letI := hf
  let comparison : pullback j ⋙ pullback j.isoOpensRange.inv ≅
      pullback j.opensRange.ι :=
    pullbackComp j.isoOpensRange.inv j ≪≫ pullbackCongr j.isoOpensRange_inv_comp
  apply (NatIso.isIso_map_iff comparison f).mp
  change IsIso ((pullback j.isoOpensRange.inv).map ((pullback j).map f))
  infer_instance

/-- The pullback functors of an actual scheme open cover jointly reflect
isomorphisms of module sheaves. This uses the actual sheaf-local criterion
on the open images of the charts. -/
theorem isIso_iff_pullback_openCover
    (cover : Scheme.OpenCover.{v} X) {M N : X.Modules} (f : M ⟶ N) :
    IsIso f ↔ ∀ i, IsIso ((pullback (cover.f i)).map f) := by
  refine ⟨fun _ _ => inferInstance, fun hf => ?_⟩
  apply (isIso_iff_of_isOpenCover cover.isOpenCover_opensRange f).mpr
  intro i
  exact isIso_pullback_opensRange_of_isIso (cover.f i) f (hf i)

/-- The pullback functors of an actual scheme open cover jointly detect
the zero object, without any quasicoherence or finiteness hypothesis. -/
theorem isZero_iff_pullback_openCover
    (cover : Scheme.OpenCover.{v} X) (M : X.Modules) :
    IsZero M ↔ ∀ i, IsZero ((pullback (cover.f i)).obj M) := by
  refine ⟨fun hM i => (pullback (cover.f i)).map_isZero hM, fun hM => ?_⟩
  have hzero : IsIso (0 : M ⟶ M) :=
    (isIso_iff_pullback_openCover cover (0 : M ⟶ M)).mpr (fun i => by
      rw [Functor.map_zero]
      exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hM i, hM i⟩)
  exact ((isIsoZero_iff_source_target_isZero M M).mp hzero).1

variable {ι : Type w} {c : ComplexShape ι}

/-- A degreewise homology isomorphism is detected after actual pullback
to every member of an arbitrary scheme open cover. -/
theorem quasiIsoAt_iff_pullback_openCover
    (cover : Scheme.OpenCover.{v} X)
    {K L : HomologicalComplex X.Modules c} (f : K ⟶ L) (degree : ι) :
    QuasiIsoAt f degree ↔ ∀ i,
      QuasiIsoAt
        (((pullback (cover.f i)).mapHomologicalComplex c).map f) degree := by
  refine ⟨fun _ _ => inferInstance, fun hf => ?_⟩
  apply (quasiIsoAt_iff_isIso_homologyMap f degree).mpr
  apply (isIso_iff_pullback_openCover cover (HomologicalComplex.homologyMap f degree)).mpr
  intro i
  exact HomologicalComplex.isIso_map_homologyMap_of_quasiIsoAt_map
    (pullback (cover.f i)) f degree (hf i)

/-- **Actual local-to-global quasi-isomorphism criterion.** A map of
complexes of module sheaves is a quasi-isomorphism if and only if its
actual scheme pullback to each open-cover chart is a quasi-isomorphism.
It applies in particular to unbounded complexes and to chain complexes
indexed by `ℕ`; no boundedness assumption occurs. -/
theorem quasiIso_iff_pullback_openCover
    (cover : Scheme.OpenCover.{v} X)
    {K L : HomologicalComplex X.Modules c} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ i,
      QuasiIso
        (((pullback (cover.f i)).mapHomologicalComplex c).map f) := by
  refine ⟨fun _ _ => inferInstance, fun hf => ?_⟩
  apply (quasiIso_iff f).mpr
  intro degree
  apply (quasiIsoAt_iff_pullback_openCover cover f degree).mpr
  intro i
  letI := hf i
  infer_instance

/-- The implication used when gluing an affine computation of an
augmentation to a global resolution of a module sheaf. -/
theorem quasiIso_of_pullback_openCover
    (cover : Scheme.OpenCover.{v} X)
    {K L : HomologicalComplex X.Modules c} (f : K ⟶ L)
    (hf : ∀ i, QuasiIso
      (((pullback (cover.f i)).mapHomologicalComplex c).map f)) :
    QuasiIso f :=
  (quasiIso_iff_pullback_openCover cover f).mpr hf

end AlgebraicGeometry.Scheme.Modules

end
