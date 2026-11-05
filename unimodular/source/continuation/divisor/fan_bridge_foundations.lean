module

public import Unimodular.FanMaximalCones
public import Unimodular.RayHyperplanes
public import Mathlib.LinearAlgebra.Basis.Submodule
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face
public import Unimodular

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Exact recovered full-cone and quotient-fan foundations. See adjacent manifest. -/

section Source_StarQuotients



@[expose] public section

open scoped Pointwise Topology BigOperators
open Filter Set TauCeti.Toric

namespace Unimodular.StarQuotients

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {F C D G : PointedCone ℝ V} (p : V →ₗ[ℝ] W)
  (hker : LinearMap.ker p = Submodule.span ℝ (F : Set V))

include hker in
/-- Equality after projection means that the difference is in the face span. -/
theorem sub_mem_span_of_map_eq {x y : V} (h : p x = p y) :
    x - y ∈ Submodule.span ℝ (F : Set V) := by
  rw [← hker]
  change p (x - y) = 0
  rw [map_sub, h, sub_self]

include hker in
theorem map_eq_zero_of_mem {x : V} (hx : x ∈ F) : p x = 0 := by
  have hm : x ∈ LinearMap.ker p := by
    rw [hker]
    exact Submodule.subset_span hx
  exact hm

include hker in
/-- A face above the contracted face is saturated for projection inside its ambient cone. -/
theorem mem_face_of_map_eq (hG : G.IsFaceOf C) (hFG : F ≤ G) {x y : V}
    (hx : x ∈ C) (hy : y ∈ G) (he : p x = p y) : x ∈ G := by
  obtain ⟨a, ha, b, hb, hab⟩ := PointedCone.mem_span.1 (sub_mem_span_of_map_eq p hker he)
  have hxby : x + b = y + a := by
    have h := congrArg (fun z : V => z + (y + b)) hab
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  apply hG.mem_of_add_mem_left hx (hG.le (hFG hb))
  rw [hxby]
  exact G.add_mem hy (hFG ha)

include hker in
theorem map_isFaceOf (hG : G.IsFaceOf C) (hFG : F ≤ G) :
    (G.map p).IsFaceOf (C.map p) := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hG.le hx, rfl⟩
  · intro x y hx hy hxy
    obtain ⟨a, ha, rfl⟩ := PointedCone.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := PointedCone.mem_map.1 hy
    obtain ⟨g, hg, he⟩ := PointedCone.mem_map.1 hxy
    have hab : a + b ∈ G := mem_face_of_map_eq p hker hG hFG
      (C.add_mem ha hb) hg (by simpa only [map_add] using he.symm)
    exact ⟨a, hG.mem_of_add_mem_left ha hb hab, rfl⟩

include hker in
/-- Projection by the span of a face gives a genuinely salient cone. -/
theorem map_salient (hF : F.IsFaceOf C) : (C.map p : ConvexCone ℝ W).Salient := by
  intro y hy hy0 hny
  obtain ⟨x, hx, rfl⟩ := PointedCone.mem_map.1 hy
  obtain ⟨z, hz, hzx⟩ := PointedCone.mem_map.1 hny
  have hsum : p (x + z) = 0 := by rw [map_add, hzx, add_neg_cancel]
  have hspan : x + z ∈ Submodule.span ℝ (F : Set V) := by
    rw [← hker]
    exact hsum
  have hxF : x ∈ F := by
    apply hF.mem_of_add_mem_left hx hz
    rw [← QuotientFaces.inf_span_eq hF]
    exact ⟨C.add_mem hx hz, hspan⟩
  exact hy0 (map_eq_zero_of_mem p hker hxF)

include hker in
/-- Images of cones sharing the contracted face commute with their actual intersection. -/
theorem map_inf (hFC : F ≤ C) (hFD : F ≤ D) :
    (C ⊓ D).map p = C.map p ⊓ D.map p := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · rintro y ⟨hx, hy⟩
    obtain ⟨x, hx, hxy⟩ := PointedCone.mem_map.1 hx
    obtain ⟨z, hz, hzy⟩ := PointedCone.mem_map.1 hy
    obtain ⟨a, ha, b, hb, hab⟩ := PointedCone.mem_span.1
      (sub_mem_span_of_map_eq p hker (hxy.trans hzy.symm))
    have he : x + b = z + a := by
      have h := congrArg (fun t : V => t + (z + b)) hab
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    refine ⟨x + b, ⟨C.add_mem hx (hFC hb), ?_⟩, ?_⟩
    · rw [he]
      exact D.add_mem hz (hFD ha)
    · change p (x + b) = y
      rw [map_add, map_eq_zero_of_mem p hker hb, add_zero, hxy]

def pullback (C : PointedCone ℝ V) (H : PointedCone ℝ W) : PointedCone ℝ V :=
  C ⊓ H.comap p

theorem pullback_isFaceOf {H : PointedCone ℝ W} (hH : H.IsFaceOf (C.map p)) :
    (pullback p C H).IsFaceOf C := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left inf_le_left
  intro x y hx hy hxy
  refine ⟨hx, ?_⟩
  apply hH.mem_of_add_mem_left ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  have h : p (x + y) ∈ H := hxy.2
  change p x + p y ∈ H
  simpa only [map_add] using h

include hker in
theorem le_pullback (hFC : F ≤ C) (H : PointedCone ℝ W) : F ≤ pullback p C H := by
  intro x hx
  refine ⟨hFC hx, ?_⟩
  change p x ∈ H
  rw [map_eq_zero_of_mem p hker hx]
  exact H.zero_mem

theorem map_pullback {H : PointedCone ℝ W} (hH : H ≤ C.map p) :
    (pullback p C H).map p = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := PointedCone.mem_map.1 (hH hx)
    exact ⟨y, ⟨hy, hx⟩, rfl⟩

section Fans

variable {N N' : Type*} [AddCommGroup N] [AddCommGroup N']
  {ι : N →+ V} {ι' : N' →+ W} (Φ : Fan ι)
  (q : N →+ N') (hq : ∀ n, p (ι n) = ι' (q n)) (hι' : IsIntegralLattice ι')
  (F) (hF : F ∈ Φ.cones)

/-- The quotient star as an actual finite rational salient fan. The target map is a
specified integral quotient lattice; the kernel condition says exactly which face is contracted. -/
def starFan : Fan ι' where
  lattice := hι'
  cones := (fun C => C.map p) '' {C ∈ Φ.cones | F ≤ C}
  finite_cones := (show Set.Finite {C : PointedCone ℝ V | C ∈ Φ.cones ∧ F ≤ C} from
    Φ.finite_cones.subset (fun _ h => h.1)).image (fun C => C.map p)
  isToricCone := by
    rintro _ ⟨C, ⟨hC, hFC⟩, rfl⟩
    exact ⟨(Φ.isToricCone hC).rational.map hq,
      map_salient p hker (Φ.isFaceOf_of_le hC hF hFC)⟩
  mem_of_isFaceOf := by
    rintro _ H ⟨C, ⟨hC, hFC⟩, rfl⟩ hH
    refine ⟨pullback p C H, ⟨Φ.mem_of_isFaceOf hC (pullback_isFaceOf p hH),
      le_pullback p hker hFC H⟩, map_pullback p hH.le⟩
  inf_isFaceOf_left := by
    rintro _ _ ⟨C, ⟨hC, hFC⟩, rfl⟩ ⟨D, ⟨hD, hFD⟩, rfl⟩
    rw [← map_inf p hker hFC hFD]
    exact map_isFaceOf p hker (Φ.inf_isFaceOf_left hC hD) (le_inf hFC hFD)

@[simp] theorem mem_starFan_cones (H : PointedCone ℝ W) :
    H ∈ (starFan (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hq) (hι' := hι') (F := F) (hF := hF)).cones ↔
      ∃ C ∈ Φ.cones, F ≤ C ∧ C.map p = H := by
  constructor
  · rintro ⟨C, ⟨hC, hFC⟩, he⟩
    exact ⟨C, hC, hFC, he⟩
  · rintro ⟨C, hC, hFC, he⟩
    exact ⟨C, ⟨hC, hFC⟩, he⟩

end Fans

section Completeness

variable {N : Type*} [AddCommGroup N] {ι : N →+ V} (Φ : Fan ι)

/-- The original star covers a neighborhood of a relative-interior point of any fan cone. -/
theorem star_mem_nhds (hΦ : Φ.IsComplete) (F : PointedCone ℝ V) (hF : F ∈ Φ.cones) :
    ∃ x ∈ F, {y | ∃ C ∈ Φ.cones, F ≤ C ∧ y ∈ C} ∈ 𝓝 x := by
  classical
  obtain ⟨x, hxF, hdetect⟩ := FanProducts.exists_face_detecting_point F (Φ.isToricCone hF).fg
  have hnear : ∀ C : Φ.cones, ∀ᶠ y in 𝓝 x, y ∈ C.1 → F ≤ C.1 := by
    intro C
    by_cases hFC : F ≤ C.1
    · exact Eventually.of_forall (fun _ _ => hFC)
    have hxnot : x ∉ C.1 := by
      intro hxC
      exact hFC ((hdetect _ (Φ.inf_isFaceOf_left hF C.2) ⟨hxF, hxC⟩).trans inf_le_right)
    have hopen := (ConeInterior.isClosed_of_fg (Φ.isToricCone C.2).fg).isOpen_compl
    filter_upwards [hopen.mem_nhds hxnot] with y hy hyC
    exact (hy hyC).elim
  refine ⟨x, hxF, ?_⟩
  filter_upwards [Filter.eventually_all.2 hnear] with y hy
  obtain ⟨C, hC, hyC⟩ := Φ.isComplete_iff.1 hΦ y
  exact ⟨C, hC, hy ⟨C, hC⟩ hyC, hyC⟩

variable {N' : Type*} [AddCommGroup N'] {ι' : N' →+ W}
  (q : N →+ N') (hq : ∀ n, p (ι n) = ι' (q n)) (hι' : IsIntegralLattice ι')
  (F) (hF : F ∈ Φ.cones)

/-- Quotient stars of complete fans are complete, for every face and every compatible
surjective quotient presentation with exactly that face span as kernel. -/
theorem starFan_complete (hΦ : Φ.IsComplete) (hp : Function.Surjective p) :
    (starFan (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hq) (hι' := hι') (F := F) (hF := hF)).IsComplete := by
  apply (Fan.isComplete_iff _).2
  intro z
  obtain ⟨v, rfl⟩ := hp z
  obtain ⟨x, hxF, hstar⟩ := star_mem_nhds Φ hΦ F hF
  have hcont : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hlim : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using hcont.tendsto (0 : ℝ)
  have he := (hlim.eventually hstar).filter_mono
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, C, hC, hFC, hxC⟩ := (hpos.and he).exists
  refine ⟨C.map p, (mem_starFan_cones (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hq) (hι' := hι') (F := F) (hF := hF) _).2
    ⟨C, hC, hFC, rfl⟩, ?_⟩
  have hm : p (x + t • v) ∈ C.map p := ⟨x + t • v, hxC, rfl⟩
  have hscale := PointedCone.smul_mem (C.map p) (inv_nonneg.2 ht.le) hm
  simpa only [map_add, map_smul, map_eq_zero_of_mem p hker hxF, zero_add,
    smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hscale

end Completeness
end Unimodular.StarQuotients
end
end Source_StarQuotients

section Source_CoordinateQuotients



@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.CoordinateQuotients

section Algebra

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype I] [DecidableEq I] (b : Module.Basis I R M) (A : Finset I)

/-- Delete precisely the basis coordinates in A. -/
noncomputable def projection : M →ₗ[R] ({i : I // i ∉ A} → R) :=
  LinearMap.pi (fun i => b.coord i.1)

@[simp] theorem projection_apply (x : M) (i : {i : I // i ∉ A}) :
    projection b A x i = b.repr x i.1 := rfl

/-- The kernel is the actual integral or real span of the deleted basis vectors. -/
theorem ker_projection : LinearMap.ker (projection b A) =
    Submodule.span R (b '' (A : Set I)) := by
  ext x
  rw [LinearMap.mem_ker, b.mem_span_image]
  constructor
  · intro hx i hi
    by_contra hiA
    have hz := congrFun hx ⟨i, hiA⟩
    exact (Finsupp.mem_support_iff.1 hi) hz
  · intro hx
    funext i
    by_contra hn
    exact i.2 (hx (Finsupp.mem_support_iff.2 hn))

theorem projection_surjective : Function.Surjective (projection b A) := by
  intro z
  let t : I → R := fun i => if h : i ∈ A then 0 else z ⟨i, h⟩
  refine ⟨b.equivFun.symm t, ?_⟩
  funext i
  change b.repr (b.equivFun.symm t) i.1 = z i
  rw [← Module.Basis.equivFun_apply, b.equivFun.apply_symm_apply]
  simp [t, i.2]

/-- The coordinate quotient is the actual module quotient by that kernel. -/
noncomputable def quotientEquiv :
    (M ⧸ Submodule.span R (b '' (A : Set I))) ≃ₗ[R] ({i : I // i ∉ A} → R) :=
  (Submodule.quotEquivOfEq _ _ (ker_projection b A).symm).trans
    ((projection b A).quotKerEquivOfSurjective (projection_surjective b A))

@[simp] theorem quotientEquiv_mk (x : M) :
    quotientEquiv b A (Submodule.Quotient.mk x) = projection b A x := by
  simp [quotientEquiv]

variable {M' : Type*} [AddCommGroup M'] [Module R M']
  (q : M →ₗ[R] M') (hq : Function.Surjective q)
  (hker : LinearMap.ker q = Submodule.span R (b '' (A : Set I)))

/-- Any surjection with this precise kernel has the same free quotient coordinates. -/
noncomputable def quotientImageEquiv : ({i : I // i ∉ A} → R) ≃ₗ[R] M' :=
  (quotientEquiv b A).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (q.quotKerEquivOfSurjective hq))

@[simp] theorem quotientImageEquiv_projection (x : M) :
    quotientImageEquiv b A q hq hker (projection b A x) = q x := by
  have hx : (quotientEquiv b A).symm (projection b A x) = Submodule.Quotient.mk x := by
    apply (quotientEquiv b A).injective
    simp
  simp only [quotientImageEquiv, LinearEquiv.trans_apply, hx]
  simp

/-- The surviving images of a basis form an integral basis of the quotient, not just a
real basis or a spanning finite-index sublattice. -/
noncomputable def imageBasis : Module.Basis {i : I // i ∉ A} R M' :=
  (Pi.basisFun R {i : I // i ∉ A}).map (quotientImageEquiv b A q hq hker)

@[simp] theorem imageBasis_apply (i : {i : I // i ∉ A}) :
    imageBasis b A q hq hker i = q (b i.1) := by
  rw [imageBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  have he : projection b A (b i.1) = Pi.single i 1 := by
    funext j
    by_cases hij : i = j
    · subst j
      simp [projection_apply]
    · have hv : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      simp [projection_apply, Module.Basis.repr_self_apply, Pi.single_apply, hij, hv, Ne.symm hij, Ne.symm hv]
  rw [← he, quotientImageEquiv_projection]

/-- Quotient coordinates are precisely the undeleted original coordinates. -/
@[simp] theorem imageBasis_repr (x : M) (i : {i : I // i ∉ A}) :
    (imageBasis b A q hq hker).repr (q x) i = b.repr x i.1 := by
  have hx : (quotientImageEquiv b A q hq hker).symm (q x) = projection b A x := by
    apply (quotientImageEquiv b A q hq hker).injective
    simp
  change (Pi.basisFun R {i : I // i ∉ A}).repr
    ((quotientImageEquiv b A q hq hker).symm (q x)) i = _
  rw [hx, Pi.basisFun_repr]
  rfl

end Algebra

section Lattices

variable {N V I : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype I] [DecidableEq I] (ι : N →+ V) (hι : IsIntegralLattice ι)
  (b : Module.Basis I ℤ N) (A : Finset I)

noncomputable def realBasis : Module.Basis I ℝ V := hι.isBaseChange.basis b

@[simp] theorem realBasis_apply (i : I) : realBasis ι hι b i = ι (b i) :=
  hι.isBaseChange.basis_apply b i

@[simp] theorem realBasis_repr (n : N) (i : I) :
    (realBasis ι hι b).repr (ι n) i = (b.repr n i : ℝ) :=
  hι.isBaseChange.basis_repr_comp_apply b n i

/-- The quotient lattice map, expressed in the surviving basis coordinates. -/
def quotientEmbedding : ({i : I // i ∉ A} → ℤ) →+ ({i : I // i ∉ A} → ℝ) :=
  (Int.castAddHom ℝ).compLeft {i : I // i ∉ A}

theorem quotientEmbedding_isIntegralLattice : IsIntegralLattice (quotientEmbedding A) := by
  apply isIntegralLattice_of_basis (Pi.basisFun ℤ {i : I // i ∉ A})
    (Pi.basisFun ℝ {i : I // i ∉ A})
  intro i
  ext j
  simp [quotientEmbedding, Pi.basisFun_apply, Pi.single_apply]

theorem projections_compatible (n : N) :
    projection (realBasis ι hι b) A (ι n) = quotientEmbedding A (projection b A n) := by
  funext i
  exact realBasis_repr ι hι b n i.1

/-- The face cone generated by exactly the indicated subset of an integral basis. -/
noncomputable def faceCone : PointedCone ℝ V :=
  PointedCone.hull ℝ ((realBasis ι hι b) '' (A : Set I))

theorem real_kernel_eq_face_span :
    LinearMap.ker (projection (realBasis ι hι b) A) =
      Submodule.span ℝ (faceCone ι hι b A : Set V) := by
  rw [ker_projection, faceCone, RayHyperplanes.span_hull_eq]

/-- The integral kernel is exactly N intersected with the contracted real span.
This rules out replacing the quotient lattice by a finite-index sublattice. -/
theorem integer_kernel_iff_real_span (n : N) :
    n ∈ Submodule.span ℤ (b '' (A : Set I)) ↔
      ι n ∈ Submodule.span ℝ (faceCone ι hι b A : Set V) := by
  rw [← ker_projection b A, ← real_kernel_eq_face_span ι hι b A,
    LinearMap.mem_ker, LinearMap.mem_ker, projections_compatible ι hι b A]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    apply (quotientEmbedding_isIntegralLattice A).injective
    simpa using h

/-- The quotient star in the actual quotient lattice, presented by its surviving coordinates. -/
noncomputable def starFan (Φ : Fan ι) (hF : faceCone ι hι b A ∈ Φ.cones) :
    Fan (quotientEmbedding A) :=
  StarQuotients.starFan (p := projection (realBasis ι hι b) A)
    (hker := real_kernel_eq_face_span ι hι b A) (Φ := Φ) (q := (projection b A).toAddMonoidHom)
    (hq := projections_compatible ι hι b A) (hι' := quotientEmbedding_isIntegralLattice A)
    (F := faceCone ι hι b A) (hF := hF)

theorem starFan_complete (Φ : Fan ι) (hF : faceCone ι hι b A ∈ Φ.cones)
    (hΦ : Φ.IsComplete) : (starFan ι hι b A Φ hF).IsComplete :=
  StarQuotients.starFan_complete (p := projection (realBasis ι hι b) A)
    (hker := real_kernel_eq_face_span ι hι b A) (Φ := Φ) (q := (projection b A).toAddMonoidHom)
    (hq := projections_compatible ι hι b A) (hι' := quotientEmbedding_isIntegralLattice A)
    (F := faceCone ι hι b A) (hF := hF) hΦ (projection_surjective _ _)

end Lattices
end Unimodular.CoordinateQuotients
end
end Source_CoordinateQuotients

section Source_RegularQuotients



@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.RegularQuotients

attribute [local instance] Classical.propDecidable

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W]
  {ι : N →+ V} {ι' : N' →+ W}

/-- A regular cone is the cone of an actual subset of any extending integral basis. -/
theorem hull_basis_indices (hι : IsIntegralLattice ι) {C : PointedCone ℝ V}
    (hC : IsToricCone ι C) {n : ℕ} (b : Module.Basis (Fin n) ℤ N)
    (r : ToricRay C ↪ Fin n) (hb : IsExtendingBasis ι b r) :
    ∃ A : Finset (Fin n),
      (∀ i, i ∈ A ↔ ∃ ρ, r ρ = i) ∧ C = PointedCone.hull ℝ (ι '' (b '' (A : Set (Fin n)))) := by
  classical
  letI := ToricRay.finite_of_fg hC.fg
  letI : Fintype (ToricRay C) := Fintype.ofFinite _
  let A := Finset.univ.image r
  have hA : ∀ i, i ∈ A ↔ ∃ ρ, r ρ = i := by simp [A]
  refine ⟨A, hA, ?_⟩
  rw [← hC.hull_primitiveGenerator hι]
  congr 1
  ext x
  constructor
  · rintro ⟨v, ⟨ρ, rfl⟩, rfl⟩
    refine ⟨b (r ρ), ⟨r ρ, (hA _).2 ⟨ρ, rfl⟩, rfl⟩, ?_⟩
    rw [(hb.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator hι hC]
  · rintro ⟨v, ⟨i, hi, rfl⟩, rfl⟩
    obtain ⟨ρ, rfl⟩ := (hA i).1 hi
    refine ⟨primitiveGenerator hι hC ρ, ⟨ρ, rfl⟩, ?_⟩
    rw [(hb.isPrimitiveGenerator_apply ρ).eq_primitiveGenerator hι hC]

/-- A face and its regular supercone are presented by nested subsets of one integral basis. -/
theorem exists_basis_face_sets (hι : IsIntegralLattice ι) {F C : PointedCone ℝ V}
    (hC : IsRegularCone ι C) (hFC : F.IsFaceOf C) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (A B : Finset (Fin n)),
      A ⊆ B ∧ F = PointedCone.hull ℝ (ι '' (b '' (A : Set (Fin n)))) ∧
      C = PointedCone.hull ℝ (ι '' (b '' (B : Set (Fin n)))) := by
  obtain ⟨n, b, r, hb⟩ := hC.exists_basis
  let rF := (ToricRay.faceEmbedding hFC).trans r
  have hbF : IsExtendingBasis ι b rF := ⟨fun ρ =>
    (isPrimitiveGenerator_faceEmbedding hFC ρ).1
      (hb.isPrimitiveGenerator_apply (ToricRay.faceEmbedding hFC ρ))⟩
  obtain ⟨A, hA, heF⟩ := hull_basis_indices hι (hC.toIsToricCone.of_isFaceOf hFC) b rF hbF
  obtain ⟨B, hB, heC⟩ := hull_basis_indices hι hC.toIsToricCone b r hb
  refine ⟨n, b, A, B, ?_, heF, heC⟩
  intro i hi
  obtain ⟨ρ, rfl⟩ := (hA i).1 hi
  exact (hB _).2 ⟨ToricRay.faceEmbedding hFC ρ, rfl⟩

/-- In the span of a subset of an integral basis, real membership and integral membership
coincide for integral vectors. This proves saturation, instead of assuming it. -/
theorem mem_integer_span_iff (hι : IsIntegralLattice ι) {I : Type*}
    [Fintype I] [DecidableEq I] (b : Module.Basis I ℤ N) (A : Finset I) (x : N) :
    x ∈ Submodule.span ℤ (b '' (A : Set I)) ↔
      ι x ∈ Submodule.span ℝ (ι '' (b '' (A : Set I))) := by
  have he : ι '' (b '' (A : Set I)) =
      CoordinateQuotients.realBasis ι hι b '' (A : Set I) := by
    rw [Set.image_image]
    congr 1
    funext i
    exact (CoordinateQuotients.realBasis_apply ι hι b i).symm
  rw [he, b.mem_span_image, (CoordinateQuotients.realBasis ι hι b).mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    CoordinateQuotients.realBasis_repr, Int.cast_ne_zero]

/-- Quotients of regular cones by spans of their faces are regular in the exact quotient
lattice. Surjectivity of q excludes a finite-index replacement of that lattice. -/
theorem map_isRegularCone (hι : IsIntegralLattice ι) (hι' : IsIntegralLattice ι')
    (p : V →ₗ[ℝ] W) (q : N →+ N') (hq : Function.Surjective q)
    (hcompat : ∀ n, p (ι n) = ι' (q n)) {F C : PointedCone ℝ V}
    (hker : LinearMap.ker p = Submodule.span ℝ (F : Set V))
    (hC : IsRegularCone ι C) (hFC : F.IsFaceOf C) : IsRegularCone ι' (C.map p) := by
  classical
  obtain ⟨n, b, A, B, hAB, heF, heC⟩ := exists_basis_face_sets hι hC hFC
  have hki : LinearMap.ker q.toIntLinearMap = Submodule.span ℤ (b '' (A : Set (Fin n))) := by
    ext x
    rw [LinearMap.mem_ker, mem_integer_span_iff hι b A]
    have hspan : Submodule.span ℝ (F : Set V) =
        Submodule.span ℝ (ι '' (b '' (A : Set (Fin n)))) := by
      rw [heF, RayHyperplanes.span_hull_eq]
    rw [← hspan, ← hker]
    change q x = 0 ↔ p (ι x) = 0
    rw [hcompat x]
    exact ⟨fun hx => by rw [hx, map_zero], fun hx => hι'.injective (by simpa using hx)⟩
  let bQ := CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hki
  let S : Set {i : Fin n // i ∉ A} := {i | i.1 ∈ B}
  let D : PointedCone ℝ W := PointedCone.hull ℝ (ι' '' (bQ '' S))
  have he : C.map p = D := by
    apply le_antisymm
    · have hle : C ≤ D.comap p := by
        rw [heC]
        apply Submodule.span_le.2
        rintro _ ⟨_, ⟨i, hiB, rfl⟩, rfl⟩
        change p (ι (b i)) ∈ D
        rw [hcompat]
        by_cases hiA : i ∈ A
        · have hzero : q (b i) = 0 := by
            change b i ∈ LinearMap.ker q.toIntLinearMap
            rw [hki]
            exact Submodule.subset_span ⟨i, hiA, rfl⟩
          rw [hzero, map_zero]
          exact D.zero_mem
        · have hbQ : bQ ⟨i, hiA⟩ = q (b i) := CoordinateQuotients.imageBasis_apply _ _ _ _ _ _
          rw [← hbQ]
          exact PointedCone.subset_hull ⟨bQ ⟨i, hiA⟩, ⟨⟨i, hiA⟩, hiB, rfl⟩, rfl⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hle hx
    · apply Submodule.span_le.2
      rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      have hbQ : bQ i = q (b i.1) := CoordinateQuotients.imageBasis_apply _ _ _ _ _ _
      rw [hbQ, ← hcompat]
      refine ⟨ι (b i.1), ?_, rfl⟩
      rw [heC]
      exact PointedCone.subset_hull ⟨b i.1, ⟨i.1, hi, rfl⟩, rfl⟩
  rw [he]
  exact isRegularCone_hull_image_basis hι' bQ S

/-- Smoothness of the complete quotient star is proved cone by cone in the quotient lattice. -/
theorem starFan_isRegular (Φ : Fan ι) (hΦ : Φ.IsRegular)
    (p : V →ₗ[ℝ] W) (q : N →+ N') (hq : Function.Surjective q)
    (hcompat : ∀ n, p (ι n) = ι' (q n)) (hι' : IsIntegralLattice ι')
    (F : PointedCone ℝ V) (hF : F ∈ Φ.cones)
    (hker : LinearMap.ker p = Submodule.span ℝ (F : Set V)) :
    (StarQuotients.starFan (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF)).IsRegular := by
  apply Fan.isRegular_iff.2
  intro H hH
  obtain ⟨C, hC, hFC, rfl⟩ := (StarQuotients.mem_starFan_cones (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) H).1 hH
  exact map_isRegularCone Φ.lattice hι' p q hq hcompat hker (Fan.isRegular_iff.1 hΦ C hC)
    (Φ.isFaceOf_of_le hC hF hFC)

end Unimodular.RegularQuotients
end
end Source_RegularQuotients

section Source_ConeBases



@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.ConeBases

attribute [local instance] Classical.propDecidable

variable {N V : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : N →+ V}

/-- The actual real cone generated by an integral basis. -/
noncomputable def cone {I : Type*} (b : Module.Basis I ℤ N) : PointedCone ℝ V :=
  PointedCone.hull ℝ (Set.range (fun i => ι (b i)))

/-- A full regular cone has a basis of the entire lattice as its ray generators. -/
theorem exists_basis_of_full_regular (hι : IsIntegralLattice ι) {C : PointedCone ℝ V}
    (hC : IsRegularCone ι C) (hfull : Submodule.span ℝ (C : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N), C = cone (ι := ι) b := by
  classical
  obtain ⟨n, b, r, hb⟩ := hC.exists_basis
  obtain ⟨B, hB, heC⟩ := RegularQuotients.hull_basis_indices hι hC.toIsToricCone b r hb
  have hBu : B = Finset.univ := by
    apply Finset.eq_univ_iff_forall.2
    intro i
    have hi : ι (b i) ∈ Submodule.span ℝ (ι '' (b '' (B : Set (Fin n)))) := by
      rw [← RayHyperplanes.span_hull_eq, ← heC, hfull]
      trivial
    have hm := (RegularQuotients.mem_integer_span_iff hι b B (b i)).2 hi
    exact b.self_mem_span_image.1 hm
  refine ⟨n, b, ?_⟩
  rw [heC, hBu]
  simp only [Finset.coe_univ, Set.image_univ, ← Set.range_comp]
  rfl

/-- Every face of a cone of a basis is generated by an actual subset of that basis. -/
theorem face_eq_basisSubset {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℤ N) {F : PointedCone ℝ V}
    (hF : F.IsFaceOf (cone (ι := ι) b)) :
    ∃ A : Finset I, F = PointedCone.hull ℝ (ι '' (b '' (A : Set I))) := by
  classical
  let A : Finset I := Finset.univ.filter (fun i => ι (b i) ∈ F)
  refine ⟨A, ?_⟩
  have he := (show (cone (ι := ι) b).Face from ⟨F, hF⟩).eq_hull_image
    (rfl : cone (ι := ι) b = PointedCone.hull ℝ (Set.range (fun i => ι (b i))))
  change F = _ at he
  rw [he]
  congr 1
  rw [Set.image_image]
  congr 1
  ext i
  simp [A]
  change (ι (b i) ∈ F ↔ ι (b i) ∈ F)
  rfl

/-- A full regular cone and any one of its faces share one full integral basis. -/
theorem exists_basis_with_face (hι : IsIntegralLattice ι) {F C : PointedCone ℝ V}
    (hC : IsRegularCone ι C) (hfull : Submodule.span ℝ (C : Set V) = ⊤)
    (hFC : F.IsFaceOf C) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (A : Finset (Fin n)),
      C = cone (ι := ι) b ∧ F = PointedCone.hull ℝ (ι '' (b '' (A : Set (Fin n)))) := by
  obtain ⟨n, b, rfl⟩ := exists_basis_of_full_regular hι hC hfull
  obtain ⟨A, hA⟩ := face_eq_basisSubset b hFC
  exact ⟨n, b, A, rfl, hA⟩

section Coordinates

variable {I : Type*} [Fintype I] [DecidableEq I]
  (hι : IsIntegralLattice ι) (b : Module.Basis I ℤ N)

/-- Reindexing a basis does not change its geometric cone. -/
theorem cone_reindex {J : Type*} (e : I ≃ J) :
    cone (ι := ι) (b.reindex e) = cone (ι := ι) b := by
  unfold cone
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨e.symm j, by simp⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp⟩

/-- Cone membership is nonnegativity of the unique real coordinates. -/
theorem mem_cone_iff (x : V) :
    x ∈ cone (ι := ι) b ↔ ∀ i, 0 ≤ (CoordinateQuotients.realBasis ι hι b).repr x i := by
  have hb : (fun i => ι (b i)) = CoordinateQuotients.realBasis ι hι b := by
    funext i
    exact (CoordinateQuotients.realBasis_apply ι hι b i).symm
  rw [cone, hb, ← Set.image_univ, PointedCone.mem_hull_image_iff_linearCombination]
  constructor
  · rintro ⟨c, _, hc, he⟩
    rw [← he, Module.Basis.repr_linearCombination]
    exact hc
  · intro h
    exact ⟨(CoordinateQuotients.realBasis ι hι b).repr x,
      (Finsupp.mem_supported _ _).2 (Set.subset_univ _), h,
      Module.Basis.linearCombination_repr _ x⟩

include hι in
/-- For lattice points, the same criterion uses their integral coordinates. -/
theorem lattice_mem_cone_iff (x : N) :
    ι x ∈ cone (ι := ι) b ↔ ∀ i, 0 ≤ b.repr x i := by
  rw [mem_cone_iff hι b]
  simp only [CoordinateQuotients.realBasis_repr]
  constructor <;> intro h i <;> exact_mod_cast h i

include hι in
/-- A cone of a full integral basis is full-dimensional. -/
theorem span_cone : Submodule.span ℝ (cone (ι := ι) b : Set V) = ⊤ := by
  rw [cone, RayHyperplanes.span_hull_eq]
  have hb : (fun i => ι (b i)) = CoordinateQuotients.realBasis ι hι b := by
    funext i
    exact (CoordinateQuotients.realBasis_apply ι hι b i).symm
  rw [hb]
  exact (CoordinateQuotients.realBasis ι hι b).span_eq

include hι in
/-- Every primitive vector on a basis cone ray is precisely the corresponding basis vector. -/
theorem primitive_generator_eq_basis (ρ : ToricRay (cone (ι := ι) b)) {u : N}
    (hu : IsPrimitiveGenerator ι ρ u) :
    ∃ i, b i = u := by
  let v := fun i => ι (b i)
  have hv : LinearIndependent ℝ v := hι.linearIndependent_basis b
  let e := toricRayEquivOfLinearIndependent v hv (rfl : cone (ι := ι) b = _)
  have hm : v (e ρ) ∈ ρ :=
    (apply_mem_iff_toricRayEquivOfLinearIndependent v hv rfl ρ (e ρ)).2 rfl
  refine ⟨e ρ, IsPrimitiveGenerator.unique hι ?_
    (isPrimitiveGenerator_iff.2 ⟨hm, b.isPrimitive _⟩) hu⟩
  exact (PointedCone.salient_hull_range hv).anti ρ.1.isFaceOf.le

include hι in
/-- Generator identification also applies to a cone supplied by an equality of cone sets. -/
theorem primitive_generator_eq_basis_of_eq {C : PointedCone ℝ V}
    (hC : C = cone (ι := ι) b) (ρ : ToricRay C) {u : N}
    (hu : IsPrimitiveGenerator ι ρ u) : ∃ i, b i = u := by
  subst C
  exact primitive_generator_eq_basis hι b ρ hu

end Coordinates

/-- Two integral bases generating the same cone differ only by a permutation. -/
theorem basis_permutation_of_cone_eq (hι : IsIntegralLattice ι)
    {I J : Type*} (b : Module.Basis I ℤ N) (c : Module.Basis J ℤ N)
    (h : cone (ι := ι) b = cone (ι := ι) c) :
    ∃ e : I ≃ J, ∀ i, b i = c (e i) := by
  let C := cone (ι := ι) b
  let vb := fun i => ι (b i)
  let vc := fun j => ι (c j)
  have hvb : LinearIndependent ℝ vb := hι.linearIndependent_basis b
  have hvc : LinearIndependent ℝ vc := hι.linearIndependent_basis c
  have hb : C = PointedCone.hull ℝ (Set.range vb) := rfl
  have hc : C = PointedCone.hull ℝ (Set.range vc) := h
  let eb := toricRayEquivOfLinearIndependent vb hvb hb
  let ec := toricRayEquivOfLinearIndependent vc hvc hc
  let e : I ≃ J := eb.symm.trans ec
  refine ⟨e, fun i => ?_⟩
  let ρ := eb.symm i
  have hbi : vb i ∈ ρ :=
    (apply_mem_iff_toricRayEquivOfLinearIndependent vb hvb hb ρ i).2
      (eb.apply_symm_apply i).symm
  have hci : vc (e i) ∈ ρ :=
    (apply_mem_iff_toricRayEquivOfLinearIndependent vc hvc hc ρ (e i)).2 rfl
  exact IsPrimitiveGenerator.unique hι
    ((PointedCone.salient_hull_range hvb).anti ρ.1.isFaceOf.le)
    (isPrimitiveGenerator_iff.2 ⟨hbi, b.isPrimitive i⟩)
    (isPrimitiveGenerator_iff.2 ⟨hci, c.isPrimitive (e i)⟩)

/-- The positive-coordinate sum is independent of the ordering or choice of a cone basis. -/
theorem positive_sum_eq_of_cone_eq (hι : IsIntegralLattice ι)
    {I J : Type*} [Fintype I] [Fintype J]
    (b : Module.Basis I ℤ N) (c : Module.Basis J ℤ N)
    (h : cone (ι := ι) b = cone (ι := ι) c) (u : N) :
    (∑ i, max (b.repr u i) 0) = ∑ j, max (c.repr u j) 0 := by
  obtain ⟨e, he⟩ := basis_permutation_of_cone_eq hι b c h
  have hb : b = c.reindex e.symm := Module.Basis.eq_of_apply_eq (by
    intro i
    simpa only [Module.Basis.reindex_apply, Equiv.symm_symm] using he i)
  rw [hb]
  simp only [Module.Basis.repr_reindex_apply, Equiv.symm_symm]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- A primitive fan ray is a primitive generator of an actual one-dimensional face
of one of its cones. Antipodal rays are distinct. -/
def IsRay (Φ : Fan ι) (u : N) : Prop :=
  ∃ C ∈ Φ.cones, ∃ ρ : ToricRay C, IsPrimitiveGenerator ι ρ u

/-- The paper's positive-coordinate criterion, quantified over every maximal-cone
basis. Basis choice is harmless by `positive_sum_eq_of_cone_eq`. -/
def PositiveCriterion (Φ : Fan ι) : Prop :=
  ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ N), cone (ι := ι) b ∈ Φ.cones →
    ∀ u, IsRay Φ u → ∑ i, max (b.repr u i) 0 ≤ 1

/-- The criterion applies to every finite indexing type, not just a chosen `Fin n`. -/
theorem PositiveCriterion.apply_basis {I : Type*} [Fintype I] [DecidableEq I]
    {Φ : Fan ι} (hΦ : PositiveCriterion Φ) (b : Module.Basis I ℤ N)
    (hb : cone (ι := ι) b ∈ Φ.cones) {u : N} (hu : IsRay Φ u) :
    ∑ i, max (b.repr u i) 0 ≤ 1 := by
  let e := Fintype.equivFin I
  have hcone : cone (ι := ι) (b.reindex e) ∈ Φ.cones := by
    rw [cone_reindex]
    exact hb
  have h := hΦ _ (b.reindex e) hcone u hu
  rw [positive_sum_eq_of_cone_eq Φ.lattice (b.reindex e) b (cone_reindex b e) u] at h
  exact h

/-- Each vector of a full cone basis is an actual primitive fan ray. -/
theorem isRay_basis {I : Type*} (Φ : Fan ι) (b : Module.Basis I ℤ N)
    (hb : cone (ι := ι) b ∈ Φ.cones) (i : I) : IsRay Φ (b i) := by
  let v := fun i => ι (b i)
  have hv : LinearIndependent ℝ v := Φ.lattice.linearIndependent_basis b
  let e := toricRayEquivOfLinearIndependent v hv (rfl : cone (ι := ι) b = _)
  refine ⟨cone b, hb, e.symm i, isPrimitiveGenerator_iff.2 ⟨?_, b.isPrimitive i⟩⟩
  exact (apply_mem_iff_toricRayEquivOfLinearIndependent v hv rfl (e.symm i) i).2
    (e.apply_symm_apply i).symm

/-- In a complete regular fan, every actual primitive ray occurs in a full cone basis. -/
theorem isRay_iff_basis (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular) (u : N) :
    IsRay Φ u ↔ ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N),
      cone (ι := ι) b ∈ Φ.cones ∧ ∃ i, b i = u := by
  constructor
  · rintro ⟨F, hF, ρ, hu⟩
    obtain ⟨C, hC, hfull, hFC⟩ := FanMaximalCones.exists_full_supercone Φ hΦ hF
    obtain ⟨n, b, rfl⟩ := exists_basis_of_full_regular Φ.lattice
      (Fan.isRegular_iff.1 hreg C hC) hfull
    have huC := (isPrimitiveGenerator_faceEmbedding hFC ρ).2 hu
    obtain ⟨i, hi⟩ := primitive_generator_eq_basis Φ.lattice b _ huC
    exact ⟨n, b, hC, i, hi⟩
  · rintro ⟨n, b, hb, i, rfl⟩
    exact isRay_basis Φ b hb i

end Unimodular.ConeBases
end
end Source_ConeBases

section Source_QuotientBases



@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.QuotientBases

attribute [local instance] Classical.propDecidable

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {ι : N →+ V} {ι' : N' →+ W}
  (hι : IsIntegralLattice ι) (hι' : IsIntegralLattice ι')
  (p : V →ₗ[ℝ] W) (q : N →+ N')
  (hcompat : ∀ n, p (ι n) = ι' (q n))
  {I : Type*} [Fintype I] [DecidableEq I]
  (b : Module.Basis I ℤ N) (A : Finset I)

include hι hι' hcompat in
/-- Compatibility with an actual lattice embedding identifies the integral kernel exactly. -/
theorem integer_kernel_eq_basis_span {F : PointedCone ℝ V}
    (hker : LinearMap.ker p = Submodule.span ℝ (F : Set V))
    (hF : F = PointedCone.hull ℝ (ι '' (b '' (A : Set I)))) :
    LinearMap.ker q.toIntLinearMap = Submodule.span ℤ (b '' (A : Set I)) := by
  ext x
  rw [LinearMap.mem_ker, RegularQuotients.mem_integer_span_iff hι b A]
  have hspan : Submodule.span ℝ (F : Set V) =
      Submodule.span ℝ (ι '' (b '' (A : Set I))) := by
    rw [hF, RayHyperplanes.span_hull_eq]
  rw [← hspan, ← hker]
  change q x = 0 ↔ p (ι x) = 0
  rw [hcompat x]
  exact ⟨fun hx => by rw [hx, map_zero], fun hx => hι'.injective (by simpa using hx)⟩

variable (hq : Function.Surjective q)
  (hk : LinearMap.ker q.toIntLinearMap = Submodule.span ℤ (b '' (A : Set I)))

include hcompat in
/-- The projected full cone is the cone of the surviving integral quotient basis. -/
theorem map_cone_eq :
    (ConeBases.cone (ι := ι) b).map p = ConeBases.cone (ι := ι')
      (CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk) := by
  let bQ := CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk
  let D := ConeBases.cone (ι := ι') bQ
  apply le_antisymm
  · have hle : ConeBases.cone (ι := ι) b ≤ D.comap p := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      change p (ι (b i)) ∈ D
      rw [hcompat]
      by_cases hi : i ∈ A
      · have hz : q (b i) = 0 := by
          change b i ∈ LinearMap.ker q.toIntLinearMap
          rw [hk]
          exact Submodule.subset_span ⟨i, hi, rfl⟩
        rw [hz, map_zero]
        exact D.zero_mem
      · have he : bQ ⟨i, hi⟩ = q (b i) := CoordinateQuotients.imageBasis_apply _ _ _ _ _ _
        rw [← he]
        exact PointedCone.subset_hull ⟨⟨i, hi⟩, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hle hx
  · apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    have he : bQ i = q (b i.1) := CoordinateQuotients.imageBasis_apply _ _ _ _ _ _
    change ι' (bQ i) ∈ (ConeBases.cone (ι := ι) b).map p
    rw [he, ← hcompat]
    exact ⟨ι (b i.1), PointedCone.subset_hull ⟨i.1, rfl⟩, rfl⟩

/-- Taking quotient coordinates can only decrease the positive-coordinate sum. -/
theorem positive_sum_le (u : N) :
    (∑ i, max ((CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk).repr (q u) i) 0) ≤
      ∑ i, max (b.repr u i) 0 := by
  have he : (∑ i, max ((CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk).repr (q u) i) 0) =
      ∑ i : {i : I // i ∉ A}, max (b.repr u i.1) 0 := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : ℤ => max z 0)
      (CoordinateQuotients.imageBasis_repr b A q.toIntLinearMap hq hk u i)
  rw [he]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : I => i ∉ A)
    (fun i => max (b.repr u i) 0)
  have hn : 0 ≤ ∑ i : {i : I // ¬ i ∉ A}, max (b.repr u i.1) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  linarith

/-- A nonzero integral vector with nonnegative coordinates and positive sum at most one
has exactly one coordinate equal to one. -/
theorem integer_coordinates_eq_single {J : Type*} [Fintype J] [DecidableEq J]
    (c : J → ℤ) (hc : ∀ i, 0 ≤ c i) (hs : ∑ i, max (c i) 0 ≤ 1)
    (hne : ∃ i, c i ≠ 0) : ∃ j, ∀ i, c i = if j = i then 1 else 0 := by
  obtain ⟨j, hj⟩ := hne
  have hlj := Finset.single_le_sum (fun i _ => le_max_right (c i) 0) (Finset.mem_univ j)
  rw [max_eq_left (hc j)] at hlj
  have hj1 : c j = 1 := by have := hc j; omega
  refine ⟨j, fun i => ?_⟩
  by_cases hji : j = i
  · subst i
    simp [hj1]
  · have hp : max (c j) 0 + max (c i) 0 ≤ ∑ k, max (c k) 0 := by
      calc
        _ = ∑ k ∈ ({j, i} : Finset J), max (c k) 0 := by simp [hji]
        _ ≤ ∑ k, max (c k) 0 := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun _ _ _ => le_max_right _ _)
    rw [max_eq_left (hc j), max_eq_left (hc i), hj1] at hp
    have hi0 : c i = 0 := by have := hc i; omega
    simp [hji, hi0]

include hι' hcompat in
/-- The projected image of a ray satisfying the coordinate bound is exactly a quotient
basis vector whenever it lies in this quotient cone and is nonzero. -/
theorem projected_eq_basis (u : N) (hu : q u ≠ 0)
    (hcone : ι' (q u) ∈ (ConeBases.cone (ι := ι) b).map p)
    (hbound : ∑ i, max (b.repr u i) 0 ≤ 1) :
    ∃ i : {i : I // i ∉ A},
      CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk i = q u := by
  let bQ := CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk
  have hc : ∀ i, 0 ≤ bQ.repr (q u) i := by
    apply (ConeBases.lattice_mem_cone_iff hι' bQ (q u)).1
    rwa [← map_cone_eq p q hcompat b A hq hk]
  have hs : ∑ i, max (bQ.repr (q u) i) 0 ≤ 1 :=
    (positive_sum_le q b A hq hk u).trans hbound
  have hn : ∃ i, bQ.repr (q u) i ≠ 0 := by
    by_contra! h
    apply hu
    apply bQ.repr.injective
    ext i
    simpa using h i
  obtain ⟨j, hj⟩ := integer_coordinates_eq_single (fun i => bQ.repr (q u) i) hc hs hn
  refine ⟨j, bQ.repr.injective ?_⟩
  ext i
  change bQ.repr (bQ j) i = bQ.repr (q u) i
  simpa only [Module.Basis.repr_self_apply] using (hj i).symm

end Unimodular.QuotientBases
end
end Source_QuotientBases

section Source_PositiveQuotients



@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.PositiveQuotients

attribute [local instance] Classical.propDecidable

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {ι : N →+ V} {ι' : N' →+ W}
  (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
  (p : V →ₗ[ℝ] W) (q : N →+ N')
  (hcompat : ∀ n, p (ι n) = ι' (q n)) (hι' : IsIntegralLattice ι')
  (F : PointedCone ℝ V) (hF : F ∈ Φ.cones)
  (hker : LinearMap.ker p = Submodule.span ℝ (F : Set V))

local notation "Ψ" => StarQuotients.starFan (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF)

include hΦ hreg in
/-- Every quotient cone lies in the projection of a full original cone containing the
contracted face; both are presented in one full integral basis. -/
theorem exists_full_basis_above {H : PointedCone ℝ W} (hH : H ∈ (Ψ).cones) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ N) (A : Finset (Fin n)),
      ConeBases.cone (ι := ι) b ∈ Φ.cones ∧
      F = PointedCone.hull ℝ (ι '' (b '' (A : Set (Fin n)))) ∧
      F ≤ ConeBases.cone (ι := ι) b ∧ H ≤ (ConeBases.cone (ι := ι) b).map p := by
  obtain ⟨D, hD, hFD, hDH⟩ := (StarQuotients.mem_starFan_cones (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) H).1 hH
  obtain ⟨C, hC, hfull, hDC⟩ := FanMaximalCones.exists_full_supercone Φ hΦ hD
  have hFC := Φ.isFaceOf_of_le hC hF (hFD.trans hDC.le)
  obtain ⟨n, b, A, rfl, hFA⟩ := ConeBases.exists_basis_with_face Φ.lattice
    (Fan.isRegular_iff.1 hreg C hC) hfull hFC
  refine ⟨n, b, A, hC, hFA, hFC.le, ?_⟩
  rw [← hDH]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hDC.le hx, rfl⟩

variable (hp : Function.Surjective p) (hq : Function.Surjective q)
  (hcrit : ConeBases.PositiveCriterion Φ)

include hΦ hreg hp hq hcrit in
/-- Every nonzero image of an original primitive ray is already the exact primitive
vector of a quotient fan ray. No normalization, sign change, or finite-index adjustment occurs. -/
theorem image_isRay {u : N} (hu : ConeBases.IsRay Φ u) (hne : q u ≠ 0) :
    ConeBases.IsRay Ψ (q u) := by
  have hcomplete := StarQuotients.starFan_complete (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) hΦ hp
  obtain ⟨H, hH, huH⟩ := (Ψ).isComplete_iff.1 hcomplete (ι' (q u))
  obtain ⟨n, b, A, hb, hFA, hFb, hHb⟩ :=
    exists_full_basis_above (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) hH
  have hk := QuotientBases.integer_kernel_eq_basis_span Φ.lattice hι' p q hcompat b A hker hFA
  let bQ := CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk
  have he : (ConeBases.cone (ι := ι) b).map p = ConeBases.cone (ι := ι') bQ :=
    QuotientBases.map_cone_eq p q hcompat b A hq hk
  have hbQ : ConeBases.cone (ι := ι') bQ ∈ (Ψ).cones := by
    rw [← he]
    exact (StarQuotients.mem_starFan_cones (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) _).2
      ⟨ConeBases.cone b, hb, hFb, rfl⟩
  obtain ⟨i, hi⟩ := QuotientBases.projected_eq_basis hι' p q hcompat b A hq hk u hne
    (hHb huH) (hcrit.apply_basis b hb hu)
  rw [← hi]
  exact ConeBases.isRay_basis Ψ bQ hbQ i

include hΦ hreg hq in
/-- Conversely, every primitive quotient ray comes from an original primitive ray. -/
theorem isRay_exists_preimage {w : N'} (hw : ConeBases.IsRay Ψ w) :
    ∃ u, ConeBases.IsRay Φ u ∧ q u = w ∧ w ≠ 0 := by
  obtain ⟨H, hH, ρ, hwρ⟩ := hw
  obtain ⟨n, b, A, hb, hFA, hFb, hHb⟩ :=
    exists_full_basis_above (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) hH
  have hk := QuotientBases.integer_kernel_eq_basis_span Φ.lattice hι' p q hcompat b A hker hFA
  let bQ := CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk
  have he : (ConeBases.cone (ι := ι) b).map p = ConeBases.cone (ι := ι') bQ :=
    QuotientBases.map_cone_eq p q hcompat b A hq hk
  have hmap : (ConeBases.cone (ι := ι) b).map p ∈ (Ψ).cones :=
    (StarQuotients.mem_starFan_cones (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) _).2
      ⟨ConeBases.cone b, hb, hFb, rfl⟩
  have hface := (Ψ).isFaceOf_of_le hmap hH hHb
  have hwmap := (isPrimitiveGenerator_faceEmbedding hface ρ).2 hwρ
  obtain ⟨i, hi⟩ := ConeBases.primitive_generator_eq_basis_of_eq hι' bQ he _ hwmap
  refine ⟨b i.1, ConeBases.isRay_basis Φ b hb i.1, ?_, hwρ.ne_zero⟩
  exact (CoordinateQuotients.imageBasis_apply b A q.toIntLinearMap hq hk i).symm.trans hi

include hΦ hreg hp hq hcrit in
/-- Exact equality of primitive ray systems after deleting zero images and repeated vectors.
Antipodal vectors remain distinct because equality here is equality in the quotient lattice. -/
theorem isRay_iff_image (w : N') :
    ConeBases.IsRay Ψ w ↔ ∃ u, ConeBases.IsRay Φ u ∧ q u = w ∧ w ≠ 0 := by
  constructor
  · exact isRay_exists_preimage (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) (hq := hq)
  · rintro ⟨u, hu, rfl, hne⟩
    exact image_isRay (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) (hp := hp) (hq := hq) (hcrit := hcrit) hu hne

include hΦ hreg hp hq hcrit in
/-- Every full cone of the quotient has a full original lift, so its coordinate criterion
is the original criterion with some coordinates deleted. -/
theorem positiveCriterion : ConeBases.PositiveCriterion Ψ := by
  intro m c hc w hw
  obtain ⟨u, hu, rfl, _⟩ :=
    isRay_exists_preimage (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) (hq := hq) hw
  obtain ⟨n, b, A, hb, hFA, hFb, hcb⟩ :=
    exists_full_basis_above (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) hc
  have hk := QuotientBases.integer_kernel_eq_basis_span Φ.lattice hι' p q hcompat b A hker hFA
  let bQ := CoordinateQuotients.imageBasis b A q.toIntLinearMap hq hk
  have he : (ConeBases.cone (ι := ι) b).map p = ConeBases.cone (ι := ι') bQ :=
    QuotientBases.map_cone_eq p q hcompat b A hq hk
  have hmap : (ConeBases.cone (ι := ι) b).map p ∈ (Ψ).cones :=
    (StarQuotients.mem_starFan_cones (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) _).2
      ⟨ConeBases.cone b, hb, hFb, rfl⟩
  have hcomplete := StarQuotients.starFan_complete (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) hΦ hp
  have hceq : ConeBases.cone (ι := ι') c = (ConeBases.cone (ι := ι) b).map p :=
    (FanMaximalCones.full_iff_maximal Ψ hcomplete hc).1 (ConeBases.span_cone hι' c)
      _ hmap hcb
  rw [← ConeBases.positive_sum_eq_of_cone_eq hι' bQ c (he.symm.trans hceq.symm) (q u)]
  exact (QuotientBases.positive_sum_le q b A hq hk u).trans (hcrit.apply_basis b hb hu)

include hΦ hreg hp hq hcrit in
/-- The complete smooth positive-coordinate quotient-star conclusion, with its exact ray
system, for every contracted fan cone and the actual integral quotient presentation. -/
theorem contraction_of_cone :
    (Ψ).IsComplete ∧ (Ψ).IsRegular ∧ ConeBases.PositiveCriterion Ψ ∧
      ∀ w, ConeBases.IsRay Ψ w ↔ ∃ u, ConeBases.IsRay Φ u ∧ q u = w ∧ w ≠ 0 := by
  refine ⟨StarQuotients.starFan_complete (p := p) (hker := hker) (Φ := Φ) (q := q) (hq := hcompat) (hι' := hι') (F := F) (hF := hF) hΦ hp,
    RegularQuotients.starFan_isRegular Φ hreg p q hq hcompat hι' F hF hker, ?_, ?_⟩
  · exact positiveCriterion (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) (hp := hp) (hq := hq) (hcrit := hcrit)
  · exact isRay_iff_image (Φ := Φ) (hΦ := hΦ) (hreg := hreg) (p := p) (q := q) (hcompat := hcompat) (hι' := hι') (F := F) (hF := hF) (hker := hker) (hp := hp) (hq := hq) (hcrit := hcrit)

end Unimodular.PositiveQuotients
end
end Source_PositiveQuotients

section Source_FanBridge



@[expose] public section

open scoped Pointwise Topology BigOperators
open Set TauCeti.Toric

namespace Unimodular.FanBridge

/-- The usual embedding of the coordinate lattice in its real ambient space. -/
def standardEmbedding (n : ℕ) : Lattice n →+ Ambient n where
  toFun := embed
  map_zero' := by ext i; simp [embed]
  map_add' := by intro x y; ext i; simp [embed]

theorem standardEmbedding_isIntegralLattice (n : ℕ) :
    IsIntegralLattice (standardEmbedding n) := by
  apply isIntegralLattice_of_basis (Pi.basisFun ℤ (Fin n)) (Pi.basisFun ℝ (Fin n))
  intro i
  ext j
  simp [standardEmbedding, embed, Pi.basisFun_apply, Pi.single_apply]

variable {n : ℕ}

/-- The older coordinate face definition equals the genuine finitely generated cone. -/
theorem basisFace_eq_hull (b : Module.Basis (Fin n) ℤ (Lattice n))
    (A : Finset (Fin n)) :
    basisFace b A = (PointedCone.hull ℝ
      (standardEmbedding n '' (b '' (A : Set (Fin n)))) : Set (Ambient n)) := by
  classical
  ext x
  constructor
  · rintro ⟨c, hc, hA, rfl⟩
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ A
    · exact PointedCone.smul_mem _ (hc i)
        (PointedCone.subset_hull ⟨b i, ⟨i, hi, rfl⟩, rfl⟩)
    · rw [hA i hi, zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    rw [Set.image_image] at hx
    obtain ⟨c, hcA, hc, he⟩ := PointedCone.mem_hull_image_iff_linearCombination.1 hx
    refine ⟨fun i => c i, hc, ?_, ?_⟩
    · intro i hi
      by_contra hn
      exact hi ((Finsupp.mem_supported _ _).1 hcA (Finsupp.mem_support_iff.2 hn))
    · rw [← he, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
      rfl

/-- In particular, a full basis cone has the same real point set in both presentations. -/
theorem basisCone_eq_cone (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    basisCone b = (ConeBases.cone (ι := standardEmbedding n) b : Set (Ambient n)) := by
  calc
    basisCone b = basisFace b Finset.univ := by
      ext x
      constructor
      · rintro ⟨c, hc, he⟩
        exact ⟨c, hc, by simp, he⟩
      · rintro ⟨c, hc, _, he⟩
        exact ⟨c, hc, he⟩
    _ = _ := by
      rw [basisFace_eq_hull]
      congr 1
      simp only [Finset.coe_univ, Set.image_univ, ← Set.range_comp]
      rfl

/-- A full regular cone in the coordinate lattice has a basis indexed by exactly Fin n. -/
theorem exists_coordinate_basis (Φ : Fan (standardEmbedding n))
    (hreg : Φ.IsRegular) {C : PointedCone ℝ (Ambient n)} (hC : C ∈ Φ.cones)
    (hfull : Submodule.span ℝ (C : Set (Ambient n)) = ⊤) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      C = ConeBases.cone (ι := standardEmbedding n) b := by
  obtain ⟨m, b, hb⟩ := ConeBases.exists_basis_of_full_regular Φ.lattice
    (Fan.isRegular_iff.1 hreg C hC) hfull
  let e := b.indexEquiv (Pi.basisFun ℤ (Fin n))
  exact ⟨b.reindex e, hb.trans (ConeBases.cone_reindex b e).symm⟩

/-- Every actual complete regular fan on the standard lattice has the coordinate
presentation used by the checked positive-coordinate and rank-three arguments.
Its primitive ray set is unchanged, and the positive-coordinate criterion transfers.
No completeness or intersection property is assumed about the newly constructed presentation. -/
theorem exists_smoothCompleteFan (Φ : Fan (standardEmbedding n))
    (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular) :
    ∃ σ : SmoothCompleteFan n,
      (∀ u, u ∈ σ.rays ↔ ConeBases.IsRay Φ u) ∧
      (ConeBases.PositiveCriterion Φ ↔ σ.PositiveCoordinateCriterion) := by
  classical
  let T := {C : Φ.cones // Submodule.span ℝ (C.1 : Set (Ambient n)) = ⊤}
  letI : Fintype T := Fintype.ofFinite T
  have hex : ∀ C : T, ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      C.1.1 = ConeBases.cone (ι := standardEmbedding n) b :=
    fun C => exists_coordinate_basis Φ hreg C.1.2 C.2
  choose B hB using hex
  let S : Finset (Module.Basis (Fin n) ℤ (Lattice n)) := Finset.univ.image B
  have hS : ∀ b ∈ S, ConeBases.cone (ι := standardEmbedding n) b ∈ Φ.cones := by
    intro b hb
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.1 hb
    rw [← hB C]
    exact C.1.2
  let σ : SmoothCompleteFan n := {
    maximal := S
    complete := by
      intro x
      obtain ⟨C, hC, hfull, hxC⟩ := FanMaximalCones.full_cones_cover Φ hΦ x
      let C' : T := ⟨⟨C, hC⟩, hfull⟩
      refine ⟨B C', Finset.mem_image.2 ⟨C', Finset.mem_univ _, rfl⟩, ?_⟩
      rw [basisCone_eq_cone, ← hB C']
      exact hxC
    intersection := by
      intro b hb c hc
      have hbc := Φ.inf_isFaceOf_left (hS b hb) (hS c hc)
      have hcb := Φ.inf_isFaceOf_right (hS b hb) (hS c hc)
      obtain ⟨A, hA⟩ := ConeBases.face_eq_basisSubset b hbc
      obtain ⟨B', hB'⟩ := ConeBases.face_eq_basisSubset c hcb
      refine ⟨A, B', ?_, ?_⟩
      · rw [basisCone_eq_cone, basisCone_eq_cone, basisFace_eq_hull]
        change ((ConeBases.cone (ι := standardEmbedding n) b ⊓
          ConeBases.cone (ι := standardEmbedding n) c : PointedCone ℝ (Ambient n)) :
          Set (Ambient n)) = _
        rw [hA]
      · rw [basisCone_eq_cone, basisCone_eq_cone, basisFace_eq_hull]
        change ((ConeBases.cone (ι := standardEmbedding n) b ⊓
          ConeBases.cone (ι := standardEmbedding n) c : PointedCone ℝ (Ambient n)) :
          Set (Ambient n)) = _
        rw [hB'] }
  have hrays : ∀ u, u ∈ σ.rays ↔ ConeBases.IsRay Φ u := by
    intro u
    constructor
    · rintro ⟨b, hb, i, rfl⟩
      exact ConeBases.isRay_basis Φ b (hS b hb) i
    · rintro ⟨F, hF, ρ, hu⟩
      obtain ⟨C, hC, hfull, hFC⟩ := FanMaximalCones.exists_full_supercone Φ hΦ hF
      let C' : T := ⟨⟨C, hC⟩, hfull⟩
      have huC := (isPrimitiveGenerator_faceEmbedding hFC ρ).2 hu
      obtain ⟨i, hi⟩ := ConeBases.primitive_generator_eq_basis_of_eq Φ.lattice (B C')
        (hB C') _ huC
      exact ⟨B C', Finset.mem_image.2 ⟨C', Finset.mem_univ _, rfl⟩, i, hi⟩
  refine ⟨σ, hrays, ⟨?_, ?_⟩⟩
  · intro hcrit b hb u hu
    exact hcrit n b (hS b hb) u ((hrays u).1 hu)
  · intro hcrit m b hb u hu
    let C' : T := ⟨⟨ConeBases.cone (ι := standardEmbedding n) b, hb⟩,
      ConeBases.span_cone Φ.lattice b⟩
    have hsum := hcrit (B C') (Finset.mem_image.2 ⟨C', Finset.mem_univ _, rfl⟩)
      u ((hrays u).2 hu)
    rw [ConeBases.positive_sum_eq_of_cone_eq Φ.lattice b (B C') (hB C') u]
    exact hsum

/-- A complete regular fan on any integral lattice can be placed in any specified
integral basis. Both primitive rays and the positive-coordinate criterion transfer
exactly; the dimension and the integral lattice are unchanged. -/
theorem exists_smoothCompleteFan_in_basis
    {N V : Type*} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
    (hcrit : ConeBases.PositiveCriterion Φ) (b : Module.Basis (Fin n) ℤ N) :
    ∃ σ : SmoothCompleteFan n, σ.PositiveCoordinateCriterion ∧
      ∀ u, ConeBases.IsRay Φ u ↔ b.equivFun u ∈ σ.rays := by
  classical
  let q : N →+ Lattice n := b.equivFun.toLinearMap.toAddMonoidHom
  let br := CoordinateQuotients.realBasis ι Φ.lattice b
  let p : V →ₗ[ℝ] Ambient n := br.equivFun.toLinearMap
  have hcompat : ∀ u, p (ι u) = standardEmbedding n (q u) := by
    intro u
    funext i
    exact CoordinateQuotients.realBasis_repr ι Φ.lattice b u i
  have hker : LinearMap.ker p = Submodule.span ℝ ((⊥ : PointedCone ℝ V) : Set V) := by
    rw [LinearMap.ker_eq_bot.mpr br.equivFun.injective]
    simp
  have hzero : (⊥ : PointedCone ℝ V) ∈ Φ.cones := by
    obtain ⟨C, hC, _⟩ := Φ.isComplete_iff.1 hΦ 0
    exact Φ.bot_mem hC
  let Γ := StarQuotients.starFan (p := p) (hker := hker) (Φ := Φ) (q := q)
    (hq := hcompat) (hι' := standardEmbedding_isIntegralLattice n) (F := ⊥) (hF := hzero)
  obtain ⟨hΓ, hΓreg, hΓcrit, hΓrays⟩ :=
    PositiveQuotients.contraction_of_cone (Φ := Φ) (hΦ := hΦ) (hreg := hreg)
      (p := p) (q := q) (hcompat := hcompat)
      (hι' := standardEmbedding_isIntegralLattice n) (F := ⊥) (hF := hzero) (hker := hker)
      (hp := br.equivFun.surjective) (hq := b.equivFun.surjective) (hcrit := hcrit)
  obtain ⟨σ, hσrays, hσcrit⟩ := exists_smoothCompleteFan Γ hΓ hΓreg
  refine ⟨σ, hσcrit.mp hΓcrit, ?_⟩
  intro u
  rw [hσrays]
  change ConeBases.IsRay Φ u ↔ ConeBases.IsRay Γ (q u)
  rw [hΓrays]
  constructor
  · intro hu
    refine ⟨u, hu, rfl, ?_⟩
    obtain ⟨C, hC, ρ, hu⟩ := hu
    intro he
    apply hu.ne_zero
    apply b.equivFun.injective
    simpa [q] using he
  · rintro ⟨v, hv, hvu, _⟩
    change b.equivFun v = b.equivFun u at hvu
    exact b.equivFun.injective hvu ▸ hv

/-- Lemma 6.1 in an arbitrary integral lattice and in any finite indexing of any
integral basis. The determinant statement follows directly from the checked basis-cover
argument, with completeness supplying a covering family of actual maximal-cone bases. -/
theorem uniform_of_positiveCriterion
    {N V I : Type*} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype I] [DecidableEq I] {ι : N →+ V}
    (Φ : Fan ι) (hΦ : Φ.IsComplete) (hreg : Φ.IsRegular)
    (hcrit : ConeBases.PositiveCriterion Φ) (b : Module.Basis I ℤ N) :
    IntegralRigidity.Uniform b (fun u : {u // ConeBases.IsRay Φ u} => u.val) := by
  classical
  let e := Fintype.equivFin I
  let b₀ := b.reindex e
  let T := {C : Φ.cones // Submodule.span ℝ (C.1 : Set V) = ⊤}
  letI : Fintype T := Fintype.ofFinite T
  have hex : ∀ C : T, ∃ c : Module.Basis (Fin (Fintype.card I)) ℤ N,
      C.1.1 = ConeBases.cone (ι := ι) c := by
    intro C
    obtain ⟨m, c, hc⟩ := ConeBases.exists_basis_of_full_regular Φ.lattice
      (Fan.isRegular_iff.1 hreg C.1.1 C.1.2) C.2
    exact ⟨c.reindex (c.indexEquiv b₀),
      hc.trans (ConeBases.cone_reindex c (c.indexEquiv b₀)).symm⟩
  choose B hB using hex
  have h : IntegralRigidity.Uniform b₀ (fun u : {u // ConeBases.IsRay Φ u} => u.val) := by
    apply BasisCover.uniform_of_basis_cover B
    · intro x
      obtain ⟨C, hC, hfull, hxC⟩ := FanMaximalCones.full_cones_cover Φ hΦ (ι x)
      let C' : T := ⟨⟨C, hC⟩, hfull⟩
      refine ⟨C', (ConeBases.lattice_mem_cone_iff Φ.lattice (B C') x).1 ?_⟩
      rw [← hB C']
      exact hxC
    · intro C u
      apply hcrit _ (B C) _ u.val u.property
      rw [← hB C]
      exact C.1.2
  intro a
  have ha := h (a ∘ e.symm)
  change |(b.reindex e).det ((fun u : {u // ConeBases.IsRay Φ u} => u.val) ∘
    (a ∘ e.symm))| ≤ 1 at ha
  rw [Module.Basis.det_reindex] at ha
  have he : ((fun u : {u // ConeBases.IsRay Φ u} => u.val) ∘ (a ∘ e.symm)) ∘ e =
      (fun u : {u // ConeBases.IsRay Φ u} => u.val) ∘ a := by
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rwa [he] at ha

end Unimodular.FanBridge
end
end Source_FanBridge

#eval "FAN_BRIDGE_FOUNDATIONS_END"
