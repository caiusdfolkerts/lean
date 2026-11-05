module
public import PaperVerification.ToricIntegralBasis
@[expose] public section
/-!
# Saturated integral affine coordinate embeddings

These data encode an ordinary injective integral affine map whose linear image
is saturated in the ambient lattice. The saturation clause is about all actual
lattice vectors in that real subspace; no decomposition property is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricExchange

/-- An integral affine coordinate embedding with exactly the induced lattice
on its real image. -/
structure IntegralAffineEmbedding (d n : ℕ) where
  origin : Lattice n
  linear : Lattice d →+ Lattice n
  realLinear : Ambient d →ₗ[ℝ] Ambient n
  injective : Function.Injective realLinear
  compatible : ∀ z, embed n (linear z) = realLinear (embed d z)
  saturated : ∀ z : Lattice n, embed n z ∈ Set.range realLinear → ∃ w, linear w = z

/-- Coordinate content of an integer vector, equal to its lattice segment length. -/
def latticeContent {n : ℕ} (z : Lattice n) : ℕ :=
  Finset.univ.gcd (fun i => (z i).natAbs)

/-- Coordinate gcd divisibility is exactly divisibility of the whole lattice vector. -/
theorem dvd_latticeContent_iff {n : ℕ} (k : ℕ) (z : Lattice n) :
    k ∣ latticeContent z ↔ ∃ w : Lattice n, z = (k : ℤ) • w := by
  classical
  constructor
  · intro hk
    have hd (i : Fin n) : (k : ℤ) ∣ z i :=
      Int.natCast_dvd.mpr (hk.trans (Finset.gcd_dvd (Finset.mem_univ i)))
    choose w hw using hd
    exact ⟨w, by funext i; exact hw i⟩
  · rintro ⟨w, rfl⟩
    apply Finset.dvd_gcd
    intro i hi
    apply Int.natCast_dvd.mp
    exact ⟨w i, rfl⟩

/-- Injective affine maps preserve ordinary extreme subsets. -/
theorem affine_isExtreme_image {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P F : Set V} (hF : IsExtreme ℝ P F) :
    IsExtreme ℝ (f '' P) (f '' F) := by
  refine ⟨Set.image_mono hF.subset, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
  rw [← image_openSegment ℝ f x y] at hseg
  obtain ⟨w, hw, he⟩ := hseg
  have hwz := hf he
  subst w
  exact ⟨x, hF.left_mem_of_mem_openSegment hx hy hz hw, rfl⟩

/-- Extremeness of an affine image is equivalent to extremeness in the source. -/
theorem affine_isExtreme_image_iff {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    (P F : Set V) :
    IsExtreme ℝ (f '' P) (f '' F) ↔ IsExtreme ℝ P F := by
  constructor
  · intro hF
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, he⟩ := hF.subset ⟨x, hx, rfl⟩
      have hyx := hf he
      simpa only [hyx] using hy
    · intro x hx y hy z hz hseg
      have hseg' : f z ∈ openSegment ℝ (f x) (f y) := by
        rw [← image_openSegment ℝ f x y]
        exact ⟨z, hseg, rfl⟩
      obtain ⟨w, hw, he⟩ := hF.left_mem_of_mem_openSegment
        ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hseg'
      have hwx := hf he
      simpa only [hwx] using hw
  · exact affine_isExtreme_image f hf

namespace IntegralAffineEmbedding

variable {d n : ℕ} (e : IntegralAffineEmbedding d n)

theorem linear_injective : Function.Injective e.linear := by
  intro x y h
  apply embed_injective d
  apply e.injective
  simpa only [e.compatible] using congrArg (embed n) h

/-- Saturation preserves divisibility of lattice vectors by every natural
number, including zero. -/
theorem linear_exists_smul_iff (k : ℕ) (z : Lattice d) :
    (∃ w : Lattice n, e.linear z = (k : ℤ) • w) ↔
      ∃ w : Lattice d, z = (k : ℤ) • w := by
  constructor
  · rintro ⟨w, hw⟩
    by_cases hk : k = 0
    · subst k
      refine ⟨0, ?_⟩
      apply e.linear_injective
      simpa using hw
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have he : e.realLinear (embed d z) = (k : ℝ) • embed n w := by
        rw [← e.compatible, hw, embed_int_smul, Int.cast_natCast]
      have hwrange : embed n w ∈ Set.range e.realLinear := by
        refine ⟨(k : ℝ)⁻¹ • embed d z, ?_⟩
        rw [map_smul, he, smul_smul, inv_mul_cancel₀ hkR, one_smul]
      obtain ⟨v, hv⟩ := e.saturated w hwrange
      refine ⟨v, ?_⟩
      apply e.linear_injective
      rw [map_zsmul, hv]
      exact hw
  · rintro ⟨w, rfl⟩
    exact ⟨e.linear w, map_zsmul e.linear _ _⟩

/-- Saturated integral embeddings preserve the exact coordinate gcd. -/
theorem latticeContent_linear (z : Lattice d) :
    latticeContent (e.linear z) = latticeContent z := by
  apply Nat.dvd_antisymm
  · apply (dvd_latticeContent_iff _ z).mpr
    apply (e.linear_exists_smul_iff _ z).mp
    exact (dvd_latticeContent_iff _ (e.linear z)).mp dvd_rfl
  · apply (dvd_latticeContent_iff _ (e.linear z)).mpr
    apply (e.linear_exists_smul_iff _ z).mpr
    exact (dvd_latticeContent_iff _ z).mp dvd_rfl

/-- The actual real affine map, including its integral translation. -/
def realMap : Ambient d →ᵃ[ℝ] Ambient n :=
  AffineMap.const ℝ (Ambient d) (embed n e.origin) + e.realLinear.toAffineMap

/-- The corresponding map on actual integer coordinates. -/
def latticeMap (z : Lattice d) : Lattice n := e.origin + e.linear z

@[simp] theorem realMap_apply (x : Ambient d) :
    e.realMap x = embed n e.origin + e.realLinear x := rfl

@[simp] theorem embed_latticeMap (z : Lattice d) :
    embed n (e.latticeMap z) = e.realMap (embed d z) := by
  simp [latticeMap, realMap_apply, e.compatible]

theorem realMap_injective : Function.Injective e.realMap := by
  intro x y h
  apply e.injective
  exact add_left_cancel h

theorem latticeMap_injective : Function.Injective e.latticeMap := by
  intro x y h
  apply embed_injective d
  apply e.realMap_injective
  simpa only [embed_latticeMap] using congrArg (embed n) h

/-- The usual lattice length is unchanged by a saturated integral affine chart. -/
theorem latticeLength_latticeMap (x y : Lattice d) :
    LatticePolytope.latticeLength (e.latticeMap x) (e.latticeMap y) =
      LatticePolytope.latticeLength x y := by
  change latticeContent (e.latticeMap y - e.latticeMap x) = latticeContent (y - x)
  have he : e.latticeMap y - e.latticeMap x = e.linear (y - x) := by
    simp only [latticeMap, map_sub]
    abel
  rw [he, e.latticeContent_linear]

/-- Every ambient lattice point in the affine image has unique integral
coordinates. Thus the coordinate lattice is the saturated face lattice. -/
theorem exists_latticeMap_of_mem_range (z : Lattice n)
    (hz : embed n z ∈ Set.range e.realMap) :
    ∃ w : Lattice d, e.latticeMap w = z := by
  obtain ⟨x, hx⟩ := hz
  have hrange : embed n (z - e.origin) ∈ Set.range e.realLinear := by
    refine ⟨x, ?_⟩
    rw [map_sub, ← hx, realMap_apply, add_sub_cancel_left]
  obtain ⟨w, hw⟩ := e.saturated (z - e.origin) hrange
  refine ⟨w, ?_⟩
  simp only [latticeMap, hw]
  abel

/-- Lattice-point membership in an affine image is exactly membership of the
unique integral preimage. -/
theorem lattice_image_membership (P : Set (Ambient d)) (z : Lattice n) :
    embed n z ∈ e.realMap '' P ↔
      ∃ w : Lattice d, embed d w ∈ P ∧ e.latticeMap w = z := by
  constructor
  · rintro ⟨x, hx, he⟩
    obtain ⟨w, hw⟩ := e.exists_latticeMap_of_mem_range z ⟨x, he⟩
    refine ⟨w, ?_, hw⟩
    have hcoord : embed d w = x := by
      apply e.realMap_injective
      rw [← e.embed_latticeMap, hw, he]
    simpa only [hcoord] using hx
  · rintro ⟨w, hw, rfl⟩
    exact ⟨embed d w, hw, (e.embed_latticeMap w).symm⟩

/-- The induced map on points of a convex set uses the actual affine image. -/
def mapLatticePoint (P : Set (Ambient d)) :
    latticePoints (embed d) P → latticePoints (embed n) (e.realMap '' P) :=
  fun z => ⟨e.latticeMap z, (e.lattice_image_membership P _).mpr ⟨z, z.property, rfl⟩⟩

/-- Summing affine images adds one copy of the origin per summand. -/
theorem total_mapLatticePoint (P : Set (Ambient d))
    (s : Multiset (latticePoints (embed d) P)) :
    total (latticePoints (embed n) (e.realMap '' P)) (s.map (e.mapLatticePoint P)) =
      s.card • e.origin + e.linear (total (latticePoints (embed d) P) s) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, total_cons, ih, Multiset.card_cons, map_add,
      add_nsmul, one_nsmul]
    change e.origin + e.linear (a : Lattice d) +
      (s.card • e.origin + e.linear (total (latticePoints (embed d) P) s)) = _
    abel

/-- Full integer decomposition transfers through a saturated integral affine
embedding in every degree, with the translation multiplicity handled exactly. -/
theorem integerDecompositionProperty_image (P : Set (Ambient d))
    (hP : IntegerDecompositionProperty (embed d) P) :
    IntegerDecompositionProperty (embed n) (e.realMap '' P) := by
  intro k hk z hz
  obtain ⟨_, ⟨x, hx, rfl⟩, hz⟩ := hz
  have hdiff : embed n (z - (k : ℤ) • e.origin) = e.realLinear ((k : ℝ) • x) := by
    rw [map_sub, embed_int_smul, hz, realMap_apply, smul_add, map_smul]
    simp only [Int.cast_natCast]
    abel
  obtain ⟨u, hu⟩ := e.saturated (z - (k : ℤ) • e.origin) ⟨(k : ℝ) • x, hdiff.symm⟩
  have huR : embed d u = (k : ℝ) • x := by
    apply e.injective
    rw [← e.compatible, hu, hdiff]
  obtain ⟨s, hcard, htotal⟩ := hP k hk u ⟨x, hx, huR⟩
  refine ⟨s.map (e.mapLatticePoint P), ?_, ?_⟩
  · simpa only [Multiset.card_map] using hcard
  · rw [e.total_mapLatticePoint, hcard, htotal, hu, natCast_zsmul]
    abel

/-- The affine range of a full-dimensional coordinate polytope equals the
actual affine span of its image. -/
theorem realMap_range_eq_affineSpan (P : LatticePolytope d) :
    Set.range e.realMap = (affineSpan ℝ (e.realMap '' P.carrier) : Set (Ambient n)) := by
  rw [← AffineSubspace.map_span]
  change Set.range e.realMap = e.realMap '' (affineSpan ℝ P.carrier : Set (Ambient d))
  rw [show affineSpan ℝ P.carrier = ⊤ from P.fullDimensional]
  simp

/-- Two full-dimensional charts of the same actual set have equal affine ranges. -/
theorem realMap_range_eq_of_image_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n) (P : LatticePolytope d) (Q : LatticePolytope k)
    (h : e.realMap '' P.carrier = f.realMap '' Q.carrier) :
    Set.range e.realMap = Set.range f.realMap := by
  rw [e.realMap_range_eq_affineSpan P, f.realMap_range_eq_affineSpan Q, h]

/-- Edges in a chart are exactly the actual nondegenerate segment faces of
its affine image. -/
theorem edge_iff_ambient (P : LatticePolytope d) (x y : Ambient d) :
    P.IsEdge x y ↔ e.realMap x ≠ e.realMap y ∧
      IsExtreme ℝ (e.realMap '' P.carrier) (segment ℝ (e.realMap x) (e.realMap y)) := by
  rw [LatticePolytope.IsEdge, ← image_segment ℝ e.realMap,
    affine_isExtreme_image_iff e.realMap e.realMap_injective]
  constructor
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (e.realMap_injective he), hface⟩
  · rintro ⟨hne, hface⟩
    exact ⟨fun he => hne (congrArg e.realMap he), hface⟩

/-- Actual edges transfer between any two injective affine charts of the same set. -/
theorem edge_transfer_iff {k : ℕ} (f : IntegralAffineEmbedding k n)
    (P : LatticePolytope d) (Q : LatticePolytope k)
    (h : e.realMap '' P.carrier = f.realMap '' Q.carrier)
    (x y : Ambient d) (u v : Ambient k)
    (hx : e.realMap x = f.realMap u) (hy : e.realMap y = f.realMap v) :
    P.IsEdge x y ↔ Q.IsEdge u v := by
  rw [e.edge_iff_ambient P, f.edge_iff_ambient Q, h, hx, hy]

/-- Equal affine coordinate ranges have equal linear direction ranges, even
when the two integral origins differ. -/
theorem linear_range_eq_of_affine_range_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realMap = Set.range f.realMap) :
    Set.range e.realLinear = Set.range f.realLinear := by
  have hincl {d k : ℕ} (e : IntegralAffineEmbedding d n) (f : IntegralAffineEmbedding k n)
      (h : Set.range e.realMap = Set.range f.realMap) :
      Set.range e.realLinear ⊆ Set.range f.realLinear := by
    rintro z ⟨x, rfl⟩
    have hx : e.realMap x ∈ Set.range f.realMap := by rw [← h]; exact Set.mem_range_self x
    have hzero : e.realMap 0 ∈ Set.range f.realMap := by rw [← h]; exact Set.mem_range_self 0
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y0, hy0⟩ := hzero
    refine ⟨y - y0, ?_⟩
    rw [map_sub]
    have he := congrArg₂ (fun a b : Ambient n => a - b) hy hy0
    simpa only [realMap_apply, map_zero, add_zero, add_sub_add_left_eq_sub,
      add_sub_cancel_left] using he
  exact Set.Subset.antisymm (hincl e f h) (hincl f e h.symm)

/-- Saturation supplies an integral coordinate preimage for every vector
expressed in another chart of the same real direction subspace. -/
theorem exists_linear_preimage_of_range_eq {k : ℕ}
    (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    ∃ w : Lattice d, e.linear w = f.linear z := by
  apply e.saturated
  rw [h, f.compatible]
  exact Set.mem_range_self (embed k z)

/-- The integral linear map changing between two saturated coordinate charts. -/
def changeLinearMap {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) : Lattice k →ₗ[ℤ] Lattice d where
  toFun z := Classical.choose (e.exists_linear_preimage_of_range_eq f h z)
  map_add' x y := by
    apply e.linear_injective
    change e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h (x + y))) =
      e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h x) +
        Classical.choose (e.exists_linear_preimage_of_range_eq f h y))
    rw [Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h (x + y))]
    simp only [map_add,
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h x),
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h y)]
  map_smul' r x := by
    apply e.linear_injective
    change e.linear (Classical.choose (e.exists_linear_preimage_of_range_eq f h (r • x))) =
      e.linear (r • Classical.choose (e.exists_linear_preimage_of_range_eq f h x))
    rw [Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h (r • x))]
    simp only [map_zsmul,
      Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h x)]

@[simp] theorem changeLinearMap_apply {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    e.linear (e.changeLinearMap f h z) = f.linear z :=
  Classical.choose_spec (e.exists_linear_preimage_of_range_eq f h z)

/-- The change of saturated lattice coordinates is an actual integral linear
equivalence, in arbitrary source dimensions. -/
def changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) : Lattice k ≃ₗ[ℤ] Lattice d :=
  LinearEquiv.ofBijective (e.changeLinearMap f h) ⟨by
    intro x y hxy
    apply f.linear_injective
    simpa only [e.changeLinearMap_apply] using congrArg e.linear hxy, by
    intro y
    obtain ⟨x, hx⟩ := f.exists_linear_preimage_of_range_eq e h.symm y
    refine ⟨x, e.linear_injective ?_⟩
    rw [e.changeLinearMap_apply]
    exact hx⟩

@[simp] theorem changeLinear_apply {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear) (z : Lattice k) :
    e.linear (e.changeLinear f h z) = f.linear z :=
  e.changeLinearMap_apply f h z

/-- Changing a saturated coordinate chart translates the origin once and
then uses the exact integral linear change of coordinates. -/
theorem latticeMap_changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear)
    (z0 : Lattice d) (hz0 : e.latticeMap z0 = f.origin) (z : Lattice k) :
    e.latticeMap (z0 + e.changeLinear f h z) = f.latticeMap z := by
  change e.origin + e.linear (z0 + e.changeLinear f h z) = f.origin + f.linear z
  rw [map_add, e.changeLinear_apply, ← add_assoc]
  exact congrArg (fun x => x + f.linear z) hz0

/-- The real images of integer-coordinate changes agree exactly. -/
theorem realMap_changeLinear {k : ℕ} (f : IntegralAffineEmbedding k n)
    (h : Set.range e.realLinear = Set.range f.realLinear)
    (z0 : Lattice d) (hz0 : e.latticeMap z0 = f.origin) (z : Lattice k) :
    e.realMap (embed d (z0 + e.changeLinear f h z)) = f.realMap (embed k z) := by
  rw [← e.embed_latticeMap, e.latticeMap_changeLinear f h z0 hz0 z, f.embed_latticeMap]

/-- Applying an affine lattice chart preserves the prescribed parity class
of a difference. This is the forward direction used for face parity. -/
theorem sameParity_latticeMap {x y : Lattice d} (h : SameParity x y) :
    SameParity (e.latticeMap x) (e.latticeMap y) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨e.linear w, ?_⟩
  change (e.origin + e.linear x) - (e.origin + e.linear y) = _
  rw [add_sub_add_left_eq_sub, ← map_sub, hw, map_add]

end IntegralAffineEmbedding

end PaperVerification.ToricGeometry
