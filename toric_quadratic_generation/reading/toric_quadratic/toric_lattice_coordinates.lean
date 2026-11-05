module

public import PaperVerification.ToricIntegralAffine
public import PaperVerification.ToricIdeal
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

/-!
# The lattice-basis representation bridge

An abstract rank-`n` lattice and its realification are identified with
`Fin n → ℤ` and `Fin n → ℝ` by an actual integral basis and its base change.
The proofs below preserve every degree of integer decomposition and identify
the actual polynomial kernels and quadratic ideals by variable renaming.
Thus choosing coordinates does not change either conclusion of Theorem 1.1.
-/

noncomputable section

namespace PaperVerification.ToricCoordinateTransport

open PaperVerification.ToricExchange
open PaperVerification.ToricGeometry
open scoped TensorProduct

section Configuration

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable (e : M ≃+ N) {A : Set M} {B : Set N}
variable (hAB : ∀ m, m ∈ A ↔ e m ∈ B)

/-- The actual bijection between lattice-point variables. -/
def configurationEquiv : A ≃ B where
  toFun a := ⟨e a, (hAB a).mp a.property⟩
  invFun b := ⟨e.symm b, (hAB (e.symm b)).mpr (by simpa using b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)

@[simp] theorem configurationEquiv_coe (a : A) :
    (configurationEquiv e hAB a : N) = e a := rfl

@[simp] theorem configurationEquiv_symm_coe (b : B) :
    ((configurationEquiv e hAB).symm b : M) = e.symm b := rfl

/-- Both the lattice sum and the degree are retained by the variable bijection. -/
theorem total_map_configurationEquiv (s : Multiset A) :
    total B (s.map (configurationEquiv e hAB)) = e (total A s) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, total_cons, configurationEquiv_coe, ih, map_add]

variable (R : Type*) [CommRing R]

/-- Literal renaming of the polynomial variables indexed by lattice points. -/
def configurationPolynomialEquiv : MvPolynomial A R ≃ₐ[R] MvPolynomial B R :=
  MvPolynomial.renameEquiv R (configurationEquiv e hAB)

@[simp] theorem configurationPolynomialEquiv_X (a : A) :
    configurationPolynomialEquiv e hAB R (MvPolynomial.X a) =
      MvPolynomial.X (configurationEquiv e hAB a) := by
  simp [configurationPolynomialEquiv]

@[simp] theorem configurationPolynomialEquiv_C (r : R) :
    configurationPolynomialEquiv e hAB R (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [configurationPolynomialEquiv, MvPolynomial.rename_C]

/-- The target isomorphism changes character exponents and fixes the
homogenizing variable. Its source and target are exactly the paper's rings. -/
def characterTargetEquiv :
    Polynomial (AddMonoidAlgebra R M) ≃+* Polynomial (AddMonoidAlgebra R N) :=
  Polynomial.mapEquiv (AddMonoidAlgebra.mapDomainRingEquiv R e)

@[simp] theorem characterTargetEquiv_C_single (m : M) (r : R) :
    characterTargetEquiv e R (Polynomial.C (AddMonoidAlgebra.single m r)) =
      Polynomial.C (AddMonoidAlgebra.single (e m) r) := by
  simp [characterTargetEquiv, Polynomial.mapEquiv]

@[simp] theorem characterTargetEquiv_X :
    characterTargetEquiv e R Polynomial.X = Polynomial.X := by
  simp [characterTargetEquiv, Polynomial.mapEquiv]

/-- The square of the actual toric homomorphisms commutes, on every polynomial. -/
theorem paperToricMap_naturality :
    (paperToricMap B R).comp (configurationPolynomialEquiv e hAB R).toRingHom =
      (characterTargetEquiv e R).toRingHom.comp (paperToricMap A R) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change paperToricMap B R (configurationPolynomialEquiv e hAB R (MvPolynomial.C r)) =
      characterTargetEquiv e R (paperToricMap A R (MvPolynomial.C r))
    simp only [configurationPolynomialEquiv_C, paperToricMap_C,
      characterTargetEquiv_C_single, map_zero]
  · intro a
    change paperToricMap B R (configurationPolynomialEquiv e hAB R (MvPolynomial.X a)) =
      characterTargetEquiv e R (paperToricMap A R (MvPolynomial.X a))
    simp only [configurationPolynomialEquiv_X, paperToricMap_X,
      map_mul, characterTargetEquiv_C_single, characterTargetEquiv_X,
      configurationEquiv_coe]

theorem paperToricMap_naturality_apply (p : MvPolynomial A R) :
    paperToricMap B R (configurationPolynomialEquiv e hAB R p) =
      characterTargetEquiv e R (paperToricMap A R p) :=
  RingHom.congr_fun (paperToricMap_naturality e hAB R) p

/-- Kernel membership is exactly preserved, not merely implied. -/
theorem mem_paper_kernel_iff (p : MvPolynomial A R) :
    configurationPolynomialEquiv e hAB R p ∈ RingHom.ker (paperToricMap B R) ↔
      p ∈ RingHom.ker (paperToricMap A R) := by
  change paperToricMap B R (configurationPolynomialEquiv e hAB R p) = 0 ↔
    paperToricMap A R p = 0
  rw [paperToricMap_naturality_apply]
  exact (characterTargetEquiv e R).map_eq_zero_iff

/-- The kernel is transported by the literal variable-renaming ring isomorphism. -/
theorem paper_kernel_map :
    (RingHom.ker (paperToricMap A R)).map
        (configurationPolynomialEquiv e hAB R).toRingHom =
      RingHom.ker (paperToricMap B R) := by
  ext p
  rw [Ideal.mem_map_iff_of_surjective (configurationPolynomialEquiv e hAB R).toRingHom
    (configurationPolynomialEquiv e hAB R).surjective]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (mem_paper_kernel_iff e hAB R q).mpr hq
  · intro hp
    obtain ⟨q, rfl⟩ := (configurationPolynomialEquiv e hAB R).surjective p
    exact ⟨q, (mem_paper_kernel_iff e hAB R q).mp hp, rfl⟩

/-- The full ideal of equal-sum quadratic binomials is transported exactly. -/
theorem polynomialQuadraticIdeal_map :
    (polynomialQuadraticIdeal A R).map
        (configurationPolynomialEquiv e hAB R).toRingHom =
      polynomialQuadraticIdeal B R := by
  rw [polynomialQuadraticIdeal, Ideal.map_span, polynomialQuadraticIdeal]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨a, b, c, d, he, rfl⟩, rfl⟩
    refine ⟨configurationEquiv e hAB a, configurationEquiv e hAB b,
      configurationEquiv e hAB c, configurationEquiv e hAB d, ?_, ?_⟩
    · simpa only [configurationEquiv_coe, map_add] using congrArg e he
    · simp only [map_sub, map_mul, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        AlgEquiv.coe_toRingEquiv, configurationPolynomialEquiv_X]
  · rintro ⟨a, b, c, d, he, rfl⟩
    let a' := (configurationEquiv e hAB).symm a
    let b' := (configurationEquiv e hAB).symm b
    let c' := (configurationEquiv e hAB).symm c
    let d' := (configurationEquiv e hAB).symm d
    have he' : (a' : M) + b' = (c' : M) + d' := by
      simpa only [a', b', c', d', configurationEquiv_symm_coe, map_add] using
        congrArg e.symm he
    refine ⟨MvPolynomial.X a' * MvPolynomial.X b' -
      MvPolynomial.X c' * MvPolynomial.X d', ⟨a', b', c', d', he', rfl⟩, ?_⟩
    simp [a', b', c', d', map_sub, map_mul]

include e hAB in
/-- Equality of the actual toric kernel and quadratic ideal is independent
of a choice of lattice coordinates, over any commutative coefficient ring. -/
theorem quadratic_generation_iff :
    RingHom.ker (paperToricMap A R) = polynomialQuadraticIdeal A R ↔
      RingHom.ker (paperToricMap B R) = polynomialQuadraticIdeal B R := by
  constructor
  · intro h
    rw [← paper_kernel_map e hAB R, h, polynomialQuadraticIdeal_map]
  · intro h
    ext p
    have hq : configurationPolynomialEquiv e hAB R p ∈ polynomialQuadraticIdeal B R ↔
        p ∈ polynomialQuadraticIdeal A R := by
      rw [← polynomialQuadraticIdeal_map e hAB R,
        Ideal.mem_map_iff_of_surjective (configurationPolynomialEquiv e hAB R).toRingHom
          (configurationPolynomialEquiv e hAB R).surjective]
      constructor
      · rintro ⟨q, hq, hqp⟩
        exact (configurationPolynomialEquiv e hAB R).injective hqp ▸ hq
      · intro hp
        exact ⟨p, hp, rfl⟩
    rw [← mem_paper_kernel_iff e hAB R p, h, hq]

end Configuration

section RealCoordinateTransport

variable {M N V W : Type*} [AddCommGroup M] [AddCommGroup N]
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable (ι : M →+ V) (κ : N →+ W) (e : M ≃+ N) (f : V ≃ₗ[ℝ] W)
variable (hcompat : ∀ m, κ (e m) = f (ι m))

/-- An integral basis of precisely the incident primitive edge directions,
written before choosing coordinates. This is the literal geometric
smoothness condition used in `LatticePolytope.Smooth`. -/
def SmoothEdgeBasis (n : ℕ) (embedding : M →+ V) (P : Set V) : Prop :=
  ∀ v ∈ P.extremePoints ℝ,
    ∃ (vZ : M) (b : Module.Basis (Fin n) ℤ M) (lengths : Fin n → ℕ),
      embedding vZ = v ∧
      (∀ i, 0 < lengths i ∧
        v ≠ embedding (vZ + (lengths i : ℤ) • b i) ∧
        IsExtreme ℝ P (segment ℝ v (embedding (vZ + (lengths i : ℤ) • b i)))) ∧
      (∀ w : V, v ≠ w → IsExtreme ℝ P (segment ℝ v w) →
        ∃ i, w = embedding (vZ + (lengths i : ℤ) • b i))

/-- Actual vertices are preserved by the real coordinate isomorphism. -/
theorem extremePoints_image_iff (P : Set V) (v : V) :
    f v ∈ (f '' P).extremePoints ℝ ↔ v ∈ P.extremePoints ℝ := by
  rw [← isExtreme_singleton, ← isExtreme_singleton]
  simpa only [Set.image_singleton, LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] using
    affine_isExtreme_image_iff f.toLinearMap.toAffineMap f.injective P {v}

/-- Actual nondegenerate segment faces, hence edges, are preserved exactly. -/
theorem edge_image_iff (P : Set V) (v w : V) :
    (f v ≠ f w ∧ IsExtreme ℝ (f '' P) (segment ℝ (f v) (f w))) ↔
      (v ≠ w ∧ IsExtreme ℝ P (segment ℝ v w)) := by
  have hface : IsExtreme ℝ (f '' P) (segment ℝ (f v) (f w)) ↔
      IsExtreme ℝ P (segment ℝ v w) := by
    have h := affine_isExtreme_image_iff f.toLinearMap.toAffineMap
      f.injective P (segment ℝ v w)
    rw [image_segment] at h
    simpa only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe] using h
  constructor
  · rintro ⟨hne, hF⟩
    exact ⟨fun h => hne (congrArg f h), hface.mp hF⟩
  · rintro ⟨hne, hF⟩
    exact ⟨fun h => hne (f.injective h), hface.mpr hF⟩

include hcompat in
/-- The full primitive edge-basis condition transfers, including the clause
that every incident edge is one of the displayed basis directions. -/
theorem smoothEdgeBasis_image (n : ℕ) (P : Set V)
    (hP : SmoothEdgeBasis n ι P) : SmoothEdgeBasis n κ (f '' P) := by
  intro v' hv'
  obtain ⟨v, hv, rfl⟩ := hv'.1
  have hvext := (extremePoints_image_iff f P v).mp hv'
  obtain ⟨vZ, b, lengths, hvZ, hinc, hall⟩ := hP v hvext
  let b' := b.map e.toIntLinearEquiv
  have hend (i : Fin n) :
      κ (e vZ + (lengths i : ℤ) • b' i) =
        f (ι (vZ + (lengths i : ℤ) • b i)) := by
    rw [← hcompat]
    congr 1
    simp [b', map_add, map_zsmul]
  refine ⟨e vZ, b', lengths, ?_, ?_, ?_⟩
  · rw [hcompat, hvZ]
  · intro i
    refine ⟨(hinc i).1, ?_⟩
    rw [hend]
    exact (edge_image_iff f P v _).mpr (hinc i).2
  · intro w' hne hF
    obtain ⟨w, rfl⟩ := f.surjective w'
    have hw := (edge_image_iff f P v w).mp ⟨hne, hF⟩
    obtain ⟨i, rfl⟩ := hall w hw.1 hw.2
    exact ⟨i, (hend i).symm⟩

include hcompat in
theorem smoothEdgeBasis_iff (n : ℕ) (P : Set V) :
    SmoothEdgeBasis n ι P ↔ SmoothEdgeBasis n κ (f '' P) := by
  constructor
  · exact smoothEdgeBasis_image ι κ e f hcompat n P
  · intro hP
    have hsymm : ∀ z, ι (e.symm z) = f.symm (κ z) := by
      intro z
      apply f.injective
      rw [← hcompat, e.apply_symm_apply, f.apply_symm_apply]
    have h := smoothEdgeBasis_image κ ι e.symm f.symm hsymm n (f '' P) hP
    simpa only [Set.image_image, Function.comp_def, f.symm_apply_apply, Set.image_id'] using h

include hcompat in
/-- Actual lattice points correspond to actual lattice points in the image. -/
theorem latticePoints_compatible_image (P : Set V) (m : M) :
    m ∈ latticePoints ι P ↔ e m ∈ latticePoints κ (f '' P) := by
  change ι m ∈ P ↔ κ (e m) ∈ f '' P
  rw [hcompat]
  constructor
  · intro hm
    exact ⟨ι m, hm, rfl⟩
  · rintro ⟨x, hx, hxm⟩
    exact f.injective hxm ▸ hx

include hcompat in
/-- Every positive-degree integral decomposition is carried to the image. -/
theorem integerDecompositionProperty_image (P : Set V)
    (hP : IntegerDecompositionProperty ι P) :
    IntegerDecompositionProperty κ (f '' P) := by
  intro k hk z hz
  obtain ⟨_, ⟨x, hx, rfl⟩, hz⟩ := hz
  have hu : ι (e.symm z) = (k : ℝ) • x := by
    apply f.injective
    rw [← hcompat, e.apply_symm_apply, map_smul]
    exact hz
  obtain ⟨s, hs, hsum⟩ := hP k hk (e.symm z) ⟨x, hx, hu⟩
  let g := configurationEquiv e (latticePoints_compatible_image ι κ e f hcompat P)
  refine ⟨s.map g, ?_, ?_⟩
  · simpa only [Multiset.card_map] using hs
  · rw [total_map_configurationEquiv, hsum, e.apply_symm_apply]

include hcompat in
/-- IDP is invariant under a compatible lattice and real linear equivalence. -/
theorem integerDecompositionProperty_iff (P : Set V) :
    IntegerDecompositionProperty ι P ↔ IntegerDecompositionProperty κ (f '' P) := by
  constructor
  · exact integerDecompositionProperty_image ι κ e f hcompat P
  · intro hP
    have hsymm : ∀ z, ι (e.symm z) = f.symm (κ z) := by
      intro z
      apply f.injective
      rw [← hcompat, e.apply_symm_apply, f.apply_symm_apply]
    have h := integerDecompositionProperty_image κ ι e.symm f.symm hsymm (f '' P) hP
    simpa only [Set.image_image, Function.comp_def, f.symm_apply_apply, Set.image_id'] using h

/-- The same lattice basis change preserves every prescribed parity class. -/
theorem sameParity_iff (a b : M) : SameParity (e a) (e b) ↔ SameParity a b := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨e.symm w, ?_⟩
    simpa only [map_sub, map_add, e.symm_apply_apply] using congrArg e.symm hw
  · rintro ⟨w, hw⟩
    refine ⟨e w, ?_⟩
    simpa only [map_sub, map_add] using congrArg e hw

end RealCoordinateTransport

section Realification

variable {M : Type*} [AddCommGroup M] {n : ℕ}

/-- The ordinary lattice inclusion in `M_ℝ = ℝ ⊗[ℤ] M`. -/
def realificationEmbedding : M →+ ℝ ⊗[ℤ] M where
  toFun m := (1 : ℝ) ⊗ₜ[ℤ] m
  map_zero' := TensorProduct.tmul_zero M (1 : ℝ)
  map_add' m₁ m₂ := TensorProduct.tmul_add (1 : ℝ) m₁ m₂

/-- The real coordinates are obtained by genuine scalar extension of an
integral basis; no compatible real isomorphism is an additional premise. -/
def basisRealCoordinates (b : Module.Basis (Fin n) ℤ M) :
    (ℝ ⊗[ℤ] M) ≃ₗ[ℝ] Ambient n :=
  (b.baseChange ℝ).equivFun

theorem basisRealCoordinates_compatible (b : Module.Basis (Fin n) ℤ M) (m : M) :
    embed n (b.equivFun m) = basisRealCoordinates b (realificationEmbedding m) := by
  ext i
  change ((b.repr m i : ℤ) : ℝ) = (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℤ] m) i
  rw [Module.Basis.baseChange_repr_tmul]
  simp only [zsmul_eq_mul, mul_one]

/-- A specified isomorphism `M ≃ ℤⁿ` alone supplies the compatible real
coordinate equivalence. -/
def realCoordinatesOfEquiv (e : M ≃+ Lattice n) :
    (ℝ ⊗[ℤ] M) ≃ₗ[ℝ] Ambient n :=
  basisRealCoordinates (Module.Basis.ofEquivFun e.toIntLinearEquiv)

theorem realCoordinatesOfEquiv_compatible (e : M ≃+ Lattice n) (m : M) :
    embed n (e m) = realCoordinatesOfEquiv e (realificationEmbedding m) := by
  simpa only [realCoordinatesOfEquiv, Module.Basis.equivFun_ofEquivFun,
    AddEquiv.coe_toIntLinearEquiv] using
    basisRealCoordinates_compatible (Module.Basis.ofEquivFun e.toIntLinearEquiv) m

theorem realificationEmbedding_injective (e : M ≃+ Lattice n) :
    Function.Injective (realificationEmbedding (M := M)) := by
  intro x y h
  apply e.injective
  apply embed_injective n
  simpa only [← realCoordinatesOfEquiv_compatible] using
    congrArg (realCoordinatesOfEquiv e) h

/-- Finite lattice convex hulls become precisely their coordinate convex
hulls under this isomorphism. -/
theorem realCoordinatesOfEquiv_convexHull (e : M ≃+ Lattice n) (s : Set M) :
    realCoordinatesOfEquiv e '' convexHull ℝ (realificationEmbedding '' s) =
      convexHull ℝ (embed n '' (e '' s)) := by
  change (realCoordinatesOfEquiv e).toLinearMap ''
      convexHull ℝ (realificationEmbedding '' s) = _
  rw [(realCoordinatesOfEquiv e).toLinearMap.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨e m, ⟨m, hm, rfl⟩, realCoordinatesOfEquiv_compatible e m⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨realificationEmbedding m, ⟨m, hm, rfl⟩,
      (realCoordinatesOfEquiv_compatible e m).symm⟩

/-- A finite full-dimensional abstract lattice polytope gives an actual
coordinate `LatticePolytope`, with no extra geometric hypothesis. -/
def coordinatePolytope (e : M ≃+ Lattice n) (s : Finset M) (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤) :
    LatticePolytope n where
  generators := s.image e
  nonempty := hs.image e
  fullDimensional := by
    rw [Finset.coe_image, ← realCoordinatesOfEquiv_convexHull]
    exact (realCoordinatesOfEquiv e).toLinearMap.toAffineMap.span_eq_top_of_surjective
      (realCoordinatesOfEquiv e).surjective hfull

theorem coordinatePolytope_carrier (e : M ≃+ Lattice n) (s : Finset M)
    (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤) :
    (coordinatePolytope e s hs hfull).carrier =
      realCoordinatesOfEquiv e '' convexHull ℝ (realificationEmbedding '' (s : Set M)) := by
  simp only [LatticePolytope.carrier, coordinatePolytope, Finset.coe_image,
    realCoordinatesOfEquiv_convexHull]

/-- Coordinate smoothness is exactly the abstract primitive edge-basis
condition; in particular no incident edges disappear under coordinate choice. -/
theorem coordinatePolytope_smooth_iff (e : M ≃+ Lattice n) (s : Finset M)
    (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤) :
    (coordinatePolytope e s hs hfull).Smooth ↔
      SmoothEdgeBasis n realificationEmbedding
        (convexHull ℝ (realificationEmbedding '' (s : Set M))) := by
  have hsmooth (Q : LatticePolytope n) :
      Q.Smooth ↔ SmoothEdgeBasis n (embed n) Q.carrier := by
    unfold LatticePolytope.Smooth SmoothEdgeBasis LatticePolytope.IsEdge
    constructor
    · intro h v hv
      obtain ⟨vZ, b, lengths, hvZ, hinc, hall⟩ := h v hv
      exact ⟨vZ, b, lengths, hvZ, hinc, fun w hne hF => hall w ⟨hne, hF⟩⟩
    · intro h v hv
      obtain ⟨vZ, b, lengths, hvZ, hinc, hall⟩ := h v hv
      exact ⟨vZ, b, lengths, hvZ, hinc, fun w hw => hall w hw.1 hw.2⟩
  rw [hsmooth, coordinatePolytope_carrier]
  exact (smoothEdgeBasis_iff realificationEmbedding (embed n) e
    (realCoordinatesOfEquiv e) (realCoordinatesOfEquiv_compatible e) n _).symm

/-- The coordinate gcd is exactly intrinsic divisibility of the original
lattice vector, so its segment-length meaning is independent of the basis. -/
theorem dvd_coordinateContent_iff (e : M ≃+ Lattice n) (k : ℕ) (m : M) :
    k ∣ latticeContent (e m) ↔ ∃ w : M, m = (k : ℤ) • w := by
  rw [dvd_latticeContent_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨e.symm w, ?_⟩
    apply e.injective
    simpa only [map_zsmul, e.apply_symm_apply] using hw
  · rintro ⟨w, rfl⟩
    exact ⟨e w, map_zsmul e _ _⟩

/-- The usual gcd length of a lattice segment does not depend on which
integral basis supplies its coordinates. -/
theorem latticeLength_independent_of_basis (e e' : M ≃+ Lattice n) (v w : M) :
    LatticePolytope.latticeLength (e v) (e w) =
      LatticePolytope.latticeLength (e' v) (e' w) := by
  have hlen (g : M ≃+ Lattice n) :
      LatticePolytope.latticeLength (g v) (g w) = latticeContent (g (w - v)) := by
    simp only [LatticePolytope.latticeLength, latticeContent, map_sub, Pi.sub_apply]
  rw [hlen, hlen]
  apply Nat.dvd_antisymm
  · exact (dvd_coordinateContent_iff e' _ (w - v)).mpr
      ((dvd_coordinateContent_iff e _ (w - v)).mp dvd_rfl)
  · exact (dvd_coordinateContent_iff e _ (w - v)).mpr
      ((dvd_coordinateContent_iff e' _ (w - v)).mp dvd_rfl)

/-- Every actual abstract lattice edge corresponds to exactly one actual
coordinate edge, with the same intrinsic lattice length. -/
theorem coordinatePolytope_edgesAtLeast_iff
    (e : M ≃+ Lattice n) (s : Finset M) (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤)
    (bound : ℕ) :
    (coordinatePolytope e s hs hfull).EdgesAtLeast bound ↔
      ∀ v w : M, realificationEmbedding v ≠ realificationEmbedding w →
        IsExtreme ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M)))
          (segment ℝ (realificationEmbedding v) (realificationEmbedding w)) →
        bound ≤ latticeContent (e (w - v)) := by
  let P := convexHull ℝ (realificationEmbedding '' (s : Set M))
  have hedge (v w : M) :
      (coordinatePolytope e s hs hfull).IsEdge (embed n (e v)) (embed n (e w)) ↔
        realificationEmbedding v ≠ realificationEmbedding w ∧
          IsExtreme ℝ P (segment ℝ (realificationEmbedding v) (realificationEmbedding w)) := by
    unfold LatticePolytope.IsEdge
    rw [coordinatePolytope_carrier, realCoordinatesOfEquiv_compatible,
      realCoordinatesOfEquiv_compatible]
    exact edge_image_iff (realCoordinatesOfEquiv e) P _ _
  have hlen (v w : M) :
      LatticePolytope.latticeLength (e v) (e w) = latticeContent (e (w - v)) := by
    simp only [LatticePolytope.latticeLength, latticeContent, map_sub, Pi.sub_apply]
  rw [LatticePolytope.edgesAtLeast_iff]
  constructor
  · intro h v w hne hF
    exact hlen v w ▸ h (e v) (e w) ((hedge v w).mpr ⟨hne, hF⟩)
  · intro h v w hF
    obtain ⟨v', rfl⟩ := e.surjective v
    obtain ⟨w', rfl⟩ := e.surjective w
    obtain ⟨hne, hF⟩ := (hedge v' w').mp hF
    rw [hlen]
    exact h v' w' hne hF

/-- The exact unrestricted IDP statement on an abstract lattice is equivalent
to the coordinate statement used by the principal theorem. -/
theorem lattice_basis_idp_iff (e : M ≃+ Lattice n) (P : Set (ℝ ⊗[ℤ] M)) :
    IntegerDecompositionProperty realificationEmbedding P ↔
      IntegerDecompositionProperty (embed n) (realCoordinatesOfEquiv e '' P) :=
  integerDecompositionProperty_iff realificationEmbedding (embed n) e
    (realCoordinatesOfEquiv e) (realCoordinatesOfEquiv_compatible e) P

/-- The exact paper-kernel quadratic-generation statement on an abstract
lattice is equivalent to the coordinate assertion, with all lattice points
and every polynomial degree retained. -/
theorem lattice_basis_quadratic_generation_iff
    (e : M ≃+ Lattice n) (P : Set (ℝ ⊗[ℤ] M))
    (R : Type*) [CommRing R] :
    RingHom.ker (paperToricMap (latticePoints realificationEmbedding P) R) =
        polynomialQuadraticIdeal (latticePoints realificationEmbedding P) R ↔
      RingHom.ker (paperToricMap
        (latticePoints (embed n) (realCoordinatesOfEquiv e '' P)) R) =
        polynomialQuadraticIdeal
          (latticePoints (embed n) (realCoordinatesOfEquiv e '' P)) R :=
  quadratic_generation_iff e
    (latticePoints_compatible_image realificationEmbedding (embed n) e
      (realCoordinatesOfEquiv e) (realCoordinatesOfEquiv_compatible e) P) R

/-- Both principal conclusions for the coordinate polytope are exactly the
paper's conclusions for the original abstract lattice and its realification. -/
theorem coordinatePolytope_principal_conclusions_iff
    (e : M ≃+ Lattice n) (s : Finset M) (hs : s.Nonempty)
    (hfull : affineSpan ℝ (convexHull ℝ (realificationEmbedding '' (s : Set M))) = ⊤)
    (R : Type*) [CommRing R] :
    ((coordinatePolytope e s hs hfull).HasIDP ∧
      (coordinatePolytope e s hs hfull).QuadraticallyGenerated R) ↔
      (IntegerDecompositionProperty realificationEmbedding
          (convexHull ℝ (realificationEmbedding '' (s : Set M))) ∧
        RingHom.ker (paperToricMap (latticePoints realificationEmbedding
          (convexHull ℝ (realificationEmbedding '' (s : Set M)))) R) =
          polynomialQuadraticIdeal (latticePoints realificationEmbedding
            (convexHull ℝ (realificationEmbedding '' (s : Set M)))) R) := by
  apply and_congr
  · change IntegerDecompositionProperty (embed n) (coordinatePolytope e s hs hfull).carrier ↔ _
    rw [coordinatePolytope_carrier]
    exact (lattice_basis_idp_iff e _).symm
  · let Q (A : Set (Ambient n)) : Prop :=
      RingHom.ker (paperToricMap (latticePoints (embed n) A) R) =
        polynomialQuadraticIdeal (latticePoints (embed n) A) R
    have hc : Q (coordinatePolytope e s hs hfull).carrier =
        Q (realCoordinatesOfEquiv e ''
          convexHull ℝ (realificationEmbedding '' (s : Set M))) :=
      congrArg Q (coordinatePolytope_carrier e s hs hfull)
    exact (iff_of_eq hc).trans (lattice_basis_quadratic_generation_iff e _ R).symm

end Realification

end PaperVerification.ToricCoordinateTransport
