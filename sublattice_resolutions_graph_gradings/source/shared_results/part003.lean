module
public import graph_foundation.part007
public import shared_results.part002

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.DeformationTransport -/
section

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.HomologicalPerturbation.LinearDeformationRetract
variable {R M N H K : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup H] [Module R H] [AddCommGroup K] [Module R K]

def changeTarget (C : LinearDeformationRetract (R:=R) (M:=M) (H:=H)) (e : H≃ₗ[R] K) :
    LinearDeformationRetract (R:=R) (M:=M) (H:=K) where
  sourceD := C.sourceD
  targetD := e.toLinearMap.comp (C.targetD.comp e.symm.toLinearMap)
  inclusion := C.inclusion.comp e.symm.toLinearMap
  projection := e.toLinearMap.comp C.projection
  homotopy := C.homotopy
  source_square := C.source_square
  target_square := by
    ext x
    change e (C.targetD (e.symm (e (C.targetD (e.symm x)))))=0
    have hsq : C.targetD (C.targetD (e.symm x)) = 0 := by
      simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun C.target_square (e.symm x)
    rw [e.symm_apply_apply, hsq, map_zero]
  inclusion_chain := by
    ext x
    change C.sourceD (C.inclusion (e.symm x))=
      C.inclusion (e.symm (e (C.targetD (e.symm x))))
    rw [e.symm_apply_apply,C.inclusion_differential]
  projection_chain := by
    ext x
    change e (C.projection (C.sourceD x))=
      e (C.targetD (e.symm (e (C.projection x))))
    rw [e.symm_apply_apply,C.projection_differential]
  retract := by
    ext x
    change e (C.projection (C.inclusion (e.symm x)))=x
    rw [C.projection_inclusion,e.apply_symm_apply]
  deformation := by
    rw [C.deformation]
    congr 1
    ext x
    change C.inclusion (C.projection x)=C.inclusion (e.symm (e (C.projection x)))
    rw [e.symm_apply_apply]

def changeSource (C : LinearDeformationRetract (R:=R) (M:=M) (H:=H)) (e : M≃ₗ[R] N) :
    LinearDeformationRetract (R:=R) (M:=N) (H:=H) where
  sourceD := e.toLinearMap.comp (C.sourceD.comp e.symm.toLinearMap)
  targetD := C.targetD
  inclusion := e.toLinearMap.comp C.inclusion
  projection := C.projection.comp e.symm.toLinearMap
  homotopy := e.toLinearMap.comp (C.homotopy.comp e.symm.toLinearMap)
  source_square := by
    ext x
    change e (C.sourceD (e.symm (e (C.sourceD (e.symm x)))))=0
    have hsq : C.sourceD (C.sourceD (e.symm x)) = 0 := by
      simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun C.source_square (e.symm x)
    rw [e.symm_apply_apply, hsq, map_zero]
  target_square := C.target_square
  inclusion_chain := by
    ext x
    change e (C.sourceD (e.symm (e (C.inclusion x))))=e (C.inclusion (C.targetD x))
    rw [e.symm_apply_apply,C.inclusion_differential]
  projection_chain := by
    ext x
    change C.projection (e.symm (e (C.sourceD (e.symm x))))=C.targetD (C.projection (e.symm x))
    rw [e.symm_apply_apply,C.projection_differential]
  retract := by
    ext x
    change C.projection (e.symm (e (C.inclusion x)))=x
    rw [e.symm_apply_apply,C.projection_inclusion]
  deformation := by
    ext x
    change e (C.sourceD (e.symm (e (C.homotopy (e.symm x)))))+
      e (C.homotopy (e.symm (e (C.sourceD (e.symm x)))))=
        x-e (C.inclusion (C.projection (e.symm x)))
    rw [e.symm_apply_apply,e.symm_apply_apply,← map_add]
    have he := LinearMap.congr_fun C.deformation (e.symm x)
    change C.sourceD (C.homotopy (e.symm x))+C.homotopy (C.sourceD (e.symm x))=
      e.symm x-C.inclusion (C.projection (e.symm x)) at he
    rw [he,map_sub,e.apply_symm_apply]

end FourPapers.HomologicalPerturbation.LinearDeformationRetract

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ExteriorWordUnit -/
section

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CliffordAlgebra
universe u v w
variable {R : Type u} [CommRing R] {I : Type v} [LinearOrder I]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Any ordering of a set of distinct exterior generators differs from the
chosen basis orientation by an explicit integral unit. This allows the graph
variable order to be arbitrary. -/
theorem exterior_word_unit_basis (b : Module.Basis I R M) (L : List I) (hL : L.Nodup) :
    ∃ ε : ℤˣ, (L.map (fun i => ExteriorAlgebra.ι R (b i))).prod =
      ε • b.ExteriorAlgebra L.toFinset := by
  induction L with
  | nil =>
    refine ⟨1, ?_⟩
    simp [Module.Basis.exteriorAlgebra_eq_prod_map_sort]
  | cons i L ih =>
    obtain ⟨ε, hε⟩ := ih (List.nodup_cons.mp hL).2
    have hi : i ∉ L.toFinset := by simpa using (List.nodup_cons.mp hL).1
    refine ⟨ε * TauCeti.ExteriorAlgebra.basisEraseSign i (insert i L.toFinset), ?_⟩
    rw [List.map_cons, List.prod_cons, hε, mul_smul_comm,
      TauCeti.ExteriorAlgebra.ι_mul_basis, if_neg hi, smul_smul]
    simp only [List.toFinset_cons]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.HomogeneousCycleSpanning -/
section

/-! # Homogeneous projection and cycle spanning in a based complex -/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg
variable {R M I T : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Projecting an actual differential to exterior degree p agrees with first
projecting its input to exterior degree p+1. Degree zero is dealt with explicitly. -/
lemma homogeneous_projection_lowering
    (b : Module.Basis I R M) (deg : I → ℕ) (D : Module.End R M)
    (hlower : ∀ i, D (b i) ∈ Grading.Piece b deg (deg i - 1))
    (hzero : ∀ i, deg i = 0 → D (b i) = 0) (p : ℕ) :
    D.comp (Grading.projection b deg (p + 1)) =
      (Grading.projection b deg p).comp D := by
  apply b.ext
  intro i
  simp only [LinearMap.comp_apply, Grading.projection_basis]
  by_cases hi : deg i = p + 1
  · rw [if_pos hi]
    exact (Grading.projection_eq_self (by simpa only [hi, Nat.add_sub_cancel] using hlower i)).symm
  · rw [if_neg hi, map_zero]
    by_cases h0 : deg i = 0
    · rw [hzero i h0, map_zero]
    · exact (Grading.projection_eq_zero (by omega) (hlower i)).symm

/-- Homogeneous cycle representatives follow from total cycle generation by
homogeneous elements. Both the representative and its boundary filling retain
the exact requested exterior degree. -/
theorem homogeneous_cycle_spanning
    (b : Module.Basis I R M) (deg : I → ℕ) (D : Module.End R M)
    (hlower : ∀ i, D (b i) ∈ Grading.Piece b deg (deg i - 1))
    (hzero : ∀ i, deg i = 0 → D (b i) = 0)
    (v : T → M) (vdeg : T → ℕ)
    (hv : ∀ t, v t ∈ Grading.Piece b deg (vdeg t))
    (hspan : LinearMap.ker D ≤ Submodule.span R (Set.range v) ⊔ LinearMap.range D)
    (p : ℕ) (z : M) (hzp : z ∈ Grading.Piece b deg p) (hz : D z = 0) :
    ∃ g, g ∈ Submodule.span R (v '' {t | vdeg t = p}) ∧
      ∃ y, y ∈ Grading.Piece b deg (p + 1) ∧ g + D y = z := by
  let P := Submodule.span R (v '' {t | vdeg t = p})
  let π := Grading.projection b deg p
  have hP : Submodule.span R (Set.range v) ≤ P.comap π := by
    apply Submodule.span_le.mpr
    rintro x ⟨t, rfl⟩
    change π (v t) ∈ P
    by_cases ht : vdeg t = p
    · have h := Grading.projection_eq_self (ht ▸ hv t)
      change π (v t) = v t at h
      rw [h]
      exact Submodule.subset_span ⟨t, ht, rfl⟩
    · have h := Grading.projection_eq_zero (Ne.symm ht) (hv t)
      change π (v t) = 0 at h
      rw [h]
      exact P.zero_mem
  obtain ⟨g, hg, dy, ⟨y, rfl⟩, hgy⟩ := Submodule.mem_sup.mp (hspan hz)
  refine ⟨π g, hP hg, Grading.projection b deg (p + 1) y,
    Grading.projection_mem _ _ _ _, ?_⟩
  have hc := LinearMap.congr_fun (homogeneous_projection_lowering b deg D hlower hzero p) y
  change D (Grading.projection b deg (p + 1) y) = π (D y) at hc
  rw [hc, ← map_add, hgy]
  exact Grading.projection_eq_self hzp

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.NatIntegerRegrade -/
section

/-! # Regrading natural-number basis pieces by integer degrees

Regrading along the injective map `ℕ → ℤ` preserves every natural-degree
piece and has no negative pieces. The basis-piece theorem identifies the
result with the literal integer-valued degree of the original basis.
This module has no dependency on graph or ideal-coordinate constructions.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg

section Regrading

variable {K M I : Type*} [CommRing K] [AddCommMonoid M] [Module K M]

def ordinaryIntegerRegrade (A : ℕ → Submodule K M) (q : ℤ) : Submodule K M :=
  ⨆ n : ℕ, ⨆ (_ : (n : ℤ) = q), A n

@[simp] theorem ordinaryIntegerRegrade_nat (A : ℕ → Submodule K M) (n : ℕ) :
    ordinaryIntegerRegrade A (n : ℤ) = A n := by
  apply le_antisymm
  · apply iSup_le
    intro m
    apply iSup_le
    intro h
    obtain rfl := Int.ofNat_inj.mp h
    exact le_rfl
  · exact le_iSup_of_le n (le_iSup_of_le rfl le_rfl)

theorem ordinaryIntegerRegrade_eq_bot_of_not_image (A : ℕ → Submodule K M)
    (q : ℤ) (hq : ¬∃ n : ℕ, (n : ℤ) = q) : ordinaryIntegerRegrade A q = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro n
  apply iSup_le
  intro h
  exact (hq ⟨n, h⟩).elim

theorem ordinaryIntegerRegrade_negative (A : ℕ → Submodule K M)
    (q : ℤ) (hq : q < 0) : ordinaryIntegerRegrade A q = ⊥ := by
  apply ordinaryIntegerRegrade_eq_bot_of_not_image
  rintro ⟨n, rfl⟩
  exact (not_lt_of_ge (Int.ofNat_nonneg n)) hq

/-- This is the usual integer degree on basis vectors, rather than a
separate convention assigning zero to unsupported degrees. -/
theorem ordinaryIntegerRegrade_basisPiece (b : Module.Basis I K M)
    (degree : I → ℕ) (q : ℤ) :
    ordinaryIntegerRegrade (Grading.Piece b degree) q =
      Grading.Piece b (fun i => (degree i : ℤ)) q := by
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    rw [ordinaryIntegerRegrade_nat]
    unfold Grading.Piece
    congr 1
    congr 1
    ext i
    exact Int.ofNat_inj.symm
  · rw [ordinaryIntegerRegrade_eq_bot_of_not_image _ _ hq]
    have hs : {i | (degree i : ℤ) = q} = (∅ : Set I) := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hq ⟨degree i, h⟩
    change ⊥ = Submodule.span K (b '' {i | (degree i : ℤ) = q})
    rw [hs]
    simp

end Regrading

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.BasisGradingDecomposition -/
section

/-! # Actual direct-sum decompositions from assigned basis degrees -/

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

open Classical CommAlg DirectSum

variable {R M I Γ : Type*} [CommRing R] [AddCommMonoid M] [Module R M] [DecidableEq Γ]
  (b : Module.Basis I R M) (degree : I → Γ)

def basisGradeDecompose : M →ₗ[R] ⨁ q, Grading.Piece b degree q :=
  (Finsupp.linearCombination R (fun i => DirectSum.lof R Γ
    (fun q => Grading.Piece b degree q) (degree i)
      ⟨b i,Grading.basis_mem_piece b degree i⟩)).comp b.repr.toLinearMap

@[simp] theorem basisGradeDecompose_basis (i : I) :
    basisGradeDecompose b degree (b i) = DirectSum.lof R Γ
      (fun q => Grading.Piece b degree q) (degree i)
        ⟨b i,Grading.basis_mem_piece b degree i⟩ := by
  simp only [basisGradeDecompose,LinearMap.comp_apply,LinearEquiv.coe_coe,
    Module.Basis.repr_self,Finsupp.linearCombination_single,one_smul]

theorem basisGradeDecompose_homogeneous (q : Γ) (x : Grading.Piece b degree q) :
    basisGradeDecompose b degree x.val = DirectSum.lof R Γ
      (fun q => Grading.Piece b degree q) q x := by
  have he : (basisGradeDecompose b degree).comp (Grading.Piece b degree q).subtype =
      DirectSum.lof R Γ (fun q => Grading.Piece b degree q) q := by
    let bq : Module.Basis {i // degree i=q} R (Grading.Piece b degree q) :=
      Grading.restrictedBasis b (fun i => degree i=q)
    have hbq (i : {i // degree i=q}) : (bq i).val = b i.val :=
      Grading.restrictedBasis_val b (fun i => degree i=q) i
    apply bq.ext
    intro i
    change basisGradeDecompose b degree (bq i).val =
      DirectSum.lof R Γ (fun q => Grading.Piece b degree q) q (bq i)
    rw [hbq,basisGradeDecompose_basis]
    rcases i with ⟨i,hi⟩
    subst q
    apply congrArg (DirectSum.lof R Γ (fun q => Grading.Piece b degree q) (degree i))
    apply Subtype.ext
    exact (hbq ⟨i,rfl⟩).symm
  exact LinearMap.congr_fun he x

def basisGradingDecomposition : DirectSum.Decomposition (Grading.Piece b degree) :=
  DirectSum.Decomposition.ofLinearMap (Grading.Piece b degree) (basisGradeDecompose b degree)
    (by
      apply b.ext
      intro i
      rw [LinearMap.comp_apply,basisGradeDecompose_basis,DirectSum.coeLinearMap_lof]
      rfl)
    (by
      apply DirectSum.linearMap_ext
      intro q
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply,DirectSum.coeLinearMap_lof,
        basisGradeDecompose_homogeneous,LinearMap.id_apply])

theorem restrictedBasis_repr (Q : I → Prop)
    (x : Submodule.span R (b '' {i | Q i})) (i : {i : I // Q i}) :
    (Grading.restrictedBasis b Q).repr x i = b.repr x.val i.val := by
  have he : (Grading.restrictedBasis b Q).coord i =
      (b.coord i.val).comp (Submodule.span R (b '' {i | Q i})).subtype := by
    apply (Grading.restrictedBasis b Q).ext
    intro j
    simp only [Module.Basis.coord_apply,LinearMap.comp_apply,Submodule.subtype_apply,
      Grading.restrictedBasis_val,Module.Basis.repr_self,Finsupp.single_apply]
    simp only [Subtype.ext_iff]
  exact LinearMap.congr_fun he x

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ProjectedFreeResolution -/
section

/-!
# An actual finite free resolution from a split graded total complex

The source module has a genuine basis with nonnegative homological degrees.
The differential lowers that degree, and its degree-zero part is zero.
An actual coefficient-linear split augmentation supplies exactness. Boundary
preimages are projected to the next homological degree, so no grading
assumption on the chosen splitting homotopy is needed.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.ProjectedFreeResolution

open Classical CommAlg CategoryTheory HomologicalComplex

universe u
variable {R S F M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module S F] [Module R F] [IsScalarTower R S F]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  {I : Type*} (b : Module.Basis I S F) (degree : I → ℕ)
  (D : Module.End S F) (ε : F →ₗ[S] M)
  (C : HomologicalPerturbation.LinearDeformationRetract (R := R) (M := F) (H := M))
  (hD : C.sourceD = D.restrictScalars R)
  (hε : C.projection = ε.restrictScalars R)
  (ht : C.targetD = 0)

abbrev piece (p : ℕ) := Grading.Piece b degree p
abbrev projection (p : ℕ) := Grading.projection b degree p

variable
  (hlower : ∀ p, D.comp (projection b degree (p+1)) = (projection b degree p).comp D)
  (hzero : D.comp (projection b degree 0) = 0)
  (hεzero : ε.comp (projection b degree 0) = ε)

include C hD in
theorem differential_square : D.comp D = 0 := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun C.source_square x
  rw [hD] at h
  exact h

include hlower in
theorem differential_mem (p : ℕ) (x : F) (hx : x ∈ piece b degree (p+1)) :
    D x ∈ piece b degree p := by
  have he := LinearMap.congr_fun (hlower p) x
  change D (projection b degree (p+1) x) = projection b degree p (D x) at he
  rw [Grading.projection_eq_self hx] at he
  rw [he]
  exact Grading.projection_mem _ _ _ _

def data : SubmoduleComplexData S F where
  piece := piece b degree
  d := D
  square_zero := differential_square D C hD
  lowers := differential_mem b degree D hlower

def complex : ChainComplex (ModuleCat.{u} S) ℕ :=
  (data b degree D C hD hlower).complex

def pieceBasis (p : ℕ) : Module.Basis {i : I // degree i = p} S (piece b degree p) :=
  Grading.restrictedBasis b (fun i => degree i = p)

@[simp] theorem pieceBasis_val (p : ℕ) (i : {i : I // degree i = p}) :
    (pieceBasis b degree p i).val = b i.val :=
  Grading.restrictedBasis_val b (fun i => degree i = p) i

theorem pieceBasis_repr (p : ℕ) (x : piece b degree p)
    (i : {i : I // degree i = p}) :
    (pieceBasis b degree p).repr x i = b.repr x.val i.val := by
  have he : (pieceBasis b degree p).coord i =
      (b.coord i.val).comp (piece b degree p).subtype := by
    apply (pieceBasis b degree p).ext
    intro j
    simp only [Module.Basis.coord_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, pieceBasis_val, Module.Basis.repr_self,
      Finsupp.single_apply]
    simp only [Subtype.ext_iff]
  exact LinearMap.congr_fun he x

theorem piece_free (p : ℕ) : Module.Free S (piece b degree p) :=
  Module.Free.of_basis (pieceBasis b degree p)

theorem piece_finite [Finite I] (p : ℕ) : Module.Finite S (piece b degree p) :=
  Module.Finite.of_basis (pieceBasis b degree p)

theorem piece_zero_above (N : ℕ) (hN : ∀ i, degree i ≤ N) (p : ℕ) (hp : N < p) :
    Subsingleton (piece b degree p) := by
  have hempty : {i : I | degree i = p} = ∅ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hi
    exact Nat.not_lt_of_ge (hi ▸ hN i) hp
  have hbot : piece b degree p = ⊥ := by
    change Submodule.span S (b '' {i : I | degree i = p}) = ⊥
    rw [hempty, Set.image_empty, Submodule.span_empty]
  rw [hbot]
  infer_instance

include hzero in
theorem zero_degree_cycle (x : piece b degree 0) : D x.val = 0 := by
  have he := LinearMap.congr_fun hzero x.val
  simpa only [LinearMap.comp_apply, Grading.projection_eq_self x.property,
    LinearMap.zero_apply] using he

include hεzero in
theorem augmentation_positive (p : ℕ) (x : piece b degree (p+1)) : ε x.val = 0 := by
  have he := LinearMap.congr_fun hεzero x.val
  change ε (projection b degree 0 x.val) = ε x.val at he
  rw [Grading.projection_eq_zero (Nat.zero_ne_add_one p) x.property, map_zero] at he
  exact he.symm

include C hD hε ht in
theorem augmentation_boundary : ε.comp D = 0 := by
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun C.projection_chain x
  rw [hD, hε, ht] at he
  exact he

def augmentationZero : piece b degree 0 →ₗ[S] M := ε.domRestrict (piece b degree 0)

include C hε hεzero in
theorem augmentationZero_surjective :
    Function.Surjective (augmentationZero b degree ε) := by
  intro m
  refine ⟨⟨projection b degree 0 (C.inclusion m), Grading.projection_mem _ _ _ _⟩, ?_⟩
  change ε (projection b degree 0 (C.inclusion m)) = m
  have hz := LinearMap.congr_fun hεzero (C.inclusion m)
  change ε (projection b degree 0 (C.inclusion m)) = ε (C.inclusion m) at hz
  rw [hz]
  have he := C.projection_inclusion m
  rw [hε] at he
  exact he

include hD hε in
theorem cycle_boundary (x : F) (hx : D x = 0) (hex : ε x = 0) : D (C.homotopy x) = x := by
  have he := LinearMap.congr_fun C.deformation x
  rw [hD, hε] at he
  change D (C.homotopy x) + C.homotopy (D x) = x - C.inclusion (ε x) at he
  simpa only [hx, hex, map_zero, add_zero, sub_zero] using he

include hε in
/-- Projecting a boundary preimage provides an actual homogeneous preimage
in the immediately preceding term of the resolution. -/
theorem homogeneous_boundary (p : ℕ) (x : piece b degree p)
    (hx : D x.val = 0) (hex : ε x.val = 0) :
    ∃ y : piece b degree (p+1), (data b degree D C hD hlower).differential p y = x := by
  refine ⟨⟨projection b degree (p+1) (C.homotopy x.val),
    Grading.projection_mem _ _ _ _⟩, ?_⟩
  apply Subtype.ext
  change D (projection b degree (p+1) (C.homotopy x.val)) = x.val
  have he := LinearMap.congr_fun (hlower p) (C.homotopy x.val)
  change D (projection b degree (p+1) (C.homotopy x.val)) =
    projection b degree p (D (C.homotopy x.val)) at he
  rw [he, cycle_boundary D ε C hD hε x.val hx hex,
    Grading.projection_eq_self x.property]

include ε hε hεzero in
theorem exact_positive (p : ℕ) : (complex b degree D C hD hlower).ExactAt (p+1) := by
  apply ((complex b degree D C hD hlower).exactAt_iff' (p+2) (p+1) p
    (by simp) (by simp)).mpr
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hdx : D x.val = 0 := by
    change (data b degree D C hD hlower).complex.d (p+1) p x = 0 at hx
    rw [SubmoduleComplexData.complex_d] at hx
    exact congrArg Subtype.val hx
  obtain ⟨y,hy⟩ := homogeneous_boundary b degree D ε C hD hε hlower (p+1) x hdx
    (augmentation_positive b degree ε hεzero p x)
  refine ⟨y, ?_⟩
  change (data b degree D C hD hlower).complex.d (p+2) (p+1) y = x
  rw [SubmoduleComplexData.complex_d]
  exact hy

include hε ht in
theorem augmentationZero_comp :
    (augmentationZero b degree ε).comp ((data b degree D C hD hlower).differential 0) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (augmentation_boundary D ε C hD hε ht) x.val

include hzero hε ht in
theorem exact_at_augmentation :
    (ShortComplex.moduleCatMk ((data b degree D C hD hlower).differential 0)
      (augmentationZero b degree ε)
      (augmentationZero_comp b degree D ε C hD hε ht hlower)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact homogeneous_boundary b degree D ε C hD hε hlower 0 x
    (zero_degree_cycle b degree D hzero x) hx

/-- The displayed chain complex is a genuine Mathlib projective resolution
of the original module. Every term has the explicit restricted free basis. -/
def resolution : ProjectiveResolution (ModuleCat.of S M) where
  complex := complex b degree D C hD hlower
  projective p := by
    change CategoryTheory.Projective (ModuleCat.of S (piece b degree p))
    exact ModuleCat.projective_of_free (pieceBasis b degree p)
  π := (ChainComplex.toSingle₀Equiv (complex b degree D C hD hlower) _).symm
    ⟨ModuleCat.ofHom (augmentationZero b degree ε), by
      rw [show (complex b degree D C hD hlower).d 1 0 =
          ModuleCat.ofHom ((data b degree D C hD hlower).differential 0) from
        SubmoduleComplexData.complex_d _ 0]
      exact ModuleCat.hom_ext (augmentationZero_comp b degree D ε C hD hε ht hlower)⟩
  quasiIso := ⟨fun p => by
    cases p with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · dsimp
          simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
          refine ⟨?_, ?_⟩
          · exact exact_at_augmentation b degree D ε C hD hε ht hlower hzero
          · exact (ModuleCat.epi_iff_surjective _).mpr
              (augmentationZero_surjective b degree ε C hε hεzero)
        · exact (complex b degree D C hD hlower).shape 0 0 (by simp)
        all_goals rfl
    | succ p =>
        rw [quasiIsoAt_iff_exactAt']
        · exact exact_positive b degree D ε C hD hε hlower hεzero p
        · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- The actual degree-zero augmentation of the constructed resolution is
the displayed restricted augmentation, with no further coordinate change. -/
@[simp] theorem resolution_π_f_zero :
    (resolution b degree D ε C hD hε ht hlower hzero hεzero).π.f 0 =
      ModuleCat.ofHom (augmentationZero b degree ε) := by
  unfold resolution
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

include D ε C hD hε ht hlower hzero hεzero in
/-- A bound on the actual homology-basis degrees bounds the genuine
projective dimension through the constructed free resolution. -/
theorem projectiveDimension_le (N : ℕ) (hN : ∀ i, degree i ≤ N) :
    CategoryTheory.projectiveDimension (ModuleCat.of S M) ≤ (N : WithBot ℕ∞) := by
  apply FourPapers.projectiveDimension_le_of_bounded_resolution
    (resolution b degree D ε C hD hε ht hlower hzero hεzero) N
  intro p hp
  letI : Subsingleton
      ((resolution b degree D ε C hD hε ht hlower hzero hεzero).complex.X p) := by
    change Subsingleton (piece b degree p)
    exact piece_zero_above b degree N hN p hp
  apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

end FourPapers.ProjectedFreeResolution

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientTotalHomology -/
section

/-! # The actual total homology of a fine quotient Koszul strand -/
section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {k : Type u} [CommRing k]

/-- Actual total Koszul homology of one fine strand. Exterior degree is retained
by the chain grading; taking this total quotient is convenient for the integral
recursion and does not identify distinct fine degrees. -/
def ClosedGraphFaceHomology {V : Type u} [Fintype V] [LinearOrder V]
    (B : Family V) (α : Exponent V) :=
  Homology (quotientTotalDifferential (k := k) B α)
    (quotientTotalDifferential B α) (quotientTotalDifferential_comp B α)

/-- Canonical group structure on the literal homology quotient. -/
instance closedGraphFaceHomologyAddCommGroup {V : Type u} [Fintype V] [LinearOrder V]
    (B : Family V) (α : Exponent V) :
    AddCommGroup (ClosedGraphFaceHomology (k := k) B α) := by
  unfold ClosedGraphFaceHomology
  infer_instance

/-- Canonical coefficient action on the same quotient. -/
instance closedGraphFaceHomologyModule {V : Type u} [Fintype V] [LinearOrder V]
    (B : Family V) (α : Exponent V) :
    Module k (ClosedGraphFaceHomology (k := k) B α) := by
  unfold ClosedGraphFaceHomology
  infer_instance

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientZeroFaces -/
section

/-! # The zero fine strand of a proper monomial quotient

At exponent zero the empty exterior face is the unique surviving face.
This elementary fact is shared by the integral recursion and the proof
that the regularity support of a nonzero ideal power is nonempty.
-/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V : Type u} [Fintype V] [LinearOrder V]

lemma quotientKoszulFaces_zero_iff (B : Family V) (hB : ¬Contains B 0) (F : Finset V) :
    quotientKoszulFaces B 0 F ↔ F = ∅ := by
  constructor
  · intro hF
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := hF.1 v
    simp [faceExponent_apply, hv] at hh
  · rintro rfl
    exact ⟨by simp [fullKoszulFaces], by simpa only [forbiddenKoszulFaces, faceExponent_empty, tsub_self] using hB⟩

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedColorCoefficients -/
section

/-!
# Literal mixed coefficients of powers of the colored ideal

For arbitrary ideals I_c in any commutative ring R, put
K = (z_c f : f in I_c) in R[z]. The component of K^n in a color
multidegree m of total degree n is exactly z^m times the actual product
of the powers I_c^(m_c). The proofs use ideal membership and polynomial
coefficients, so apply equally to the monomial and deformed ideals.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial

variable {C R : Type*} [Fintype C] [DecidableEq C] [CommRing R]

@[simp] theorem powerProduct_single (I : C → Ideal R) (c : C) (n : ℕ) :
    powerProduct I (Finsupp.single c n) = (I c)^n := by
  classical
  unfold powerProduct
  calc
    (∏ x, (I x) ^ (Finsupp.single c n) x) =
        ∏ x, if c = x then (I x)^n else 1 := by
      apply Finset.prod_congr rfl
      intro x hx
      by_cases h : c = x <;> simp only [Finsupp.single_apply, h, if_true, if_false, pow_zero]
    _ = (I c)^n := Fintype.prod_ite_eq c (fun x => (I x)^n)

/-- The actual colored ideal, with arbitrary coefficients from each I_c. -/
def coloredIdeal (I : C → Ideal R) : Ideal (MvPolynomial C R) :=
  Ideal.span {p | ∃ c, ∃ f ∈ I c, p = monomial (Finsupp.single c 1) f}

theorem coloredIdeal_generator (I : C → Ideal R) (c : C) (f : R) (hf : f ∈ I c) :
    monomial (Finsupp.single c 1) f ∈ coloredIdeal I :=
  Ideal.subset_span ⟨c,f,hf,rfl⟩

/-- Replacing each coefficient ideal by a generating set gives exactly
its color-tagged generating set; scalar coefficients remain literal. -/
theorem coloredIdeal_span (B : C → Set R) :
    coloredIdeal (fun c => Ideal.span (B c)) =
      Ideal.span {p : MvPolynomial C R | ∃ c, ∃ f ∈ B c,
        p = monomial (Finsupp.single c 1) f} := by
  let P : Ideal (MvPolynomial C R) := Ideal.span
    {p : MvPolynomial C R | ∃ c, ∃ f ∈ B c, p = monomial (Finsupp.single c 1) f}
  change coloredIdeal (fun c => Ideal.span (B c)) = P
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨c,f,hf,rfl⟩
    induction hf using Submodule.span_induction with
    | mem f hf => exact Ideal.subset_span ⟨c,f,hf,rfl⟩
    | zero =>
        change monomial (Finsupp.single c 1) (0 : R) ∈ P
        rw [map_zero]
        exact P.zero_mem
    | add f g hf hg ihf ihg =>
        change monomial (Finsupp.single c 1) (f+g) ∈ P
        rw [map_add]
        exact P.add_mem ihf ihg
    | smul q f hf ih =>
        change monomial (Finsupp.single c 1) (q*f) ∈ P
        rw [← C_mul_monomial]
        exact P.mul_mem_left (MvPolynomial.C q) ih
  · apply Ideal.span_le.mpr
    rintro _ ⟨c,f,hf,rfl⟩
    exact coloredIdeal_generator _ c f (Ideal.subset_span hf)

/-- All mixed products whose color exponent divides a and whose total
number of chosen factors is n. -/
def mixedCoefficientBound (I : C → Ideal R) (n : ℕ) (a : C →₀ ℕ) : Ideal R :=
  ⨆ b : {b : C →₀ ℕ // b ≤ a ∧ b.degree = n}, powerProduct I b.val

lemma mixedCoefficientBound_mono (I : C → Ideal R) (n : ℕ)
    {a b : C →₀ ℕ} (hab : a ≤ b) :
    mixedCoefficientBound I n a ≤ mixedCoefficientBound I n b := by
  apply iSup_le
  intro c
  exact le_iSup_of_le ⟨c.val,c.property.1.trans hab,c.property.2⟩ le_rfl

lemma powerProduct_le_mixedCoefficientBound (I : C → Ideal R) (a : C →₀ ℕ) :
    powerProduct I a ≤ mixedCoefficientBound I a.degree a :=
  le_iSup_of_le ⟨a,le_rfl,rfl⟩ le_rfl

theorem mixedCoefficientBound_minimal (I : C → Ideal R) (a : C →₀ ℕ) :
    mixedCoefficientBound I a.degree a = powerProduct I a := by
  apply le_antisymm
  · apply iSup_le
    intro b
    have hb : b.val = a := eq_of_le_of_degree_eq b.property.1 b.property.2
    rw [hb]
  · exact powerProduct_le_mixedCoefficientBound I a

theorem mixedCoefficientBound_below (I : C → Ideal R) (n : ℕ)
    (a : C →₀ ℕ) (ha : a.degree < n) : mixedCoefficientBound I n a = ⊥ := by
  apply le_bot_iff.mp
  apply iSup_le
  intro b
  have hh := CommAlg.Polymatroid.degree_mono b.property.1
  rw [b.property.2] at hh
  exact (Nat.not_le_of_lt ha hh).elim

theorem mixedCoefficientBound_mul (I : C → Ideal R) (m n : ℕ)
    (a b : C →₀ ℕ) :
    mixedCoefficientBound I m a * mixedCoefficientBound I n b ≤
      mixedCoefficientBound I (m+n) (a+b) := by
  unfold mixedCoefficientBound
  rw [Ideal.iSup_mul]
  apply iSup_le
  intro c
  rw [Ideal.mul_iSup]
  apply iSup_le
  intro d
  rw [← powerProduct_add]
  exact le_iSup_of_le ⟨c.val+d.val,add_le_add c.property.1 d.property.1,
    by simp only [map_add,c.property.2,d.property.2]⟩ le_rfl

/-- A coefficientwise ideal determined by a monotone family of actual
coefficient ideals. -/
def colorCoefficientIdeal (J : (C →₀ ℕ) → Ideal R)
    (hJ : Monotone J) : Ideal (MvPolynomial C R) where
  carrier := {p | ∀ a, p.coeff a ∈ J a}
  zero_mem' := by intro a; simp
  add_mem' hp hq := by
    intro a
    simpa only [MvPolynomial.coeff_add] using (J a).add_mem (hp a) (hq a)
  smul_mem' f p hp := by
    intro a
    change (f*p).coeff a ∈ J a
    rw [coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1+uv.2=a := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    apply (J a).mul_mem_left
    have hle : uv.2 ≤ a := by
      intro c
      have hh := congrArg (fun b : C →₀ ℕ => b c) he
      simp only [Finsupp.add_apply] at hh
      omega
    exact hJ hle (hp uv.2)

def coloredPowerBound (I : C → Ideal R) (n : ℕ) : Ideal (MvPolynomial C R) :=
  colorCoefficientIdeal (mixedCoefficientBound I n)
    (fun _ _ h => mixedCoefficientBound_mono I n h)

lemma coloredPowerBound_mul (I : C → Ideal R) (m n : ℕ) :
    coloredPowerBound I m * coloredPowerBound I n ≤ coloredPowerBound I (m+n) := by
  apply Ideal.mul_le.mpr
  intro p hp q hq a
  rw [coeff_mul]
  apply Ideal.sum_mem
  intro uv huv
  have he : uv.1+uv.2=a := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  rw [← he]
  exact mixedCoefficientBound_mul I m n uv.1 uv.2 (Ideal.mul_mem_mul (hp uv.1) (hq uv.2))

lemma coloredIdeal_le_bound (I : C → Ideal R) : coloredIdeal I ≤ coloredPowerBound I 1 := by
  apply Ideal.span_le.mpr
  rintro _ ⟨c,f,hf,rfl⟩ a
  by_cases ha : Finsupp.single c 1 = a
  · subst a
    simp only [coeff_monomial, if_true]
    have hh := powerProduct_le_mixedCoefficientBound I (Finsupp.single c 1)
    have hf' : f ∈ powerProduct I (Finsupp.single c 1) := by
      simpa only [powerProduct_single,pow_one] using hf
    simpa only [Finsupp.degree_single] using hh hf' 
  · simp only [coeff_monomial, if_neg ha]
    exact Ideal.zero_mem _

theorem coloredIdeal_power_le_bound (I : C → Ideal R) (n : ℕ) :
    coloredIdeal I ^ n ≤ coloredPowerBound I n := by
  induction n with
  | zero =>
      intro p hp a
      have h : powerProduct I 0 ≤ mixedCoefficientBound I 0 a :=
        le_iSup_of_le ⟨0,zero_le,by simp⟩ le_rfl
      exact h (by simp)
  | succ n ih =>
      rw [pow_succ]
      exact (Ideal.mul_mono ih (coloredIdeal_le_bound I)).trans (coloredPowerBound_mul I n 1)

/-- The forward coefficient assertion includes every polynomial in K^n,
not only products of the chosen generators. -/
theorem coloredIdeal_power_minimal_coeff (I : C → Ideal R) (n : ℕ)
    (p : MvPolynomial C R) (hp : p ∈ coloredIdeal I ^ n)
    (a : C →₀ ℕ) (ha : a.degree=n) : p.coeff a ∈ powerProduct I a := by
  have hh := coloredIdeal_power_le_bound I n hp a
  rw [← ha,mixedCoefficientBound_minimal] at hh
  exact hh

theorem coloredIdeal_power_coeff_below (I : C → Ideal R) (n : ℕ)
    (p : MvPolynomial C R) (hp : p ∈ coloredIdeal I ^ n)
    (a : C →₀ ℕ) (ha : a.degree<n) : p.coeff a = 0 := by
  have hh := coloredIdeal_power_le_bound I n hp a
  rw [mixedCoefficientBound_below I n a ha] at hh
  exact hh

/-- The reverse coefficient assertion: every element of the literal mixed
product supplies the corresponding color monomial in the ordinary power. -/
theorem monomial_powerProduct_mem_coloredPower (I : C → Ideal R)
    (a : C →₀ ℕ) (f : R) (hf : f ∈ powerProduct I a) :
    monomial a f ∈ coloredIdeal I ^ a.degree := by
  generalize hn : a.degree=n
  induction n generalizing a f with
  | zero => simp only [hn,pow_zero,Ideal.one_eq_top,Submodule.mem_top]
  | succ n ih =>
      have hne : a≠0 := by intro he; simp [he] at hn
      obtain ⟨c,hc⟩ := Finsupp.support_nonempty_iff.mpr hne
      have hcpos : 0<a c := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hc)
      have hs : Finsupp.single c 1 ≤ a := by
        intro j
        by_cases hj : c=j
        · subst j
          simpa only [Finsupp.single_eq_same] using (Nat.succ_le_iff.mpr hcpos)
        · simp [Finsupp.single_apply,hj]
      let b := a-Finsupp.single c 1
      have he : b+Finsupp.single c 1=a := tsub_add_cancel_of_le hs
      have hb : b.degree=n := by
        have hh : b.degree + 1 = n + 1 := by
          simpa only [map_add,Finsupp.degree_single,hn] using
            congrArg (fun t : C →₀ ℕ => t.degree) he
        exact Nat.add_right_cancel hh
      have hprod : powerProduct I a=powerProduct I b*I c := by
        rw [← he,powerProduct_add,powerProduct_single,pow_one]
      rw [hprod] at hf
      refine Submodule.mul_induction_on hf (fun x hx y hy => ?_) (fun x y hx hy => ?_)
      · have hmul := Ideal.mul_mem_mul (ih b x hx hb) (coloredIdeal_generator I c y hy)
        rw [monomial_mul, he] at hmul
        simpa only [hb,hn,← pow_succ] using hmul
      · rw [map_add]
        exact Ideal.add_mem _ hx hy

theorem coloredIdeal_power_minimal_monomial_iff (I : C → Ideal R)
    (a : C →₀ ℕ) (f : R) :
    monomial a f ∈ coloredIdeal I ^ a.degree ↔ f ∈ powerProduct I a := by
  constructor
  · intro h
    simpa only [coeff_monomial,if_true] using
      coloredIdeal_power_minimal_coeff I a.degree (monomial a f) h a rfl
  · exact monomial_powerProduct_mem_coloredPower I a f

/-- The ordinary fine-color homogeneous submodule: all coefficients away
from the prescribed exponent are zero. -/
def pureColorPiece (a : C →₀ ℕ) : Submodule R (MvPolynomial C R) where
  carrier := {p | ∀ b, b≠a → p.coeff b=0}
  zero_mem' := by simp
  add_mem' hp hq := by intro b hb; simp [hp b hb,hq b hb]
  smul_mem' r p hp := by intro b hb; simp [hp b hb]

def coloredPowerPiece (I : C → Ideal R) (a : C →₀ ℕ) :
    Submodule R (MvPolynomial C R) :=
  (coloredIdeal I ^ a.degree).restrictScalars R ⊓ pureColorPiece a

lemma pureColorPiece_eq_monomial (a : C →₀ ℕ) (p : MvPolynomial C R)
    (hp : p ∈ pureColorPiece a) : p=monomial a (p.coeff a) := by
  ext b
  by_cases hb : b=a
  · subst b; simp
  · simp only [coeff_monomial,if_neg (Ne.symm hb),hp b hb]

/-- Exact identification of the minimum-color component with the actual
mixed ideal product. The map is precisely f ↦ z^a f and its inverse reads
the color coefficient. No quotient, flatness, or field assumption occurs. -/
def mixedCoefficientEquiv (I : C → Ideal R) (a : C →₀ ℕ) :
    powerProduct I a ≃ₗ[R] coloredPowerPiece I a where
  toFun f := ⟨monomial a f.val,
    monomial_powerProduct_mem_coloredPower I a f.val f.property,by
      intro b hb
      simp only [coeff_monomial,if_neg (Ne.symm hb)]⟩
  invFun p := ⟨p.val.coeff a,
    coloredIdeal_power_minimal_coeff I a.degree p.val p.property.1 a rfl⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv p := Subtype.ext (pureColorPiece_eq_monomial a p.val p.property.2).symm
  map_add' f g := Subtype.ext (map_add (monomial a) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (monomial a) r f.val)

@[simp] theorem mixedCoefficientEquiv_val (I : C → Ideal R)
    (a : C →₀ ℕ) (f : powerProduct I a) :
    (mixedCoefficientEquiv I a f).val=monomial a f.val := rfl

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.ProjectionRangeBasis -/
section

/-! # A basis for the image of a coordinate projection

The image is the literal range subalgebra of the given algebra map. The
basis consists exactly of the original basis vectors fixed by that map.
-/
section
set_option autoImplicit false
noncomputable section
namespace FourPapers.ProjectionRangeBasis
open Classical
variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (b : Module.Basis I K A) (P : I → Prop) [DecidablePred P] (π : A →ₐ[K] A)
  (hπ : ∀ i, π (b i) = if P i then b i else 0)

include hπ in
lemma range_eq_span : π.range.toSubmodule = Submodule.span K (b '' {i | P i}) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change π x ∈ Submodule.span K (b '' {i | P i})
    have hx : x ∈ Submodule.span K (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [hπ]
        split_ifs with hi
        · exact Submodule.subset_span ⟨i, hi, rfl⟩
        · exact Submodule.zero_mem _
    | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span K (b '' {i | P i})))
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
        rw [map_smul]
        exact Submodule.smul_mem _ c ih
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change P i at hi
    refine ⟨b i, ?_⟩
    change π (b i) = b i
    rw [hπ, if_pos hi]

def basis : Module.Basis {i // P i} K π.range :=
  (CommAlg.Grading.restrictedBasis b P).map
    (LinearEquiv.ofEq _ _ (range_eq_span b P π hπ).symm)

@[simp] lemma basis_val (i : {i // P i}) : (basis b P π hπ i).val = b i.val := by
  change (CommAlg.Grading.restrictedBasis b P i).val = b i.val
  exact CommAlg.Grading.restrictedBasis_val b P i

end FourPapers.ProjectionRangeBasis

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColoredRows -/
section

/-!
# The colored sublattice as an actual additional row

The row of color variables is part of the polynomial ring, and the
polynomial equivalence below sends the literal ideal Σ z_c I_c to the
literal sublattice ideal of the augmented row product.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
universe u
variable {d r : ℕ} (n : Fin d → ℕ)

abbrev coloredRows : Fin (d+1) → ℕ := Fin.cons r n

def coloredTuple (c : Fin r) (a : FiniteTuple n) : FiniteTuple (coloredRows (r := r) n) :=
  Fin.cases c a

@[simp] lemma coloredTuple_zero (c : Fin r) (a : FiniteTuple n) :
    coloredTuple n c a 0=c := rfl
@[simp] lemma coloredTuple_succ (c : Fin r) (a : FiniteTuple n) (i : Fin d) :
    coloredTuple n c a i.succ=a i := rfl

def coloredTupleEquiv : (Fin r × FiniteTuple n) ≃ FiniteTuple (coloredRows (r := r) n) where
  toFun a := coloredTuple n a.1 a.2
  invFun a := (a 0,fun i => a i.succ)
  left_inv _ := rfl
  right_inv a := by funext i; exact Fin.cases rfl (fun _ => rfl) i

theorem coloredTuple_inf (c e : Fin r) (a b : FiniteTuple n) :
    coloredTuple n (c⊓e) (a⊓b)=coloredTuple n c a ⊓ coloredTuple n e b := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem coloredTuple_sup (c e : Fin r) (a b : FiniteTuple n) :
    coloredTuple n (c⊔e) (a⊔b)=coloredTuple n c a ⊔ coloredTuple n e b := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def coloredFamily (E : Fin r → Finset (FiniteTuple n)) :
    Finset (FiniteTuple (coloredRows (r := r) n)) :=
  Finset.univ.biUnion fun c => (E c).image (coloredTuple n c)

@[simp] theorem coloredTuple_mem_family (E : Fin r → Finset (FiniteTuple n))
    (c : Fin r) (a : FiniteTuple n) : coloredTuple n c a ∈ coloredFamily n E ↔ a∈E c := by
  simp only [coloredFamily,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨e,b,hb,he⟩
    have hh : (e,b)=(c,a) := (coloredTupleEquiv n).injective he
    cases hh
    exact hb
  · intro ha
    exact ⟨c,a,ha,rfl⟩

/-- This is precisely the paper's closure condition on (c,a), expressed
without an extra hypothesis on any individual fiber. -/
def ColoredLatticeClosed (E : Fin r → Finset (FiniteTuple n)) : Prop :=
  (∀ c a, a∈E c → ∀ e b, b∈E e → a⊓b∈E (c⊓e)) ∧
  (∀ c a, a∈E c → ∀ e b, b∈E e → a⊔b∈E (c⊔e))

theorem coloredLatticeClosed_iff (E : Fin r → Finset (FiniteTuple n)) :
    ColoredLatticeClosed n E ↔
      finiteLatticeClosed (coloredRows (r := r) n) (coloredFamily n E) := by
  constructor
  · intro h
    constructor
    · intro a ha b hb
      obtain ⟨⟨c,a⟩,rfl⟩ := (coloredTupleEquiv n).surjective a
      obtain ⟨⟨e,b⟩,rfl⟩ := (coloredTupleEquiv n).surjective b
      change coloredTuple n c a ⊓ coloredTuple n e b ∈ coloredFamily n E
      rw [← coloredTuple_inf,coloredTuple_mem_family]
      exact h.1 c a ((coloredTuple_mem_family n E c a).mp ha)
        e b ((coloredTuple_mem_family n E e b).mp hb)
    · intro a ha b hb
      obtain ⟨⟨c,a⟩,rfl⟩ := (coloredTupleEquiv n).surjective a
      obtain ⟨⟨e,b⟩,rfl⟩ := (coloredTupleEquiv n).surjective b
      change coloredTuple n c a ⊔ coloredTuple n e b ∈ coloredFamily n E
      rw [← coloredTuple_sup,coloredTuple_mem_family]
      exact h.2 c a ((coloredTuple_mem_family n E c a).mp ha)
        e b ((coloredTuple_mem_family n E e b).mp hb)
  · intro h
    constructor
    · intro c a ha e b hb
      rw [← coloredTuple_mem_family n E, coloredTuple_inf]
      exact h.1 _ ((coloredTuple_mem_family n E c a).mpr ha)
        _ ((coloredTuple_mem_family n E e b).mpr hb)
    · intro c a ha e b hb
      rw [← coloredTuple_mem_family n E, coloredTuple_sup]
      exact h.2 _ ((coloredTuple_mem_family n E c a).mpr ha)
        _ ((coloredTuple_mem_family n E e b).mpr hb)

def coloredVariableEquiv :
    (ULift.{u} (Fin r) ⊕ FiniteVariable.{u} n) ≃
      FiniteVariable.{u} (coloredRows (r := r) n) where
  toFun := Sum.elim (fun c => ⟨0,c⟩) (fun v => ⟨v.1.succ,v.2⟩)
  invFun v := Fin.cases (fun c => Sum.inl c)
    (fun i c => Sum.inr ⟨i,c⟩) v.1 v.2
  left_inv v := by rcases v with c | ⟨i,j⟩ <;> rfl
  right_inv v := by
    rcases v with ⟨i,j⟩
    revert j
    exact Fin.cases (fun _ => rfl) (fun _ _ => rfl) i

variable {k : Type u} [CommRing k]

def coloredPolynomialEquiv :
    MvPolynomial (ULift.{u} (Fin r)) (MvPolynomial (FiniteVariable.{u} n) k) ≃ₐ[k]
      MvPolynomial (FiniteVariable.{u} (coloredRows (r := r) n)) k :=
  (sumAlgEquiv k (ULift.{u} (Fin r)) (FiniteVariable.{u} n)).symm.trans
    (renameEquiv k (coloredVariableEquiv n))

@[simp] theorem coloredPolynomialEquiv_X (c : ULift.{u} (Fin r)) :
    coloredPolynomialEquiv (k := k) n (X c)=X ⟨0,c⟩ := by
  simp [coloredPolynomialEquiv,coloredVariableEquiv]

@[simp] theorem coloredPolynomialEquiv_C_X (v : FiniteVariable.{u} n) :
    coloredPolynomialEquiv (r := r) (k := k) n (C (X v)) =
      X (⟨v.1.succ,v.2⟩ : FiniteVariable.{u} (coloredRows (r := r) n)) := by
  simp [coloredPolynomialEquiv,coloredVariableEquiv]

lemma coloredPolynomialEquiv_row (c : Fin r) (a : FiniteTuple n) :
    coloredPolynomialEquiv (k := k) n
      (monomial (Finsupp.single (ULift.up c) 1) (finiteRowMonomial n a))=
        finiteRowMonomial (coloredRows (r := r) n) (coloredTuple n c a) := by
  have he : monomial (Finsupp.single (ULift.up c) 1) (finiteRowMonomial n (k := k) a)=
      X (ULift.up c) * C (finiteRowMonomial n a) := by simp [X,C_mul_monomial,mul_comm]
  rw [he,map_mul]
  simp only [finiteRowMonomial,map_prod,coloredPolynomialEquiv_X]
  rw [Fin.prod_univ_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact coloredPolynomialEquiv_C_X n ⟨i,ULift.up (a i)⟩

/-- The fibers are the actual original ideals, not an isomorphic abstract
family supplied as a hypothesis. -/
def coloredIdeals (E : Fin r → Finset (FiniteTuple n))
    (c : ULift.{u} (Fin r)) : Ideal (MvPolynomial (FiniteVariable.{u} n) k) :=
  finiteSublatticeIdeal n (E c.down)

lemma coloredIdeal_row_generators (E : Fin r → Finset (FiniteTuple n)) :
    coloredIdeal (coloredIdeals (k := k) n E)=
      Ideal.span {p | ∃ c : Fin r, ∃ a∈E c,
        p=monomial (Finsupp.single (ULift.up c) 1) (finiteRowMonomial n a)} := by
  change coloredIdeal (fun c : ULift.{u} (Fin r) =>
    Ideal.span ((finiteRowMonomial n (k := k)) '' (E c.down : Set _))) = _
  rw [coloredIdeal_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨c,f,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨c.down,a,ha,rfl⟩
  · rintro ⟨c,a,ha,rfl⟩
    exact ⟨ULift.up c,finiteRowMonomial n a,⟨a,ha,rfl⟩,rfl⟩

/-- The exact polynomial and ideal identification used in Theorem 5.5. -/
theorem coloredIdeal_map_eq_sublattice (E : Fin r → Finset (FiniteTuple n)) :
    Ideal.map (coloredPolynomialEquiv (k := k) n).toRingHom
      (coloredIdeal (coloredIdeals (k := k) n E))=
        finiteSublatticeIdeal (coloredRows (r := r) n) (coloredFamily n E) := by
  rw [coloredIdeal_row_generators,Ideal.map_span,finiteSublatticeIdeal]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨p,⟨c,a,ha,rfl⟩,rfl⟩
    exact ⟨coloredTuple n c a,(coloredTuple_mem_family n E c a).mpr ha,
      (coloredPolynomialEquiv_row n c a).symm⟩
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨⟨c,a⟩,rfl⟩ := (coloredTupleEquiv n).surjective a
    refine ⟨monomial (Finsupp.single (ULift.up c) 1) (finiteRowMonomial n a),
      ⟨c,a,(coloredTuple_mem_family n E c a).mp ha,rfl⟩,?_⟩
    exact coloredPolynomialEquiv_row n c a

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColorDiagonal -/
section

/-!
# The minimum color-degree diagonal of an actual monomial Koszul complex

The color variables are an arbitrary specified subset of the polynomial
variables. Every displayed ideal generator has color degree one. In the
degree-m diagonal of its m-th power, the actual exterior monomial therefore
contains no color variable. This includes m = 0 and arbitrary coefficient
rings; it is a statement about the literal monomial basis, not a dimension
count or a chosen replacement complex.

This is the common chain-level restriction used in Sections 5 and 7. It does
not, by itself, assert the mixed-power generation or mixed Tor formula.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid

universe u
variable {V : Type u} [Fintype V] [LinearOrder V]

/-- Total degree in precisely the designated color variables. -/
def colorDegree (Z : Finset V) : Exponent V →+ ℕ where
  toFun a := subsetSum a Z
  map_zero' := by simp [subsetSum]
  map_add' a b := by simp [subsetSum, Finset.sum_add_distrib]

lemma colorDegree_mono (Z : Finset V) {a b : Exponent V} (h : a ≤ b) :
    colorDegree Z a ≤ colorDegree Z b :=
  Finset.sum_le_sum (fun v _ => h v)

@[simp] lemma colorDegree_single (Z : Finset V) (v : V) (a : ℕ) :
    colorDegree Z (Finsupp.single v a) = if v ∈ Z then a else 0 := by
  simp [colorDegree, subsetSum, Finsupp.single_apply, eq_comm]

lemma colorDegree_power_generator (B : Family V) (Z : Finset V)
    (hB : ∀ a ∈ B, colorDegree Z a = 1) (m : ℕ)
    (a : Exponent V) (ha : a ∈ exponentPowerFamily B m) :
    colorDegree Z a = m := by
  induction m generalizing a with
  | zero =>
      have he : a = 0 := by simpa only [exponentPowerFamily, Finset.mem_singleton] using ha
      rw [he, map_zero]
  | succ m ih =>
      obtain ⟨⟨b,c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hb,hc⟩ := Finset.mem_product.mp hbc
      rw [map_add, ih b hb, hB c hc]

theorem colorDegree_power_lower (B : Family V) (Z : Finset V)
    (hB : ∀ a ∈ B, colorDegree Z a = 1) (m : ℕ)
    {a : Exponent V} (ha : Contains (exponentPowerFamily B m) a) :
    m ≤ colorDegree Z a := by
  obtain ⟨b,hb,hba⟩ := ha
  rw [← colorDegree_power_generator B Z hB m b hb]
  exact colorDegree_mono Z hba

/-- The generator dividing a minimum-color monomial has exactly the same
exponent at every color variable. There is no residual color factor. -/
theorem colorDegree_minimal_generator_colors (B : Family V) (Z : Finset V)
    (hB : ∀ a ∈ B, colorDegree Z a = 1) (m : ℕ)
    {a b : Exponent V} (ha : colorDegree Z a = m)
    (hb : b ∈ exponentPowerFamily B m) (hba : b ≤ a) :
    ∀ v ∈ Z, b v = a v := by
  have hs : ∑ v ∈ Z, b v = ∑ v ∈ Z, a v :=
    (colorDegree_power_generator B Z hB m b hb).trans ha.symm
  exact (Finset.sum_eq_sum_iff_of_le (fun v _ => hba v)).mp hs

lemma colorDegree_face_eq_zero_iff (Z F : Finset V) :
    colorDegree Z (faceExponent F) = 0 ↔ Disjoint F Z := by
  change (∑ v ∈ Z, faceExponent F v) = 0 ↔ _
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro v hvF hvZ
    have hh := h v hvZ
    exact Nat.one_ne_zero (by simpa only [faceExponent_apply, if_pos hvF] using hh)
  · intro h v hvZ
    have hvF : v ∉ F := fun hv => (Finset.disjoint_left.mp h hv hvZ)
    simp only [faceExponent_apply, if_neg hvF]

/-- Every surviving basis vector on the minimum-color diagonal has no
exterior color variable. -/
theorem minimumColorDiagonal_no_exterior (B : Family V) (Z : Finset V)
    (hB : ∀ a ∈ B, colorDegree Z a = 1) (m : ℕ)
    (α : Exponent V) (hα : colorDegree Z α = m)
    (F : Finset V) (hF : koszulFaces (exponentPowerFamily B m) α F) :
    Disjoint F Z := by
  have hlow := colorDegree_power_lower B Z hB m hF.2
  have he := congrArg (colorDegree Z) (tsub_add_cancel_of_le hF.1)
  rw [map_add, hα] at he
  exact (colorDegree_face_eq_zero_iff Z F).mp (by omega)

theorem minimumColorDiagonal_residual_colors (B : Family V) (Z : Finset V)
    (hB : ∀ a ∈ B, colorDegree Z a = 1) (m : ℕ)
    (α : Exponent V) (hα : colorDegree Z α = m)
    (F : Finset V) (hF : koszulFaces (exponentPowerFamily B m) α F) :
    ∀ v ∈ Z, (α - faceExponent F) v = α v := by
  have hdis := minimumColorDiagonal_no_exterior B Z hB m α hα F hF
  intro v hvZ
  have hvF : v ∉ F := fun hv => Finset.disjoint_left.mp hdis hv hvZ
  simp only [Finsupp.tsub_apply, faceExponent_apply, if_neg hvF, tsub_zero]

variable {k : Type u} [CommRing k]

/-- The same restriction on the actual coefficient/exterior basis of the
Koszul tensor module. Its hypothesis is the genuine total multidegree,
including the exterior factor. -/
theorem minimumColorDiagonal_monomialIndex (B : Family V) (Z : Finset V)
    (hB : ∀ a ∈ B, colorDegree Z a = 1) (m p : ℕ)
    (a : MonomialIndex (exponentPowerFamily B m) p)
    (ha : colorDegree Z (monomialDegree a) = m) :
    Disjoint a.1.val Z := by
  have hlow := colorDegree_power_lower B Z hB m a.2.property
  have he : colorDegree Z a.2.val + colorDegree Z (faceExponent a.1.val) = m := by
    simpa only [monomialDegree, map_add] using ha
  exact (colorDegree_face_eq_zero_iff Z a.1.val).mp (by omega)

/-- On a fixed genuine fine strand, every nonzero basis coefficient has an
exterior face disjoint from the color variables. -/
theorem minimumColorDiagonal_support (B : Family V) (Z : Finset V)
    (hB : ∀ a ∈ B, colorDegree Z a = 1) (m p : ℕ)
    (α : Exponent V) (hα : colorDegree Z α = m)
    (z : Set.powersetCard V p →₀ monomialIdeal k (exponentPowerFamily B m))
    (hz : z ∈ homogeneousPiece (k := k) (exponentPowerFamily B m) α p)
    (a : MonomialIndex (exponentPowerFamily B m) p)
    (ha : (monomialCoefficientBasis (k := k) (exponentPowerFamily B m) p).repr z a ≠ 0) :
    Disjoint a.1.val Z := by
  have hd : monomialDegree a = α := ((Grading.mem_piece (monomialCoefficientBasis (k := k) (exponentPowerFamily B m) p)
    monomialDegree α z).mp hz) a ha
  apply minimumColorDiagonal_monomialIndex B Z hB m p a
  rw [hd]
  exact hα

section RowColor
variable {d : ℕ} (n : Fin d → ℕ)

/-- Choosing the added color row uses exactly its actual polynomial
variables, with no auxiliary variables or relabeling assumptions. -/
def finiteRowColorVariables (r : Fin d) : Finset (FiniteVariable.{u} n) :=
  Finset.univ.filter (fun v => v.1 = r)

lemma finiteRowExponent_colorDegree (r : Fin d) (a : FiniteTuple n) :
    colorDegree (finiteRowColorVariables n r) (finiteRowExponent.{u} n a) = 1 := by
  unfold finiteRowExponent
  rw [map_sum]
  simp [finiteRowColorVariables]

lemma finiteRowFamily_colorDegree (E : Finset (FiniteTuple n)) (r : Fin d) :
    ∀ a ∈ finiteRowFamily.{u} n E, colorDegree (finiteRowColorVariables n r) a = 1 := by
  intro a ha
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ha
  exact finiteRowExponent_colorDegree n r b

/-- The literal diagonal assertion used for a colored sublattice ideal.
No lattice hypothesis is needed for this degree calculation. -/
theorem finiteSublattice_colorDiagonal_no_exterior
    (E : Finset (FiniteTuple n)) (r : Fin d) (m : ℕ)
    (α : Exponent (FiniteVariable.{u} n))
    (hα : colorDegree (finiteRowColorVariables n r) α = m)
    (F : Finset (FiniteVariable.{u} n))
    (hF : koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α F) :
    Disjoint F (finiteRowColorVariables n r) := by
  apply minimumColorDiagonal_no_exterior (finiteRowFamily n E) (finiteRowColorVariables n r)
    (finiteRowFamily_colorDegree n E r) m α hα F
  convert hF using 1 <;> congr 1
  exact Subsingleton.elim _ _

end RowColor

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CoordinateFoundation -/
section

/-!
# Compatibility imports for the recovered CoordinateFoundation development

The mathematical proofs live in their original modular sources. The saved
source comparison records the unchanged proof bodies and the independent
variable-universe generality retained by those original modules.
-/

end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesImageExtension -/
section

section
set_option Elab.async false

/- Exact mathematical body of ReesImage.lean, checked against the accepted modular foundation. -/
set_option autoImplicit false

/-!
# The monoid algebra is the actual finite Rees presentation image

An explicit injective algebra map sends a monoid basis element to the corresponding
monomial in `S[t]`. Its range is proved equal to the image of the presentation
`x ↦ x`, `T_a ↦ u_a t`. The degree-`m` monoid indices are exactly the monomials of
`I_E ^ m`, by the ordinary-power membership theorem.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical MvPolynomial CommAlg.Polymatroid

universe u v
variable {d : ℕ} {n : Fin d → ℕ} (E : Finset (FiniteTuple n))
variable (k : Type v) [CommRing k]

lemma addMonoidAlgebra_mapDomain_surjective {k A B : Type*} [Semiring k]
    {f : A → B} (hf : Function.Surjective f) :
    Function.Surjective (AddMonoidAlgebra.mapDomain (R := k) f) := by
  intro x
  obtain ⟨y,hy⟩ := Finsupp.mapDomain_surjective hf x.coeff
  exact ⟨AddMonoidAlgebra.ofCoeff y,congrArg AddMonoidAlgebra.ofCoeff hy⟩

def finiteReesPresentationMap :
    MvPolynomial (FiniteReesVariable.{u} E) k →ₐ[k] MvPolynomial (Option (FiniteVariable.{u} n)) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k (finiteReesExponentMap E)

def finiteReesImage : Subalgebra k (MvPolynomial (Option (FiniteVariable.{u} n)) k) :=
  (finiteReesPresentationMap E k).range

def finiteExponentToRange : (FiniteReesVariable.{u} E →₀ ℕ) →+ finiteReesExponentMonoid.{u} E where
  toFun a := ⟨finiteReesExponentMap E a,⟨a,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

lemma finiteExponentToRange_surjective : Function.Surjective (finiteExponentToRange.{u} E) := by
  intro a
  obtain ⟨c,hc⟩ := a.property
  exact ⟨c,Subtype.ext hc⟩

def finitePresentationToMonoid :
    MvPolynomial (FiniteReesVariable.{u} E) k →ₐ[k] AddMonoidAlgebra k (finiteReesExponentMonoid.{u} E) :=
  AddMonoidAlgebra.mapDomainAlgHom k k (finiteExponentToRange E)

lemma finitePresentationToMonoid_surjective :
    Function.Surjective (finitePresentationToMonoid.{u} E k) :=
  addMonoidAlgebra_mapDomain_surjective (finiteExponentToRange_surjective E)

def finiteReesMonoidMap :
    AddMonoidAlgebra k (finiteReesExponentMonoid.{u} E) →ₐ[k]
      MvPolynomial (Option (FiniteVariable.{u} n)) k :=
  AddMonoidAlgebra.mapDomainAlgHom k k (finiteReesExponentMonoid E).subtype

lemma finiteReesMonoidMap_injective : Function.Injective (finiteReesMonoidMap.{u} E k) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

lemma finiteReesPresentation_factorization :
    (finiteReesMonoidMap.{u} E k).comp (finitePresentationToMonoid E k) =
      finiteReesPresentationMap E k := by
  rw [finiteReesMonoidMap,finitePresentationToMonoid,← AddMonoidAlgebra.mapDomainAlgHom_comp]
  rfl

lemma finiteReesMonoidMap_range : (finiteReesMonoidMap.{u} E k).range = finiteReesImage E k := by
  ext f
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨p,rfl⟩ := finitePresentationToMonoid_surjective E k g
    refine ⟨p,?_⟩
    exact (AlgHom.congr_fun (finiteReesPresentation_factorization E k) p).symm.trans hg
  · rintro ⟨p,hp⟩
    exact ⟨finitePresentationToMonoid E k p,
      (AlgHom.congr_fun (finiteReesPresentation_factorization E k) p).trans hp⟩

/-- A genuine algebra equivalence to the actual image in the polynomial ring. -/
def finiteReesMonoidEquiv :
    AddMonoidAlgebra k (finiteReesExponentMonoid.{u} E) ≃ₐ[k] finiteReesImage E k :=
  (AlgEquiv.ofInjective (finiteReesMonoidMap E k) (finiteReesMonoidMap_injective E k)).trans
    (Subalgebra.equivOfEq _ _ (finiteReesMonoidMap_range E k))

@[simp] lemma finiteReesMonoidEquiv_single (a : finiteReesExponentMonoid.{u} E) (c : k) :
    (finiteReesMonoidEquiv E k (AddMonoidAlgebra.single a c)).val = monomial a.val c := by
  change finiteReesMonoidMap E k (AddMonoidAlgebra.single a c) = _
  exact AddMonoidAlgebra.mapDomain_single

/-- The actual Rees algebra's basis consists of genuine monomials of `S[t]`. -/
def finiteReesImageBasis : Module.Basis (finiteReesExponentMonoid.{u} E) k (finiteReesImage E k) :=
  (AddMonoidAlgebra.basis (finiteReesExponentMonoid E) k).map (finiteReesMonoidEquiv E k).toLinearEquiv

@[simp] lemma finiteReesImageBasis_val (a : finiteReesExponentMonoid.{u} E) :
    (finiteReesImageBasis E k a).val = monomial a.val 1 := by
  simp [finiteReesImageBasis,Module.Basis.map_apply]

variable {E k}

def finiteReesFineExponent (a : finiteReesExponentMonoid.{u} E) : Exponent (FiniteVariable.{u} n) :=
  a.val.comapDomain some (Option.some_injective _).injOn

lemma finiteReesTarget_reconstruct (a : finiteReesExponentMonoid.{u} E) :
    finiteTargetExponent (finiteReesFineExponent a) (a.val none) = a.val := by
  ext x
  cases x with
  | none => simp
  | some x => simp [finiteReesFineExponent]

/-- The degree `m` exponent indices are exactly the monomial indices of the
actual ordinary power; both directions retain all fine exponents. -/
def finiteReesPowerIndexEquiv (m : ℕ) :
    {a : finiteReesExponentMonoid.{u} E // a.val none = m} ≃
      {a : Exponent (FiniteVariable.{u} n) //
        Contains (exponentPowerFamily (finiteRowFamily n E) m) a} where
  toFun a := ⟨finiteReesFineExponent a.val,(finiteTarget_mem_rees_iff _ m).mp (by
    have h := a.val.property
    rw [← finiteReesTarget_reconstruct a.val] at h
    simpa only [a.property] using h)⟩
  invFun a := ⟨⟨finiteTargetExponent a.val m,(finiteTarget_mem_rees_iff _ m).mpr a.property⟩,
    finiteTargetExponent_none _ _⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [a.property] using finiteReesTarget_reconstruct a.val
  right_inv a := by
    apply Subtype.ext
    ext x
    simp [finiteReesFineExponent]

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.TriangularPerturbationUnits -/
section

/-!
# Genuine inverse operators from strictly decreasing basis degree

A nonnegative degree on an arbitrary basis suffices: no finite total rank is
required. The previously checked unitriangular-basis construction supplies
the inverse. This is the local finiteness needed for the perturbation of an
infinite polynomial resolution.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Package an actual linear equivalence as a unit of the endomorphism ring. -/
def linearEquivUnit (e : M ≃ₗ[R] M) : (Module.End R M)ˣ where
  val := e.toLinearMap
  inv := e.symm.toLinearMap
  val_inv := by ext x; exact e.apply_symm_apply x
  inv_val := by ext x; exact e.symm_apply_apply x

/-- A strictly degree-lowering operator has an invertible `1 + f`. -/
def triangularUnit (b : Module.Basis I R M) (rank : I → ℕ)
    (f : Module.End R M)
    (hf : ∀ i j, rank i ≤ rank j → b.repr (f (b i)) j = 0) :
    (Module.End R M)ˣ :=
  linearEquivUnit (Sublattice.triangularLinearEquiv b (1 + f) rank
    (by
      intro i
      have hi := hf i i le_rfl
      simpa only [LinearMap.add_apply, Module.End.one_apply, map_add,
        Finsupp.add_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        hi, add_zero])
    (by
      intro i j hij hrij
      have hi := hf i j hrij
      simpa only [LinearMap.add_apply, Module.End.one_apply, map_add,
        Finsupp.add_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne hij.symm, hi, zero_add]))

@[simp] theorem triangularUnit_val (b : Module.Basis I R M) (rank : I → ℕ)
    (f : Module.End R M)
    (hf : ∀ i j, rank i ≤ rank j → b.repr (f (b i)) j = 0) :
    (triangularUnit b rank f hf : Module.End R M) = 1 + f :=
  Sublattice.triangularLinearEquiv_toLinearMap ..

end FourPapers.HomologicalPerturbation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.DegreeLoweringPerturbation -/
section

/-!
# Finite perturbation from a nonnegative basis degree

The complex may have infinite total rank. The two inverse operators in the
perturbation lemma are constructed from strict decrease of a natural-valued
degree. In the polynomial application this is the internal degree of the
coefficient Koszul factor, not the total polynomial degree of the enlarged
free resolution. This distinction makes the construction locally finite.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.HomologicalPerturbation

variable {R M H I : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

def DegreeNonincreasing (b : Module.Basis I R M) (rank : I → ℕ)
    (f : Module.End R M) : Prop :=
  ∀ i j, rank i < rank j → b.repr (f (b i)) j = 0

def DegreeDecreasing (b : Module.Basis I R M) (rank : I → ℕ)
    (f : Module.End R M) : Prop :=
  ∀ i j, rank i ≤ rank j → b.repr (f (b i)) j = 0

theorem degreeDecreasing_of_mem_span (b : Module.Basis I R M) (rank : I → ℕ)
    (f : Module.End R M)
    (hf : ∀ i, f (b i) ∈ Submodule.span R (b '' {j | rank j < rank i})) :
    DegreeDecreasing b rank f := by
  classical
  intro i j hij
  by_contra hne
  have hj := (b.mem_span_image.mp (hf i)) (Finsupp.mem_support_iff.mpr hne)
  exact Nat.not_lt_of_ge hij hj

theorem DegreeNonincreasing.neg {b : Module.Basis I R M} {rank : I → ℕ}
    {f : Module.End R M} (hf : DegreeNonincreasing b rank f) :
    DegreeNonincreasing b rank (-f) := by
  intro i j hij
  simp only [LinearMap.neg_apply, map_neg, Finsupp.neg_apply, hf i j hij, neg_zero]

theorem DegreeNonincreasing.baseChange {b : Module.Basis I R M} {rank : I → ℕ}
    {f : Module.End R M} (hf : DegreeNonincreasing b rank f)
    (S : Type*) [CommRing S] [Algebra R S] :
    DegreeNonincreasing (b.baseChange S) rank (f.baseChange S) := by
  intro i j hij
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Module.Basis.baseChange_repr_tmul, hf i j hij, zero_smul]

lemma coefficient_apply_sum (b : Module.Basis I R M)
    (f : Module.End R M) (x : M) (j : I) :
    b.repr (f x) j = ∑ i ∈ (b.repr x).support,
      b.repr x i * b.repr (f (b i)) j := by
  classical
  have hx : x = ∑ i ∈ (b.repr x).support, b.repr x i • b i := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (b.linearCombination_repr x).symm
  calc
    b.repr (f x) j = b.repr
        (f (∑ i ∈ (b.repr x).support, b.repr x i • b i)) j :=
      congrArg (fun y => b.repr (f y) j) hx
    _ = _ := by
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        smul_eq_mul]

lemma DegreeDecreasing.mul_nonincreasing
    {b : Module.Basis I R M} {rank : I → ℕ} {f g : Module.End R M}
    (hf : DegreeDecreasing b rank f) (hg : DegreeNonincreasing b rank g) :
    DegreeDecreasing b rank (f * g) := by
  classical
  intro i j hij
  change b.repr (f (g (b i))) j = 0
  rw [coefficient_apply_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : rank k ≤ rank i
  · rw [hf k j (hki.trans hij), mul_zero]
  · rw [hg i k (Nat.lt_of_not_ge hki), zero_mul]

lemma DegreeNonincreasing.mul_decreasing
    {b : Module.Basis I R M} {rank : I → ℕ} {f g : Module.End R M}
    (hf : DegreeNonincreasing b rank f) (hg : DegreeDecreasing b rank g) :
    DegreeDecreasing b rank (f * g) := by
  classical
  intro i j hij
  change b.repr (f (g (b i))) j = 0
  rw [coefficient_apply_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : rank i ≤ rank k
  · rw [hg i k hik, zero_mul]
  · rw [hf k j ((Nat.lt_of_not_ge hik).trans_le hij), mul_zero]

namespace LinearContraction

variable (C : LinearContraction (R := R) (M := M) (H := H))
  (b : Module.Basis I R M) (rank : I → ℕ) (δ : Module.End R M)
  (hδ : DegreeDecreasing b rank δ)
  (hh : DegreeNonincreasing b rank C.h)

def leftPerturbationUnit : (Module.End R M)ˣ :=
  triangularUnit b rank (δ * C.h) (hδ.mul_nonincreasing hh)

def rightPerturbationUnit : (Module.End R M)ˣ :=
  triangularUnit b rank (C.h * δ) (hh.mul_decreasing hδ)

@[simp] theorem leftPerturbationUnit_val :
    (C.leftPerturbationUnit b rank δ hδ hh : Module.End R M) = 1 + δ * C.h :=
  triangularUnit_val ..

@[simp] theorem rightPerturbationUnit_val :
    (C.rightPerturbationUnit b rank δ hδ hh : Module.End R M) = 1 + C.h * δ :=
  triangularUnit_val ..

/-- A degree decrease constructs both required inverse operators and hence
the actual transferred differential, chain maps, and chain homotopy. -/
def perturbByDegree (hD : (C.d + δ) * (C.d + δ) = 0) :
    LinearDeformationRetract (R := R) (M := M) (H := H) :=
  C.perturb δ (C.leftPerturbationUnit b rank δ hδ hh)
    (C.rightPerturbationUnit b rank δ hδ hh)
    (C.leftPerturbationUnit_val b rank δ hδ hh)
    (C.rightPerturbationUnit_val b rank δ hδ hh) hD

/-- The finite model inherits minimal entries from the literal polynomial
perturbation. The statement is about coefficients in any actual target basis. -/
theorem perturbByDegree_coefficient_mem_ideal
    (hD : (C.d + δ) * (C.d + δ) = 0)
    {J : Type*} (c : Module.Basis J R H) (I₀ : Ideal R)
    (hI : ∀ x, δ x ∈ I₀ • (⊤ : Submodule R M)) (i j : J) :
    c.repr ((C.perturbByDegree b rank δ hδ hh hD).targetD (c i)) j ∈ I₀ :=
  C.transferredDifferential_basis_coefficient_mem δ
    (C.leftPerturbationUnit b rank δ hδ hh) c I₀ hI i j

end LinearContraction
end FourPapers.HomologicalPerturbation

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalFacets -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid
universe u

/-- The row indexing is `Fin (d+1)` only to name its first and last entries.
There is no bound on the number of rows or columns. -/
abbrev UnitIntervalRows (d N : ℕ) : Fin (d+1) → ℕ := fun _ => N

variable {d N : ℕ}
variable {E : Finset ((Fin (d+1) → Fin N))}

/-- Exactly the unit-interval facet condition in Section 6: facets are increasing
tuples, and every increasing tuple inside a facet's endpoint interval is a facet. -/
structure UnitIntervalFacetFamily (E : Finset ((Fin (d+1) → Fin N))) : Prop where
  increasing : ∀ a ∈ E, StrictMono a
  interval : ∀ a ∈ E, ∀ b : (Fin (d+1) → Fin N), StrictMono b →
    a 0 ≤ b 0 → b (Fin.last d) ≤ a (Fin.last d) → b ∈ E

theorem UnitIntervalFacetFamily.latticeClosed (hE : UnitIntervalFacetFamily E) :
    finiteLatticeClosed (UnitIntervalRows d N) E := by
  constructor
  · intro a ha b hb
    have hmono : StrictMono (β := Fin N) (fun i : Fin (d+1) => min (a i : Fin N) (b i : Fin N)) := by
      intro i j hij
      exact min_lt_min (hE.increasing a ha hij) (hE.increasing b hb hij)
    by_cases h : a 0 ≤ b 0
    · exact hE.interval a ha (a ⊓ b) hmono (by simp [Pi.inf_apply, inf_eq_left.mpr h])
        (by exact min_le_left _ _)
    · exact hE.interval b hb (a ⊓ b) hmono
        (by simpa [Pi.inf_apply, inf_eq_right.mpr (le_of_not_ge h)])
        (by exact min_le_right _ _)
  · intro a ha b hb
    have hmono : StrictMono (β := Fin N) (fun i : Fin (d+1) => max (a i : Fin N) (b i : Fin N)) := by
      intro i j hij
      exact max_lt_max (hE.increasing a ha hij) (hE.increasing b hb hij)
    by_cases h : a (Fin.last d) ≤ b (Fin.last d)
    · exact hE.interval b hb (a ⊔ b) hmono (by exact le_max_right _ _)
        (by simpa [Pi.sup_apply, sup_eq_right.mpr h])
    · exact hE.interval a ha (a ⊔ b) hmono (by exact le_max_left _ _)
        (by simpa [Pi.sup_apply, sup_eq_left.mpr (le_of_not_ge h)])

/-- A clique interval containing column `j` and the last column of `a` exists.
This is the predicate `c(a_last) ≤ j` in the paper. -/
def facetCoverAt (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N)) (j : Fin N) : Prop :=
  ∃ b ∈ E, b 0 ≤ j ∧ a (Fin.last d) ≤ b (Fin.last d)

lemma facetCoverAt_self {a : (Fin (d+1) → Fin N)} (ha : a ∈ E) :
    facetCoverAt E a (a 0) := ⟨a, ha, le_rfl, le_rfl⟩

lemma facetCoverAt_mono {a : (Fin (d+1) → Fin N)} {i j : Fin N}
    (h : i ≤ j) (hi : facetCoverAt E a i) : facetCoverAt E a j := by
  obtain ⟨b, hb, hbi, hab⟩ := hi
  exact ⟨b, hb, hbi.trans h, hab⟩

lemma facetCoverAt_last_antitone {a b : (Fin (d+1) → Fin N)}
    (h : a (Fin.last d) ≤ b (Fin.last d)) {j : Fin N}
    (hb : facetCoverAt E b j) : facetCoverAt E a j := by
  obtain ⟨c, hc, hcj, hbc⟩ := hb
  exact ⟨c, hc, hcj, h.trans hbc⟩

def facetCutoffCandidates (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N)) : Finset (Fin N) :=
  (E.filter (fun b => a (Fin.last d) ≤ b (Fin.last d))).image (fun b => b 0)

lemma facetCutoffCandidates_nonempty {a : (Fin (d+1) → Fin N)}
    (ha : a ∈ E) : (facetCutoffCandidates E a).Nonempty := by
  exact ⟨a 0, mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, le_rfl⟩, rfl⟩⟩

def facetCutoff {a : (Fin (d+1) → Fin N)} (ha : a ∈ E) : Fin N :=
  (facetCutoffCandidates E a).min' (facetCutoffCandidates_nonempty ha)

/-- The minimum-free predicate used in the proofs is rigorously identified
with the exact cutoff appearing in Lemma 6.1. -/
lemma facetCutoff_le_iff {a : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (j : Fin N) : facetCutoff ha ≤ j ↔ facetCoverAt E a j := by
  constructor
  · intro hj
    have hm := Finset.min'_mem (facetCutoffCandidates E a) (facetCutoffCandidates_nonempty ha)
    obtain ⟨b, hb, hbc⟩ := mem_image.mp hm
    obtain ⟨hbE, hab⟩ := mem_filter.mp hb
    exact ⟨b, hbE, hbc.le.trans hj, hab⟩
  · rintro ⟨b, hb, hbj, hab⟩
    exact (Finset.min'_le _ _ (mem_image.mpr ⟨b, mem_filter.mpr ⟨hb, hab⟩, rfl⟩)).trans hbj

def facetPrevious (r : Fin (d+1)) : Fin (d+1) := ⟨r.val-1, by omega⟩

@[simp] lemma facetPrevious_succ (r : Fin d) : facetPrevious r.succ = r.castSucc := by
  apply Fin.ext
  simp [facetPrevious]

lemma facetPrevious_lt {r : Fin (d+1)} (hr : r ≠ 0) : facetPrevious r < r := by
  have hpos : 0 < r.val := by
    by_contra h
    apply hr
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  change r.val-1 < r.val
  omega

def facetLinearVariables (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N)) : Finset (FiniteVariable.{u} (UnitIntervalRows d N)) :=
  Finset.univ.filter (fun v => v.2.down < a v.1 ∧
    if v.1 = 0 then facetCoverAt E a v.2.down else a (facetPrevious v.1) < v.2.down)

@[simp] lemma facetLinearVariables_zero
    (a : (Fin (d+1) → Fin N)) (j : Fin N) :
    (⟨0, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∈ facetLinearVariables E a ↔
      j < a 0 ∧ facetCoverAt E a j := by simp [facetLinearVariables]

@[simp] lemma facetLinearVariables_succ
    (a : (Fin (d+1) → Fin N)) (r : Fin d) (j : Fin N) :
    (⟨r.succ, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∈ facetLinearVariables E a ↔
      j < a r.succ ∧ a r.castSucc < j := by simp [facetLinearVariables]

def facetResidualFacets (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N)) : Finset ((Fin (d+1) → Fin N)) :=
  E.filter (fun b => ¬ facetCoverAt E a (b 0) ∧ ∀ r : Fin d, b r.succ ≤ a r.castSucc)

@[simp] lemma mem_facetResidualFacets (a b : (Fin (d+1) → Fin N)) :
    b ∈ facetResidualFacets E a ↔
      b ∈ E ∧ ¬ facetCoverAt E a (b 0) ∧ ∀ r : Fin d, b r.succ ≤ a r.castSucc := by
  simp [facetResidualFacets]

/-- The residual is literally a variable restriction of the original facet ideal. -/
def facetResidualRows (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N)) (r : Fin (d+1)) : Finset (Fin N) :=
  Finset.univ.filter (fun j => if r = 0 then ¬ facetCoverAt E a j else j ≤ a (facetPrevious r))

lemma facetResidualFacets_restriction (a b : (Fin (d+1) → Fin N)) :
    b ∈ facetResidualFacets E a ↔ b ∈ E ∧ ∀ r, b r ∈ facetResidualRows E a r := by
  rw [mem_facetResidualFacets]
  constructor
  · rintro ⟨hb, h0, hs⟩
    refine ⟨hb, ?_⟩
    intro r
    refine Fin.cases ?_ (fun s => ?_) r
    · simpa [facetResidualRows] using h0
    · simpa [facetResidualRows] using hs s
  · rintro ⟨hb, hrows⟩
    refine ⟨hb, ?_, ?_⟩
    · simpa [facetResidualRows] using hrows 0
    · intro r
      simpa [facetResidualRows] using hrows r.succ

lemma facetResidualFacets_mono {a b : (Fin (d+1) → Fin N)}
    (hab : a ≤ b) : facetResidualFacets E a ⊆ facetResidualFacets E b := by
  intro c hc
  obtain ⟨hcE, hc0, hcr⟩ := (mem_facetResidualFacets a c).mp hc
  exact (mem_facetResidualFacets b c).mpr ⟨hcE,
    fun h => hc0 (facetCoverAt_last_antitone (hab _) h), fun r => (hcr r).trans (hab _)⟩

lemma facetResidualFacets_strict (hE : UnitIntervalFacetFamily E)
    {a b : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (hb : b ∈ facetResidualFacets E a) : ∀ r, b r < a r := by
  obtain ⟨hbE, hb0, hbr⟩ := (mem_facetResidualFacets a b).mp hb
  intro r
  refine Fin.cases ?_ (fun s => ?_) r
  · exact lt_of_not_ge (fun h => hb0 (facetCoverAt_mono h (facetCoverAt_self ha)))
  · exact (hbr s).trans_lt (hE.increasing a ha ((show s.castSucc < s.succ from Fin.castSucc_lt_succ)))

lemma facetResidualFacets_predecessor (hE : UnitIntervalFacetFamily E)
    {a b : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (hb : b ∈ facetResidualFacets E a) : b ≤ a ∧ b ≠ a := by
  have h := facetResidualFacets_strict hE ha hb
  exact ⟨fun r => (h r).le, fun heq => (h 0).ne (congrFun heq 0)⟩

theorem facetColon_disjoint_support (hE : UnitIntervalFacetFamily E)
    {a b : (Fin (d+1) → Fin N)}
    {v : FiniteVariable.{u} (UnitIntervalRows d N)}
    (hv : v ∈ facetLinearVariables E a) (hb : b ∈ facetResidualFacets E a) :
    finiteRowExponent (UnitIntervalRows d N) b v = 0 := by
  obtain ⟨hbE, hb0, hbr⟩ := (mem_facetResidualFacets a b).mp hb
  rcases v with ⟨r, ⟨j⟩⟩
  revert hv
  refine Fin.cases ?_ (fun s => ?_) r
  · intro hv
    have hj := (facetLinearVariables_zero a j).mp hv
    have hne : b 0 ≠ j := fun h => hb0 (h.symm ▸ hj.2)
    simp [finiteRowExponent_apply, hne]
  · intro hv
    have hj := (facetLinearVariables_succ a s j).mp hv
    have hne : b s.succ ≠ j := ((hbr s).trans_lt hj.2).ne
    simp [finiteRowExponent_apply, hne]

/-- Once a coordinate agrees with the distinguished facet, absence of a linear
ratio forces the next coordinate to agree as well. -/
lemma facet_equality_propagates (hE : UnitIntervalFacetFamily E)
    {a b : (Fin (d+1) → Fin N)} (hb : b ∈ E) (hba : b ≤ a)
    (havoid : ∀ r, b r ≠ a r →
      (⟨r, ULift.up (b r)⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∉ facetLinearVariables E a)
    (r : Fin d) (hr : b r.castSucc = a r.castSucc) : b r.succ = a r.succ := by
  by_contra hn
  apply havoid r.succ hn
  apply (facetLinearVariables_succ a r (b r.succ)).mpr
  exact ⟨lt_of_le_of_ne (hba _) hn, hr ▸ hE.increasing b hb ((show r.castSucc < r.succ from Fin.castSucc_lt_succ))⟩

/-- Every predecessor ratio not divisible by a linear-colon variable is the
entire monomial of a residual facet. This is the key arbitrary-row step of 6.1. -/
theorem facet_predecessor_residual (hE : UnitIntervalFacetFamily E)
    {a b : (Fin (d+1) → Fin N)} (ha : a ∈ E) (hb : b ∈ E)
    (hba : b ≤ a) (hne : b ≠ a)
    (havoid : ∀ r, b r ≠ a r →
      (⟨r, ULift.up (b r)⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∉ facetLinearVariables E a) :
    b ∈ facetResidualFacets E a ∧ ∀ r, b r ≠ a r := by
  have hcover : ¬ facetCoverAt E a (b 0) := by
    intro hc
    have h0 : b 0 = a 0 := by
      by_contra h0
      exact havoid 0 h0 ((facetLinearVariables_zero a (b 0)).mpr
        ⟨lt_of_le_of_ne (hba _) h0, hc⟩)
    apply hne
    funext r
    exact Fin.induction h0 (fun s hs => facet_equality_propagates hE hb hba havoid s hs) r
  have hlast : b (Fin.last d) ≠ a (Fin.last d) := by
    intro heq
    exact hcover ⟨b, hb, le_rfl, heq.ge⟩
  have hcoord : ∀ r, b r ≠ a r := by
    intro r
    refine Fin.reverseInduction hlast (fun s hs => ?_) r
    intro heq
    exact hs (facet_equality_propagates hE hb hba havoid s heq)
  refine ⟨(mem_facetResidualFacets a b).mpr ⟨hb, hcover, ?_⟩, hcoord⟩
  intro r
  by_contra hle
  apply havoid r.succ (hcoord _)
  exact (facetLinearVariables_succ a r (b r.succ)).mpr
    ⟨lt_of_le_of_ne (hba _) (hcoord _), lt_of_not_ge hle⟩

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.UnitIntervalFacetFamily.latticeClosed
#print axioms FourPapers.Sublattice.facet_predecessor_residual

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalColon -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid
universe u
variable {d N : ℕ}
variable {E : Finset ((Fin (d+1) → Fin N))}

lemma facet_update_le (a : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (j : Fin N) (hj : j ≤ a r) : Function.update a r j ≤ a := by
  intro s
  by_cases hs : s = r
  · subst s
    simpa using hj
  · simp [Function.update_of_ne hs]

lemma facet_update_ne (a : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (j : Fin N) (hj : j ≠ a r) : Function.update a r j ≠ a := by
  intro heq
  exact hj (by simpa using congrFun heq r)

lemma facet_update_strictMono {a : (Fin (d+1) → Fin N)}
    (ha : StrictMono a) (r : Fin (d+1)) (j : Fin N)
    (hj : j < a r) (hleft : ∀ s < r, a s < j) : StrictMono (Function.update a r j) := by
  intro s t hst
  by_cases hs : s = r
  · subst s
    have ht : t ≠ r := ne_of_gt hst
    simpa [Function.update_of_ne ht] using hj.trans (ha hst)
  · by_cases ht : t = r
    · subst t
      simpa [Function.update_of_ne hs] using hleft s hst
    · simpa [Function.update_of_ne hs, Function.update_of_ne ht] using ha hst

/-- Each displayed linear generator is an actual predecessor ratio, obtained
by lowering the indicated coordinate within a clique interval. -/
theorem facet_linear_update_mem (hE : UnitIntervalFacetFamily E)
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (r : Fin (d+1)) (j : Fin N)
    (hv : (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∈ facetLinearVariables E a) :
    Function.update a r j ∈ E := by
  have hvar : j < a r ∧
      (if r = 0 then facetCoverAt E a j else a (facetPrevious r) < j) := by
    simpa only [facetLinearVariables, mem_filter, mem_univ, true_and] using hv
  have hleft : ∀ s < r, a s < j := by
    intro s hsr
    by_cases hr : r = 0
    · subst r
      exact False.elim (by have : s.val < 0 := hsr; omega)
    · have hs : s ≤ facetPrevious r := by
        change s.val ≤ r.val-1
        have : s.val < r.val := hsr
        omega
      exact (hE.increasing a ha).monotone hs |>.trans_lt (by simpa [hr] using hvar.2)
  have hm := facet_update_strictMono (hE.increasing a ha) r j hvar.1 hleft
  have hle := facet_update_le a r j hvar.1.le
  by_cases hr : r = 0
  · subst r
    obtain ⟨b, hb, hbj, hab⟩ := (show facetCoverAt E a j by simpa using hvar.2)
    exact hE.interval b hb _ hm (by simpa using hbj) ((hle _).trans hab)
  · exact hE.interval a ha _ hm (by simp [Function.update_of_ne (Ne.symm hr)]) (hle _)

lemma facetRatio_contains_coordinate (a b : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (hr : b r ≠ a r) :
    Finsupp.single (⟨r, ULift.up (b r)⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) 1 ≤
      finiteRowExponent (UnitIntervalRows d N) b - finiteRowExponent (UnitIntervalRows d N) a := by
  apply Finsupp.single_le_iff.mpr
  simp [Finsupp.tsub_apply, finiteRowExponent_apply, hr, Ne.symm hr]

lemma facetRatio_disjoint (a b : (Fin (d+1) → Fin N))
    (h : ∀ r, b r ≠ a r) :
    finiteRowExponent (UnitIntervalRows d N) b - finiteRowExponent (UnitIntervalRows d N) a =
      finiteRowExponent (UnitIntervalRows d N) b := by
  ext v
  rcases v with ⟨r, ⟨j⟩⟩
  by_cases hj : b r = j
  · subst j
    simp [Finsupp.tsub_apply, finiteRowExponent_apply, h r, Ne.symm (h r)]
  · simp [Finsupp.tsub_apply, finiteRowExponent_apply, hj]

lemma facetRatio_update (a : (Fin (d+1) → Fin N))
    (r : Fin (d+1)) (j : Fin N) (hj : j ≠ a r) :
    finiteRowExponent (UnitIntervalRows d N) (Function.update a r j) -
      finiteRowExponent (UnitIntervalRows d N) a =
        Finsupp.single (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) 1 := by
  ext v
  rcases v with ⟨s, ⟨i⟩⟩
  by_cases hs : s = r
  · subst s
    by_cases hi : j = i
    · subst i
      simp [Finsupp.tsub_apply, finiteRowExponent_apply, Finsupp.single_apply, hj, Ne.symm hj]
    · simp [Finsupp.tsub_apply, finiteRowExponent_apply, Finsupp.single_apply, hi]
  · have hvar : (⟨r, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ≠ ⟨s, ULift.up i⟩ :=
      fun h => hs (congrArg Sigma.fst h).symm
    simp [Finsupp.tsub_apply, finiteRowExponent_apply, Function.update_of_ne hs,
      Finsupp.single_apply, hvar]

def facetColonFamily (E : Finset ((Fin (d+1) → Fin N)))
    (a : (Fin (d+1) → Fin N)) : Family (FiniteVariable.{u} (UnitIntervalRows d N)) :=
  (facetLinearVariables E a).image (fun v => Finsupp.single v 1) ∪
    finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a)

/-- The complete arbitrary-row colon identity, first as equality of the exact
monomial divisibility predicates. -/
theorem facetCoordinateColon_contains_iff (hE : UnitIntervalFacetFamily E)
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ E)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    Contains (finiteCoordinatePredecessorFamily E a) α ↔ Contains (facetColonFamily E a) α := by
  constructor
  · rintro ⟨c, hc, hcα⟩
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
    obtain ⟨hbE, hba, hne⟩ := mem_filter.mp hb
    by_cases hlinear : ∃ r, b r ≠ a r ∧
        (⟨r, ULift.up (b r)⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∈ facetLinearVariables E a
    · obtain ⟨r, hr, hrv⟩ := hlinear
      refine ⟨Finsupp.single ⟨r, ULift.up (b r)⟩ 1, ?_,
        (facetRatio_contains_coordinate a b r hr).trans hcα⟩
      exact mem_union_left _ (mem_image.mpr ⟨_, hrv, rfl⟩)
    · have hav : ∀ r, b r ≠ a r →
          (⟨r, ULift.up (b r)⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∉ facetLinearVariables E a :=
        fun r hr hv => hlinear ⟨r, hr, hv⟩
      obtain ⟨hbres, hcoord⟩ := facet_predecessor_residual hE ha hbE hba hne hav
      refine ⟨finiteRowExponent (UnitIntervalRows d N) b,
        mem_union_right _ (mem_image.mpr ⟨b, hbres, rfl⟩), ?_⟩
      rwa [facetRatio_disjoint a b hcoord] at hcα
  · rintro ⟨c, hc, hcα⟩
    rcases mem_union.mp hc with hc | hc
    · obtain ⟨⟨r, ⟨j⟩⟩, hv, rfl⟩ := mem_image.mp hc
      have hj : j < a r := (by
        simpa only [facetLinearVariables, mem_filter, mem_univ, true_and] using hv :
          j < a r ∧ (if r = 0 then facetCoverAt E a j else a (facetPrevious r) < j)).1
      let b := Function.update a r j
      refine ⟨finiteRowExponent (UnitIntervalRows d N) b - finiteRowExponent (UnitIntervalRows d N) a,
        mem_image.mpr ⟨b, mem_filter.mpr ⟨facet_linear_update_mem hE ha r j hv,
          facet_update_le a r j hj.le, facet_update_ne a r j hj.ne⟩, rfl⟩, ?_⟩
      simpa only [b, facetRatio_update a r j hj.ne] using hcα
    · obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
      have hp := facetResidualFacets_predecessor hE ha hb
      have hs := facetResidualFacets_strict hE ha hb
      refine ⟨finiteRowExponent (UnitIntervalRows d N) b - finiteRowExponent (UnitIntervalRows d N) a,
        mem_image.mpr ⟨b, mem_filter.mpr ⟨(mem_facetResidualFacets a b).mp hb |>.1,
          hp.1, hp.2⟩, rfl⟩, ?_⟩
      simpa only [facetRatio_disjoint a b (fun r => (hs r).ne)] using hcα

/-- Lemma 6.1 for every number of rows, stated for the genuine ideal colon. -/
theorem unitIntervalPredecessorColon_eq {k : Type*} [CommSemiring k]
    (hE : UnitIntervalFacetFamily E) {a : (Fin (d+1) → Fin N)} (ha : a ∈ E) :
    finitePredecessorColon (UnitIntervalRows d N) (k := k) E a =
      monomialIdeal k (facetColonFamily E a) := by
  rw [← finiteCoordinatePredecessor_ideal (k := k) hE.latticeClosed ha]
  ext f
  simp_rw [mem_monomialIdeal_iff, facetCoordinateColon_contains_iff hE ha]

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitIntervalPredecessorColon_eq

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientInvariance -/
section

set_option autoImplicit false

/-!
# Actual quotient Koszul complexes depend only on the monomial ideal

Different generating families can contain redundant monomials involving variables
absent from a minimal family. The comparison below uses a proved equality of the
whole divisibility predicate, and transports the actual complexes and homology.
-/

noncomputable section
namespace FourPapers.Sublattice

open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
variable {B C : Family V}

def quotientFaceEquivOfContains (h : ∀ v, Contains B v ↔ Contains C v)
    (a : Exponent V) (i : ℕ) :
    Simplicial.Chains (k := k) (quotientKoszulFaces B a) i ≃ₗ[k]
      Simplicial.Chains (k := k) (quotientKoszulFaces C a) i :=
  LinearEquiv.ofEq _ _ (congrArg (fun P => Simplicial.Chains (k := k) P i)
    (quotientKoszulFaces_eq_of_contains h a))

@[simp] lemma quotientFaceEquivOfContains_val (h : ∀ v, Contains B v ↔ Contains C v)
    (a : Exponent V) (i : ℕ)
    (z : Simplicial.Chains (k := k) (quotientKoszulFaces B a) i) :
    (quotientFaceEquivOfContains (k := k) h a i z).val = z.val := rfl

/-- A genuine chain isomorphism, with the projected exterior differential checked. -/
def quotientFaceIsoOfContains (h : ∀ v, Contains B v ↔ Contains C v) (a : Exponent V) :
    quotientFaceComplex (k := k) B a ≅ quotientFaceComplex C a :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (quotientFaceEquivOfContains (k := k) h a i).toModuleIso) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      rw [quotientFaceComplex_d,quotientFaceComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      change
        (quotientFaceDifferential C a j
          (quotientFaceEquivOfContains (k := k) h a (j + 1) z)).val =
        (quotientFaceEquivOfContains (k := k) h a j
          (quotientFaceDifferential B a j z)).val
      simp only [quotientFaceEquivOfContains_val,
        quotientFaceDifferential_val,quotientFaceProjection_eq_of_contains h])

/-- Equality of ideal membership induces an isomorphism of the actual homogeneous
Koszul complexes; this is used when replacing lexicographic ratios by minimal ones. -/
def quotientHomogeneousIsoOfContains (h : ∀ v, Contains B v ↔ Contains C v) (a : Exponent V) :
    quotientHomogeneousComplex (k := k) B a ≅ quotientHomogeneousComplex C a :=
  (quotientFacesIso B a).symm ≪≫ quotientFaceIsoOfContains h a ≪≫ quotientFacesIso C a

end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientDegreeHomology -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open FourPapers.FilteredHomology
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The actual cycles of exterior degree p in one fine quotient strand. -/
def ClosedGraphDegreeCycles (B : Family V) (α : Exponent V) (p : ℕ) :
    Submodule k (TotalFaceModule (k := k) (quotientKoszulFaces B α)) :=
  LinearMap.ker (quotientTotalDifferential B α) ⊓ totalFacePiece (quotientKoszulFaces B α) p

instance closedGraphDegreeCyclesAddCommGroup (B : Family V) (α : Exponent V) (p : ℕ) :
    AddCommGroup (ClosedGraphDegreeCycles (k := k) B α p) :=
  Submodule.addCommGroup (R := k)
    (M := TotalFaceModule (k := k) (quotientKoszulFaces B α)) (ClosedGraphDegreeCycles B α p)

instance closedGraphDegreeCyclesModule (B : Family V) (α : Exponent V) (p : ℕ) :
    Module k (ClosedGraphDegreeCycles (k := k) B α p) :=
  Submodule.module (R := k)
    (M := TotalFaceModule (k := k) (quotientKoszulFaces B α)) (ClosedGraphDegreeCycles B α p)

/-- Use the canonical submodule quotient on the explicitly named cycle carrier. -/
local instance closedGraphDegreeCycles_hasQuotient (B : Family V) (α : Exponent V) (p : ℕ) :
    HasQuotient ↥(ClosedGraphDegreeCycles (k := k) B α p)
      (Submodule k ↥(ClosedGraphDegreeCycles (k := k) B α p)) :=
  @Submodule.hasQuotient k ↥(ClosedGraphDegreeCycles (k := k) B α p)
    inferInstance inferInstance inferInstance

/-- The actual boundary map from degree p+1, with both cycle and degree
membership proved in its codomain. -/
def closedGraphDegreeBoundary (B : Family V) (α : Exponent V) (p : ℕ) :
    totalFacePiece (k := k) (quotientKoszulFaces B α) (p + 1) →ₗ[k]
      ClosedGraphDegreeCycles (k := k) B α p :=
  ((quotientTotalDifferential B α).domRestrict
    (totalFacePiece (quotientKoszulFaces B α) (p + 1))).codRestrict _
    (fun x => ⟨LinearMap.congr_fun (quotientTotalDifferential_comp B α) x.val,
      quotientTotalDifferential_lowers B α p x.val x.property⟩)

/-- Literal homogeneous homology, retaining the exact exterior degree. -/
def ClosedGraphDegreeHomology (B : Family V) (α : Exponent V) (p : ℕ) :=
  ↥(ClosedGraphDegreeCycles (k := k) B α p) ⧸
    LinearMap.range (closedGraphDegreeBoundary (k := k) B α p)

instance closedGraphDegreeHomologyAddCommGroup (B : Family V) (α : Exponent V) (p : ℕ) :
    AddCommGroup (ClosedGraphDegreeHomology (k := k) B α p) :=
  Submodule.Quotient.addCommGroup (R := k) (M := ClosedGraphDegreeCycles (k := k) B α p)
    (LinearMap.range (closedGraphDegreeBoundary (k := k) B α p))

instance closedGraphDegreeHomologyModule (B : Family V) (α : Exponent V) (p : ℕ) :
    Module k (ClosedGraphDegreeHomology (k := k) B α p) :=
  Submodule.Quotient.module (R := k) (M := ClosedGraphDegreeCycles (k := k) B α p)
    (LinearMap.range (closedGraphDegreeBoundary (k := k) B α p))


end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientPieceHomology -/
section

/-! # Cycles and boundaries in the homogeneous quotient Koszul complex

The actual finite face basis and the cycle/boundary quotient are identified
with the nonnegative complex used by the generic splitting construction.
The degree-zero comparison uses the proved zero outgoing differential.
No graph hypothesis or freeness of homology is required.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

local instance quotientPieceCyclesAddCommGroup (B : Family V) (α : Exponent V) (p : ℕ) :
    AddCommGroup (FourPapers.ProjectiveComplexSplitting.cycles (R := k)
      (fun i => ↥((quotientTotalData (k := k) B α).piece i))
      (quotientTotalData B α).differential p) :=
  Submodule.addCommGroup (R := k) (M := ↥((quotientTotalData (k := k) B α).piece p)) _

local instance quotientPieceCyclesModule (B : Family V) (α : Exponent V) (p : ℕ) :
    Module k (FourPapers.ProjectiveComplexSplitting.cycles (R := k)
      (fun i => ↥((quotientTotalData (k := k) B α).piece i))
      (quotientTotalData B α).differential p) :=
  Submodule.module (R := k) (M := ↥((quotientTotalData (k := k) B α).piece p)) _

def quotientTotalPieceBasis (B : Family V) (α : Exponent V) (p : ℕ) :
    Module.Basis (QuotientFaceIndex B α p) k
      (totalFacePiece (k := k) (quotientKoszulFaces B α) p) :=
  (quotientFaceBasis B α p).map (totalFacePieceEquiv (quotientKoszulFaces B α) p).symm

@[simp] lemma quotientTotalPieceBasis_val (B : Family V) (α : Exponent V) (p : ℕ)
    (F : QuotientFaceIndex B α p) :
    (quotientTotalPieceBasis (k := k) B α p F).val =
      totalFaceBasis (quotientKoszulFaces B α) ⟨F.val, F.property.1⟩ := by
  apply Subtype.ext
  rw [totalFaceBasis_val]
  change (quotientFaceBasis (k := k) B α p F).val = Simplicial.basis F.val
  exact quotientFaceBasis_val B α p F

/-- The nonnegative complex's cycle module includes degree zero in full.
Its identification with the intersection model is proved also in degree
zero, using the actual vanishing of the outgoing exterior differential. -/
def quotientPieceCyclesEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    FourPapers.ProjectiveComplexSplitting.cycles (R := k)
      (fun i => ↥((quotientTotalData (k := k) B α).piece i))
      (quotientTotalData B α).differential p ≃ₗ[k]
      ClosedGraphDegreeCycles (k := k) B α p := by
  cases p with
  | zero =>
      exact
        { toFun := fun x => ⟨x.val.val,
            ⟨quotientTotalDifferential_zero_degree B α x.val.val x.val.property, x.val.property⟩⟩
          invFun := fun x => ⟨⟨x.val, x.property.2⟩, trivial⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
  | succ p =>
      exact
        { toFun := fun x => ⟨x.val.val, ⟨congrArg Subtype.val x.property, x.val.property⟩⟩
          invFun := fun x => ⟨⟨x.val, x.property.2⟩, Subtype.ext x.property.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }

@[simp] lemma quotientPieceCyclesEquiv_val (B : Family V) (α : Exponent V) (p : ℕ)
    (x : FourPapers.ProjectiveComplexSplitting.cycles (R := k)
      (fun i => ↥((quotientTotalData (k := k) B α).piece i))
      (quotientTotalData B α).differential p) :
    (quotientPieceCyclesEquiv (k := k) B α p x).val = x.val.val := by
  cases p <;> rfl

lemma quotientPieceCyclesEquiv_boundaries (B : Family V) (α : Exponent V) (p : ℕ) :
    (FourPapers.ProjectiveComplexSplitting.boundaries (R := k)
      (fun i => ↥((quotientTotalData (k := k) B α).piece i))
      (quotientTotalData B α).differential
      (quotientTotalData B α).differential_comp p).map
        (quotientPieceCyclesEquiv B α p).toLinearMap =
      LinearMap.range (closedGraphDegreeBoundary B α p) := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact (quotientPieceCyclesEquiv_val (k := k) B α p
      (FourPapers.ProjectiveComplexSplitting.toCycles (R := k)
        (fun i => ↥((quotientTotalData (k := k) B α).piece i))
        (quotientTotalData B α).differential (quotientTotalData B α).differential_comp p y)).symm
  · rintro ⟨y, rfl⟩
    refine ⟨FourPapers.ProjectiveComplexSplitting.toCycles (R := k)
      (fun i => ↥((quotientTotalData (k := k) B α).piece i))
      (quotientTotalData B α).differential (quotientTotalData B α).differential_comp p y,
      ⟨y, rfl⟩, ?_⟩
    apply Subtype.ext
    exact quotientPieceCyclesEquiv_val (k := k) B α p
      (FourPapers.ProjectiveComplexSplitting.toCycles (R := k)
        (fun i => ↥((quotientTotalData (k := k) B α).piece i))
        (quotientTotalData B α).differential (quotientTotalData B α).differential_comp p y)

set_option backward.isDefEq.respectTransparency true in
def quotientPieceHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    FourPapers.ProjectiveComplexSplitting.Homology (R := k)
      (fun i => ↥((quotientTotalData (k := k) B α).piece i))
      (quotientTotalData B α).differential
      (quotientTotalData B α).differential_comp p ≃ₗ[k]
      ClosedGraphDegreeHomology (k := k) B α p := by
  unfold ClosedGraphDegreeHomology
  exact FourPapers.ProjectiveComplexSplitting.homologyEquivOfCycles (R := k)
    (fun i => ↥((quotientTotalData (k := k) B α).piece i))
    (quotientTotalData B α).differential (quotientTotalData B α).differential_comp
    (N := ↥(ClosedGraphDegreeCycles (k := k) B α p))
    p
    (LinearMap.range (closedGraphDegreeBoundary (k := k) B α p))
    (quotientPieceCyclesEquiv (k := k) B α p)
    (quotientPieceCyclesEquiv_boundaries (k := k) B α p)

end FourPapers.Sublattice

end
end
end


end
