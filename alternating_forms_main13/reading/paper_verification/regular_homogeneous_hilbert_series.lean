module

public import PaperVerification.GradedInjectiveQuotient
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Hilbert series of an actual quotient by a homogeneous regular sequence

The result is proved by successively quotienting the module by each scalar.
At every step the grading is the image of the original homogeneous pieces.
The final linear equivalence is Mathlib's quotient-by-a-list equivalence, so
this construction concerns the literal quotient by the generated ideal.
-/

@[expose] public section
noncomputable section
open scoped Pointwise PowerSeries

namespace PaperVerification.RegularHomogeneousHilbertSeries

open GradedInjectiveQuotient

universe u v w

variable {K : Type u} {R : Type v} {M : Type w}
  [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]

/-- Scalar multiplication, viewed over the coefficient field. -/
def scalarMap (r : R) : M →ₗ[K] M :=
  (LinearMap.lsmul R M r).restrictScalars K

@[simp] theorem scalarMap_apply (r : R) (x : M) : scalarMap (K:=K) r x = r • x := rfl

/-- The image of scalar multiplication is the actual scalar-generated submodule. -/
theorem smulTop_restrictScalars_eq_range (r : R) :
    (r • (⊤ : Submodule R M)).restrictScalars K =
      LinearMap.range (scalarMap (K:=K) (M:=M) r) := by
  ext x
  change x ∈ r • (⊤ : Submodule R M) ↔ _
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    LinearMap.mem_range, scalarMap_apply]

variable (G : TauCeti.InternalGrading K M ℕ)

/-- A scalar image is homogeneous when scalar multiplication has one degree. -/
theorem smulTop_homogeneous (r : R) (e : ℕ)
    (hr : TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) r) G.piece G.piece e) :
    DirectSum.SetLike.IsHomogeneous G.piece (r • (⊤ : Submodule R M)) := by
  intro d x hx
  have hx' : x ∈ LinearMap.range (scalarMap (K:=K) r) := by
    rw [← smulTop_restrictScalars_eq_range]
    exact hx
  have h := hr.isHomogeneous_range d hx'
  rw [← smulTop_restrictScalars_eq_range] at h
  exact h

/-- A homogeneous scalar acts with the same degree on every homogeneous quotient. -/
theorem scalarMap_quotient_homogeneous (U : Submodule R M)
    (hU : DirectSum.SetLike.IsHomogeneous G.piece U) (r : R) (e : ℕ)
    (hr : TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) r) G.piece G.piece e) :
    TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) r)
      (G.quotient U hU).piece (G.quotient U hU).piece e := by
  apply TauCeti.LinearMap.isHomogeneous_def.mpr
  intro d x hx
  obtain ⟨y,hy,rfl⟩ := (G.mem_quotient_piece_iff U hU).mp hx
  exact G.mk_mem_quotient_piece U hU (hr.map_mem hy)

/-- Transport across an actual linear equivalence does not change the Hilbert series. -/
theorem hilbertSeries_map {N : Type*} [AddCommGroup N] [Module K N]
    (E : M ≃ₗ[K] N) : hilbertSeries (G.map E) = hilbertSeries G := by
  apply PowerSeries.ext
  intro d
  simp only [hilbertSeries, PowerSeries.coeff_mk]
  have hd : Module.finrank K ((G.map E).piece d) = Module.finrank K (G.piece d) := by
    rw [TauCeti.InternalGrading.map_piece]
    exact E.finrank_map_eq (G.piece d)
  exact congrArg (fun n : ℕ => (n:ℤ)) hd

/-- The quotient by the zero submodule retains every graded-piece dimension. -/
theorem hilbertSeries_quotient_bot
    (hbot : DirectSum.SetLike.IsHomogeneous G.piece (⊥ : Submodule R M)) :
    hilbertSeries (G.quotient (⊥ : Submodule R M) hbot) = hilbertSeries G := by
  apply PowerSeries.ext
  intro d
  have hi : Function.Injective (quotientPieceMap G (⊥ : Submodule R M) hbot d) := by
    intro x y h
    apply Subtype.ext
    have hxy := congrArg Subtype.val h
    change (Submodule.Quotient.mk (x:M) : M ⧸ (⊥ : Submodule R M)) =
      Submodule.Quotient.mk (y:M) at hxy
    simpa only [Submodule.Quotient.eq, Submodule.mem_bot, sub_eq_zero] using hxy
  have E := LinearEquiv.ofBijective (quotientPieceMap G (⊥ : Submodule R M) hbot d)
    ⟨hi, quotientPieceMap_surjective G (⊥ : Submodule R M) hbot d⟩
  simpa only [hilbertSeries, PowerSeries.coeff_mk] using
    congrArg (fun n : ℕ => (n:ℤ)) E.finrank_eq.symm

/-- The recursive quotient equivalence sends a class to its successive classes. -/
theorem quotientConsEquiv_mk (r : R) (rs : List R) (x : M) :
    Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.Quotient.mk x) := rfl

/-- The quotient has its original image grading and the regular-sequence product
formula. All homogeneous pieces of the initial module may be infinite in total;
only each individual piece is required to be finite-dimensional. -/
theorem exists_quotient_grading_hilbertSeries
    (rs : List (R × ℕ))
    (hhom : ∀ re ∈ rs,
      TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) re.1) G.piece G.piece re.2)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M (rs.map Prod.fst))
    (hfinite : ∀ d, FiniteDimensional K (G.piece d)) :
    ∃ H : TauCeti.InternalGrading K
        (M ⧸ (Ideal.ofList (rs.map Prod.fst) • ⊤ : Submodule R M)) ℕ,
      (∀ d, H.piece d = (G.piece d).map
        ((Ideal.ofList (rs.map Prod.fst) • ⊤ : Submodule R M).mkQ.restrictScalars K)) ∧
      hilbertSeries H = hilbertSeries G * (rs.map (fun re =>
        (1-PowerSeries.X^re.2 : ℤ⟦X⟧))).prod := by
  induction rs generalizing M with
  | nil =>
      have hbot : DirectSum.SetLike.IsHomogeneous G.piece (⊥ : Submodule R M) := by
        intro d x hx
        have hx0 : x=0 := hx
        simp [hx0]
      let U₀ : Submodule R M := Ideal.ofList (([] : List (R × ℕ)).map Prod.fst) • ⊤
      have hzero : (⊥ : Submodule R M)=U₀ := by simp [U₀]
      let E := (Submodule.quotEquivOfEq (⊥ : Submodule R M) U₀ hzero).restrictScalars K
      refine ⟨(G.quotient ⊥ hbot).map E, ?_, ?_⟩
      · intro d
        rw [TauCeti.InternalGrading.map_piece, TauCeti.InternalGrading.quotient_piece,
          ← Submodule.map_comp]
        rfl
      · rw [hilbertSeries_map, hilbertSeries_quotient_bot]
        simp
  | cons re rs ih =>
      rcases re with ⟨r,e⟩
      have hr := hhom (r,e) (List.mem_cons_self ..)
      have hrest := fun re hre => hhom re (List.mem_cons_of_mem _ hre)
      have hregular := (RingTheory.Sequence.isWeaklyRegular_cons_iff M r
        (rs.map Prod.fst)).mp (by simpa only [List.map_cons] using hreg)
      let U : Submodule R M := r • ⊤
      let hU := smulTop_homogeneous G r e hr
      let G₁ := G.quotient U hU
      have hf₁ : ∀ d, FiniteDimensional K (G₁.piece d) := by
        intro d
        letI := hfinite d
        exact quotientPiece_finite G U hU d
      have hh₁ : ∀ re ∈ rs,
          TauCeti.LinearMap.IsHomogeneous (scalarMap (K:=K) re.1) G₁.piece G₁.piece re.2 := by
        intro re hre
        exact scalarMap_quotient_homogeneous G U hU re.1 re.2 (hrest re hre)
      obtain ⟨H₁, hpieces₁, hseries₁⟩ := ih G₁ hh₁ hregular.2 hf₁
      let E := (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r
        (rs.map Prod.fst)).restrictScalars K
      let H := H₁.map E.symm
      refine ⟨H, ?_, ?_⟩
      · intro d
        dsimp only [H]
        rw [TauCeti.InternalGrading.map_piece, hpieces₁]
        dsimp only [G₁]
        rw [TauCeti.InternalGrading.quotient_piece]
        rw [← Submodule.map_comp, ← Submodule.map_comp]
        congr 1
      · have hs₁ : hilbertSeries G₁ = hilbertSeries G * (1-PowerSeries.X^e) :=
          hilbertSeries_quotient G U hU (scalarMap r) e hr hregular.1
            (smulTop_restrictScalars_eq_range r) hfinite
        rw [hilbertSeries_map, hseries₁, hs₁]
        simp only [List.map_cons, List.prod_cons]
        ring

end PaperVerification.RegularHomogeneousHilbertSeries
