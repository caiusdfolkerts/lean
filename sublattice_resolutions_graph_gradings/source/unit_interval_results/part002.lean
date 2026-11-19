module
public import unit_fixed_face_grading
public import shared_results.part023
public import unit_interval_results.part001

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealQuotientDegreeEquiv -/
section

/-!
# The full homogeneous ideal-to-quotient homology shift

In a nonzero fine degree, creation by a variable occurring in that degree
contracts the full polynomial strand. The connecting map sends a quotient
cycle to the boundary of its literal exterior representative. The proof
below constructs its inverse modulo actual boundaries; it establishes an
equivalence of modules, rather than only nonvanishing transfer.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def IdealFaceDegreeCycles (B : Family V) (α : Exponent V) (p : ℕ) :
    Submodule k (TotalFaceModule (k := k) (koszulFaces B α)) :=
  LinearMap.ker (idealTotalDifferential (koszulFaces_downward B α)) ⊓
    totalFacePiece (koszulFaces B α) p

instance idealFaceDegreeCyclesAddCommGroup (B : Family V) (α : Exponent V) (p : ℕ) :
    AddCommGroup (IdealFaceDegreeCycles (k := k) B α p) :=
  Submodule.addCommGroup (R := k)
    (M := TotalFaceModule (k := k) (koszulFaces B α)) (IdealFaceDegreeCycles B α p)

instance idealFaceDegreeCyclesModule (B : Family V) (α : Exponent V) (p : ℕ) :
    Module k (IdealFaceDegreeCycles (k := k) B α p) :=
  Submodule.module (R := k)
    (M := TotalFaceModule (k := k) (koszulFaces B α)) (IdealFaceDegreeCycles B α p)

/-- Use Mathlib's canonical quotient on the explicitly named cycle carrier. -/
local instance idealFaceDegreeCycles_hasQuotient (B : Family V) (α : Exponent V) (p : ℕ) :
    HasQuotient ↥(IdealFaceDegreeCycles (k := k) B α p)
      (Submodule k ↥(IdealFaceDegreeCycles (k := k) B α p)) :=
  @Submodule.hasQuotient k ↥(IdealFaceDegreeCycles (k := k) B α p)
    inferInstance inferInstance inferInstance

def idealFaceDegreeBoundary (B : Family V) (α : Exponent V) (p : ℕ) :
    totalFacePiece (k := k) (koszulFaces B α) (p+1) →ₗ[k]
      IdealFaceDegreeCycles (k := k) B α p :=
  ((idealTotalDifferential (koszulFaces_downward B α)).domRestrict
    (totalFacePiece (koszulFaces B α) (p+1))).codRestrict _ (by
      intro x
      refine ⟨?_, Simplicial.boundary_mem (koszulFaces_downward B α) x.property⟩
      apply Subtype.ext
      exact Simplicial.boundary_boundary x.val.val)

abbrev IdealFaceDegreeHomology (B : Family V) (α : Exponent V) (p : ℕ) :=
  ↥(IdealFaceDegreeCycles (k := k) B α p) ⧸
    LinearMap.range (idealFaceDegreeBoundary (k := k) B α p)

def idealFacePieceCyclesEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    ProjectiveComplexSplitting.cycles
      (fun i => ↥((idealTotalData (k := k) (koszulFaces_downward B α)).piece i))
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential p ≃ₗ[k]
        IdealFaceDegreeCycles (k := k) B α p := by
  cases p with
  | zero =>
      exact
        { toFun := fun x => ⟨x.val.val, ⟨Subtype.ext
            (Simplicial.boundary_zero_degree_zero x.val.property), x.val.property⟩⟩
          invFun := fun x => ⟨⟨x.val,x.property.2⟩,trivial⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
  | succ p =>
      exact
        { toFun := fun x => ⟨x.val.val,⟨congrArg Subtype.val x.property,x.val.property⟩⟩
          invFun := fun x => ⟨⟨x.val,x.property.2⟩,Subtype.ext x.property.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }

theorem idealFacePieceCyclesEquiv_boundaries (B : Family V) (α : Exponent V) (p : ℕ) :
    (ProjectiveComplexSplitting.boundaries
      (fun i => ↥((idealTotalData (k := k) (koszulFaces_downward B α)).piece i))
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential_comp p).map
        (idealFacePieceCyclesEquiv (k := k) B α p).toLinearMap =
          LinearMap.range (idealFaceDegreeBoundary (k := k) B α p) := by
  have hmap (y : totalFacePiece (k := k) (koszulFaces B α) (p+1)) :
      idealFacePieceCyclesEquiv (k := k) B α p
        (ProjectiveComplexSplitting.toCycles
          (fun i => ↥((idealTotalData (k := k) (koszulFaces_downward B α)).piece i))
          (idealTotalData (k := k) (koszulFaces_downward B α)).differential
          (idealTotalData (k := k) (koszulFaces_downward B α)).differential_comp p y) =
        idealFaceDegreeBoundary (k := k) B α p y := by
    cases p <;> rfl
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    exact ⟨y,(hmap y).symm⟩
  · rintro ⟨y,rfl⟩
    refine ⟨ProjectiveComplexSplitting.toCycles
      (fun i => ↥((idealTotalData (k := k) (koszulFaces_downward B α)).piece i))
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential_comp p y,
      ⟨y,rfl⟩,hmap y⟩

def idealFacePieceHomologyEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    ProjectiveComplexSplitting.Homology
      (fun i => ↥((idealTotalData (k := k) (koszulFaces_downward B α)).piece i))
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential_comp p ≃ₗ[k]
        IdealFaceDegreeHomology (k := k) B α p := by
  let C := fun i => ↥((idealTotalData (k := k) (koszulFaces_downward B α)).piece i)
  let D := (idealTotalData (k := k) (koszulFaces_downward B α)).differential
  let Z : Submodule k (C p) := ProjectiveComplexSplitting.cycles C D p
  letI : AddCommGroup ↥Z := Submodule.addCommGroup (R := k) (M := C p) Z
  letI : Module k ↥Z := Submodule.module (R := k) (M := C p) Z
  exact Submodule.Quotient.equiv (R := k) (R₂ := k)
    (ProjectiveComplexSplitting.boundaries C D
      (idealTotalData (k := k) (koszulFaces_downward B α)).differential_comp p)
    (LinearMap.range (idealFaceDegreeBoundary (k := k) B α p))
    (idealFacePieceCyclesEquiv (k := k) B α p)
    (idealFacePieceCyclesEquiv_boundaries (k := k) B α p)

def idealCategoricalFaceDegreeEquiv (B : Family V) (α : Exponent V) (p : ℕ) :
    (homogeneousComplex (k := k) B α).homology p ≃ₗ[k]
      IdealFaceDegreeHomology (k := k) B α p :=
  (((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) p).mapIso
      (idealTotalKoszulIso (k := k) B α).symm).toLinearEquiv.trans
        (submoduleComplexHomologyEquiv (idealTotalData (k := k) (koszulFaces_downward B α)) p)).trans
          (idealFacePieceHomologyEquiv (k := k) B α p)

/-- The connecting map is the boundary of the literal quotient-cycle
representative, which belongs to the ideal because its projection is zero. -/
def quotientIdealConnectingCycles (B : Family V) (α : Exponent V) (p : ℕ) :
    ClosedGraphDegreeCycles (k := k) B α (p+1) →ₗ[k]
      IdealFaceDegreeCycles (k := k) B α p where
  toFun z := by
    have hzfull : z.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
      Simplicial.chains_mono (fun _ hs => hs.1) (p+1) z.property.2
    have hmem : Simplicial.boundary z.val.val ∈ Simplicial.Chains (koszulFaces B α) p :=
      quotientFaceProjection_zero_mem_ideal_degree B α p
        (Simplicial.boundary_mem (fullKoszulFaces_downward α) hzfull)
        (congrArg Subtype.val z.property.1)
    exact ⟨⟨Simplicial.boundary z.val.val,chains_mem_basisSpan hmem⟩,
      ⟨Subtype.ext (Simplicial.boundary_boundary z.val.val),hmem⟩⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add Simplicial.boundary x.val.val y.val.val
  map_smul' c x := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul Simplicial.boundary c x.val.val

@[simp] theorem quotientIdealConnectingCycles_val (B : Family V) (α : Exponent V) (p : ℕ)
    (z : ClosedGraphDegreeCycles (k := k) B α (p+1)) :
    (quotientIdealConnectingCycles (k := k) B α p z).val.val = Simplicial.boundary z.val.val := rfl

theorem quotientIdealConnectingCycles_boundary (B : Family V) (α : Exponent V) (p : ℕ)
    (z : totalFacePiece (k := k) (quotientKoszulFaces B α) (p+2)) :
    ∃ y, idealFaceDegreeBoundary (k := k) B α p y =
      quotientIdealConnectingCycles (k := k) B α p (closedGraphDegreeBoundary (k := k) B α (p+1) z) := by
  have hzfull : z.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+2) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+2) z.property
  have hd := Simplicial.boundary_mem (fullKoszulFaces_downward α) hzfull
  have hy := quotientFaceProjection_sub_mem_ideal_degree B α (p+1) hd
  refine ⟨⟨⟨_,chains_mem_basisSpan hy⟩,hy⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change Simplicial.boundary
      (quotientFaceProjection B α (Simplicial.boundary z.val.val) -
        Simplicial.boundary z.val.val) =
    Simplicial.boundary (quotientFaceProjection B α (Simplicial.boundary z.val.val))
  rw [map_sub,Simplicial.boundary_boundary,sub_zero]

def quotientIdealConnecting (B : Family V) (α : Exponent V) (p : ℕ) :
    ClosedGraphDegreeHomology (k := k) B α (p+1) →ₗ[k]
      IdealFaceDegreeHomology (k := k) B α p :=
  (LinearMap.range (closedGraphDegreeBoundary (k := k) B α (p+1))).liftQ
    ((LinearMap.range (idealFaceDegreeBoundary (k := k) B α p)).mkQ.comp
      (quotientIdealConnectingCycles (k := k) B α p)) (by
        rintro x ⟨z,rfl⟩
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact quotientIdealConnectingCycles_boundary (k := k) B α p z)

@[simp] theorem quotientIdealConnecting_mk (B : Family V) (α : Exponent V) (p : ℕ)
    (z : ClosedGraphDegreeCycles (k := k) B α (p+1)) :
    quotientIdealConnecting (k := k) B α p (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk (quotientIdealConnectingCycles (k := k) B α p z) :
        IdealFaceDegreeHomology (k := k) B α p) := rfl

theorem quotientIdealConnecting_injective (B : Family V) (α : Exponent V)
    (e : V) (he : 0 < α e) (p : ℕ) :
    Function.Injective (quotientIdealConnecting (k := k) B α p) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨z,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary (k := k) B α (p+1))).mkQ_surjective x
  change quotientIdealConnecting (k := k) B α p (Submodule.Quotient.mk z) = 0 at hx
  rw [quotientIdealConnecting_mk] at hx
  obtain ⟨y,hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
  have hdy : Simplicial.boundary y.val.val = Simplicial.boundary z.val.val :=
    congrArg (fun c : IdealFaceDegreeCycles (k := k) B α p => c.val.val) hy
  have hzfull : z.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+1) z.property.2
  have hyfull : y.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+1) y.property
  have hdiff := (Simplicial.Chains (k := k) (fullKoszulFaces α) (p+1)).sub_mem hzfull hyfull
  have hclosed : Simplicial.boundary (z.val.val-y.val.val) = 0 := by
    rw [map_sub,hdy,sub_self]
  have hc := creation_mem_chains e (fun _ hs => fullKoszulFaces_insert he hs) hdiff
  let v : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α (Simplicial.creation e (z.val.val-y.val.val)),
      relativeProjection_mem _ _ _ _⟩
  have hv : v ∈ totalFacePiece (quotientKoszulFaces B α) (p+2) :=
    quotientFaceProjection_degree B α (p+2) hc
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨⟨v,hv⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
      (quotientFaceProjection B α (Simplicial.creation e (z.val.val-y.val.val)))) = z.val.val
  rw [quotientFaceProjection_boundary B α (chains_mem_basisSpan hc),
    Simplicial.boundary_creation,hclosed,map_zero,sub_zero,map_sub,
    quotientFaceProjection_zero_on_ideal B α y.val.property,sub_zero]
  exact relativeProjection_eq_self z.val.property

theorem quotientIdealConnecting_surjective (B : Family V) (α : Exponent V)
    (e : V) (he : 0 < α e) (p : ℕ) :
    Function.Surjective (quotientIdealConnecting (k := k) B α p) := by
  intro x
  obtain ⟨c,rfl⟩ := (LinearMap.range (idealFaceDegreeBoundary (k := k) B α p)).mkQ_surjective x
  have hcfull : c.val.val ∈ Simplicial.Chains (fullKoszulFaces α) p :=
    Simplicial.chains_mono (fun _ hs => hs.1) p c.property.2
  have hccycle : Simplicial.boundary c.val.val = 0 := congrArg Subtype.val c.property.1
  let v := Simplicial.creation e c.val.val
  have hvfull : v ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    creation_mem_chains e (fun _ hs => fullKoszulFaces_insert he hs) hcfull
  have hdv : Simplicial.boundary v = c.val.val := by
    dsimp only [v]
    rw [Simplicial.boundary_creation,hccycle,map_zero,sub_zero]
  let z : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α v,relativeProjection_mem _ _ _ _⟩
  have hz : z ∈ totalFacePiece (quotientKoszulFaces B α) (p+1) :=
    quotientFaceProjection_degree B α (p+1) hvfull
  have hdz : quotientTotalDifferential B α z = 0 := by
    apply Subtype.ext
    change quotientFaceProjection B α (Simplicial.boundary (quotientFaceProjection B α v)) = 0
    rw [quotientFaceProjection_boundary B α (chains_mem_basisSpan hvfull),hdv]
    exact quotientFaceProjection_zero_on_ideal B α c.val.property
  let zc : ClosedGraphDegreeCycles (k := k) B α (p+1) := ⟨z,hdz,hz⟩
  refine ⟨Submodule.Quotient.mk zc,?_⟩
  rw [quotientIdealConnecting_mk]
  apply (Submodule.Quotient.eq _).mpr
  have hy := quotientFaceProjection_sub_mem_ideal_degree B α (p+1) hvfull
  refine ⟨⟨⟨_,chains_mem_basisSpan hy⟩,hy⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change Simplicial.boundary (quotientFaceProjection B α v-v) =
    Simplicial.boundary (quotientFaceProjection B α v)-c.val.val
  rw [map_sub,hdv]

/-- The connecting homomorphism is an actual module equivalence in every
nonzero fine degree, over an arbitrary commutative coefficient ring. -/
def quotientIdealDegreeEquiv (B : Family V) (α : Exponent V)
    (e : V) (he : 0 < α e) (p : ℕ) :
    ClosedGraphDegreeHomology (k := k) B α (p+1) ≃ₗ[k]
      IdealFaceDegreeHomology (k := k) B α p :=
  LinearEquiv.ofBijective (quotientIdealConnecting (k := k) B α p)
    ⟨quotientIdealConnecting_injective (k := k) B α e he p,
      quotientIdealConnecting_surjective (k := k) B α e he p⟩

section Field
variable {K : Type u} [Field K]

/-- The full numerical shift, with the actual quotient and ideal Tor
definitions on the two sides. No proper-ideal premise is needed away from
fine degree zero. -/
theorem quotientBettiNumber_succ_eq_ideal (B : Family V) (α : Exponent V)
    (hα : α ≠ 0) (p : ℕ) :
    quotientBettiNumber (k := K) B α (p+1) = bettiNumber (k := K) B α p := by
  obtain ⟨e,he⟩ : ∃ e,0 < α e := by
    by_contra! hh
    apply hα
    ext e
    exact Nat.eq_zero_of_le_zero (hh e)
  rw [quotientBettiNumber_eq_homology,
    (quotientCategoricalDegreeHomologyEquiv (k := K) B α (p+1)).finrank_eq,
    (quotientIdealDegreeEquiv (k := K) B α e he p).finrank_eq]
  exact (idealCategoricalFaceDegreeEquiv (k := K) B α p).finrank_eq.symm.trans
    (gradedTorIso (k := K) B α p).toLinearEquiv.finrank_eq

end Field
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientIdealDegreeEquiv
#print axioms FourPapers.Sublattice.quotientBettiNumber_succ_eq_ideal

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealQuotientOrdinaryShift -/
section

/-! # The full ideal-to-quotient shift in the ordinary grading

The equality follows by summing the actual fine-degree connecting
isomorphisms. The positive internal degree hypothesis removes exactly
the polynomial ring's degree-zero free summand.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option Elab.async false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The ordinary Betti numbers of a quotient are those of its ideal one
homological degree earlier in every positive internal degree. -/
theorem ordinaryQuotientBettiNumber_succ_eq_ideal
    (B : Family V) (Q p : ℕ) (hQ : 0 < Q) :
    ordinaryQuotientBettiNumber (k := k) B Q (p+1) =
      ordinaryMonomialBettiNumber (k := k) B Q p := by
  rw [ordinaryQuotientBettiNumber_eq_sum, ordinaryMonomialBettiNumber_eq_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply quotientBettiNumber_succ_eq_ideal
  intro hα
  have hd := α.property
  rw [hα, map_zero] at hd
  omega

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.ordinaryQuotientBettiNumber_succ_eq_ideal

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerColonBetti -/
section

/-! # The complete first-power colon sum in the ordinary grading

A one-term multichain is literally a generator. Specializing the proved
all-powers decomposition and the genuine ideal-to-quotient connecting
isomorphism gives the generator filtration formula used in Lemma 6.1.
The statements retain every variable restriction and every homological
degree; the coefficient ideals are the actual predecessor ideals.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- The literal one-term weak chain attached to a generator. -/
def finiteOneChain (a : E) : FiniteMultichain n E 1 :=
  ⟨fun _ => a, fun _ _ _ => le_rfl⟩

/-- A one-term multichain has exactly its sole generator as data. -/
def finiteOneChainEquiv : FiniteMultichain n E 1 ≃ E where
  toFun w := w.val 0
  invFun := finiteOneChain
  left_inv w := by
    apply Subtype.ext
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  right_inv _ := rfl

@[simp] theorem finiteOneChain_coefficient (a : E) :
    finiteChainCoefficientFamily.{u} n (finiteOneChain a) =
      finitePredecessorFamily n E a.val := by
  ext g
  change g ∈ (Finset.univ : Finset (Fin 1)).biUnion
    (fun i => finitePredecessorFamily n E ((finiteOneChain a).val i).val) ↔ _
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and, finiteOneChain]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨0,h⟩⟩

/-- The exact quotient Betti sum over predecessor colons. The row count
is positive precisely to exclude the unit ideal's degree-zero generator. -/
theorem firstPowerQuotientBetti_colon_sum {k : Type u} [Field k]
    (hE : finiteLatticeClosed n E) (hd : 0 < d) (q p : ℕ) :
    ordinaryQuotientBettiNumber (k := k) (finiteRowFamily n E) (d+q) (p+1) =
      ∑ a : E, ordinaryQuotientBettiNumber (k := k)
        (finitePredecessorFamily n E a.val) q p := by
  rw [ordinaryQuotientBettiNumber_succ_eq_ideal _ _ _ (by omega)]
  have h := ordinaryPowerBetti_chain_sum (k := k) hE 1 (by omega) q p
  simp only [one_mul, exponentPowerFamily_one] at h
  rw [h]
  exact Fintype.sum_equiv (finiteOneChainEquiv (n := n) (E := E)) _ _ (by
    intro w
    have hw := (finiteOneChainEquiv (n := n) (E := E)).symm_apply_apply w
    change finiteOneChain ((finiteOneChainEquiv (n := n) (E := E)) w) = w at hw
    rw [← hw,finiteOneChain_coefficient]
    rfl)

/-- The same actual quotient recursion for every set of retained row
variables. No interval closure of the retained sets is assumed. -/
theorem restrictedFirstPowerQuotientBetti_colon_sum {k : Type u} [Field k]
    (hE : finiteLatticeClosed n E) (hd : 0 < d)
    (A : ∀ r, Finset (Fin (n r))) (q p : ℕ) :
    ordinaryQuotientBettiNumber (k := k)
      (finiteRowFamily n (finiteRowRestriction E A)) (d+q) (p+1) =
      ∑ a : finiteRowRestriction E A, ordinaryQuotientBettiNumber (k := k)
        (finitePredecessorFamily n (finiteRowRestriction E A) a.val) q p :=
  firstPowerQuotientBetti_colon_sum (finiteRowRestriction_closed hE A) hd q p

/-- Positive homological entries below the generator degree vanish. This
supplies all omitted positive internal degrees of the polynomial identity. -/
theorem restrictedFirstPowerQuotientBetti_eq_zero_below {k : Type u} [Field k]
    (hE : finiteLatticeClosed n E) (A : ∀ r, Finset (Fin (n r)))
    (Q p : ℕ) (hQ : 0 < Q) (hbelow : Q < d) :
    ordinaryQuotientBettiNumber (k := k)
      (finiteRowFamily n (finiteRowRestriction E A)) Q (p+1) = 0 := by
  rw [ordinaryQuotientBettiNumber_succ_eq_ideal _ _ _ hQ]
  simpa only [one_mul, exponentPowerFamily_one] using
    ordinaryPowerBetti_eq_zero_below (k := k)
      (finiteRowRestriction_closed hE A) 1 (by omega) Q p (by simpa using hbelow)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.restrictedFirstPowerQuotientBetti_colon_sum

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.LinearVariableDegreeHomology -/
section

/-! # The exact graded exterior factor for disjoint linear variables

The factor is the actual signed exterior multiplication equivalence.
Its degree shift is the cardinality of the forced face in the chosen fine
degree. Both maps on cycles and both maps on boundaries are retained.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
lemma linearVariableQuotientFactor_degree (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (p : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B (α.filter (fun v => v ∉ L))))
    (hx : x ∈ totalFacePiece _ p) :
    linearVariableQuotientFactor L B hB α hsq x ∈
      totalFacePiece (quotientKoszulFaces (variableMonomialFamily L ∪ B) α)
        (p+(α.filter (fun v => v ∈ L)).support.card) := by
  have hA : ∀ v ∈ (α.filter (fun v => v ∈ L)).support, v ∈ L := by
    intro v hv
    have hn := Finsupp.mem_support_iff.mp hv
    by_contra hh
    simp [Finsupp.filter_apply, hh] at hn
  have hQ : ∀ F, quotientKoszulFaces B (α.filter (fun v => v ∉ L)) F →
      ∀ v ∈ F, v ∉ L := by
    intro F hF v hv hn
    have hh := hF.1 v
    simp [faceExponent_apply, Finsupp.filter_apply, hv, hn] at hh
  have h := fixedFaceFactorEquiv_mem_degree (k := k) (fun v => v ∈ L)
    (α.filter (fun v => v ∈ L)).support
    (quotientKoszulFaces B (α.filter (fun v => v ∉ L))) hA hQ p x hx
  change (fixedFaceFactorEquiv _ _ _ hA hQ x).val ∈ Simplicial.Chains _ _ at h
  rw [fixedFaceFactorEquiv_val] at h
  change (linearVariableQuotientFactor L B hB α hsq x).val ∈ Simplicial.Chains _ _
  rw [linearVariableQuotientFactor_val, linearVariableQuotient_faces_factor L B hB α hsq]
  exact h

lemma linearVariableQuotientFactor_symm_degree (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (p : ℕ)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces (variableMonomialFamily L ∪ B) α))
    (hx : x ∈ totalFacePiece _ (p+(α.filter (fun v => v ∈ L)).support.card)) :
    (linearVariableQuotientFactor L B hB α hsq).symm x ∈
      totalFacePiece (quotientKoszulFaces B (α.filter (fun v => v ∉ L))) p := by
  unfold linearVariableQuotientFactor
  rw [LinearEquiv.trans_symm,LinearEquiv.trans_apply,LinearEquiv.ofEq_symm]
  apply fixedFaceFactorEquiv_symm_mem_degree _ _ _ _ _ p
  change x.val ∈ Simplicial.Chains _ _
  rw [← linearVariableQuotient_faces_factor L B hB α hsq]
  exact hx

/-- The homogeneous cycle equivalence keeps the forced exterior degree. -/
def linearVariableDegreeCyclesEquiv (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (p : ℕ) :
    ClosedGraphDegreeCycles (k := k) B (α.filter (fun v => v ∉ L)) p ≃ₗ[k]
      ClosedGraphDegreeCycles (k := k) (variableMonomialFamily L ∪ B) α
        (p+(α.filter (fun v => v ∈ L)).support.card) where
  toFun z := ⟨linearVariableQuotientFactor L B hB α hsq z.val,by
    constructor
    · change quotientTotalDifferential (variableMonomialFamily L ∪ B) α
        (linearVariableQuotientFactor L B hB α hsq z.val) = 0
      rw [linearVariableQuotientFactor_differential,z.property.1,
        map_zero,smul_zero]
    · exact linearVariableQuotientFactor_degree L B hB α hsq p z.val z.property.2⟩
  invFun z := ⟨(linearVariableQuotientFactor L B hB α hsq).symm z.val,by
    constructor
    · exact linearVariableQuotientFactor_symm_cycle L B hB α hsq z.val z.property.1
    · exact linearVariableQuotientFactor_symm_degree L B hB α hsq p z.val z.property.2⟩
  left_inv z := Subtype.ext (LinearEquiv.symm_apply_apply _ z.val)
  right_inv z := Subtype.ext (LinearEquiv.apply_symm_apply _ z.val)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

private lemma linearVariableSign_square (L : Finset V) (α : Exponent V) :
    ((-1 : k)^(α.filter (fun v => v ∈ L)).support.card) *
      ((-1 : k)^(α.filter (fun v => v ∈ L)).support.card) = 1 := by
  rw [← pow_add,← two_mul,pow_mul]
  simp

lemma linearVariableDegreeCyclesEquiv_boundaries (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (p : ℕ) :
    (LinearMap.range (closedGraphDegreeBoundary (k := k) B
      (α.filter (fun v => v ∉ L)) p)).map
      (linearVariableDegreeCyclesEquiv L B hB α hsq p).toLinearMap =
        LinearMap.range (closedGraphDegreeBoundary (variableMonomialFamily L ∪ B) α
          (p+(α.filter (fun v => v ∈ L)).support.card)) := by
  let e := linearVariableQuotientFactor (k := k) L B hB α hsq
  let c : k := (-1 : k)^(α.filter (fun v => v ∈ L)).support.card
  have hcc : c*c=1 := linearVariableSign_square L α
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    have hy := linearVariableQuotientFactor_degree L B hB α hsq (p+1) y.val y.property
    have hy' : c • e y.val ∈ totalFacePiece
        (quotientKoszulFaces (variableMonomialFamily L ∪ B) α)
          (p+(α.filter (fun v => v ∈ L)).support.card+1) := by
      apply Submodule.smul_mem
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hy
    refine ⟨⟨c • e y.val,hy'⟩,?_⟩
    apply Subtype.ext
    change quotientTotalDifferential (variableMonomialFamily L ∪ B) α (c • e y.val) =
      e (quotientTotalDifferential B (α.filter (fun v => v ∉ L)) y.val)
    rw [map_smul]
    change c • quotientTotalDifferential (variableMonomialFamily L ∪ B) α
      (linearVariableQuotientFactor L B hB α hsq y.val) = _
    rw [linearVariableQuotientFactor_differential]
    change c • (c • e _) = e _
    rw [smul_smul,hcc,one_smul]
  · rintro ⟨y,rfl⟩
    have hy : y.val ∈ totalFacePiece
        (quotientKoszulFaces (variableMonomialFamily L ∪ B) α)
          ((p+1)+(α.filter (fun v => v ∈ L)).support.card) := by
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using y.property
    have hys := linearVariableQuotientFactor_symm_degree L B hB α hsq (p+1) y.val hy
    let w : totalFacePiece (k := k)
        (quotientKoszulFaces B (α.filter (fun v => v ∉ L))) (p+1) :=
      ⟨c • e.symm y.val,Submodule.smul_mem _ c hys⟩
    refine ⟨closedGraphDegreeBoundary B (α.filter (fun v => v ∉ L)) p w,
      ⟨w,rfl⟩,?_⟩
    apply Subtype.ext
    change e (quotientTotalDifferential B (α.filter (fun v => v ∉ L))
      (c • e.symm y.val)) = quotientTotalDifferential (variableMonomialFamily L ∪ B) α y.val
    rw [map_smul,map_smul]
    have hd := linearVariableQuotientFactor_differential L B hB α hsq (e.symm y.val)
    change quotientTotalDifferential (variableMonomialFamily L ∪ B) α (e (e.symm y.val)) =
      c • e (quotientTotalDifferential B (α.filter (fun v => v ∉ L)) (e.symm y.val)) at hd
    rw [e.apply_symm_apply] at hd
    exact hd.symm

/-- The actual homogeneous homology equivalence underlying the factor
`(1+s v)^|L|`; its fine shift is precisely the chosen subset of L. -/
def linearVariableDegreeHomologyEquiv (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (p : ℕ) :
    ClosedGraphDegreeHomology (k := k) B (α.filter (fun v => v ∉ L)) p ≃ₗ[k]
      ClosedGraphDegreeHomology (k := k) (variableMonomialFamily L ∪ B) α
        (p+(α.filter (fun v => v ∈ L)).support.card) :=
  Submodule.Quotient.equiv _ _ (linearVariableDegreeCyclesEquiv L B hB α hsq p)
    (linearVariableDegreeCyclesEquiv_boundaries L B hB α hsq p)

section Field
variable {K : Type u} [Field K]

/-- The exact numerical exterior factor, in each squarefree fine degree. -/
theorem linearVariable_quotientBetti_shift (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (p : ℕ) :
    quotientBettiNumber (k := K) (variableMonomialFamily L ∪ B) α
      (p+(α.filter (fun v => v ∈ L)).support.card) =
        quotientBettiNumber (k := K) B (α.filter (fun v => v ∉ L)) p := by
  simp only [quotientBettiNumber_eq_homology]
  rw [(quotientCategoricalDegreeHomologyEquiv (k := K) _ α _).finrank_eq,
    (quotientCategoricalDegreeHomologyEquiv (k := K) B _ p).finrank_eq]
  exact (linearVariableDegreeHomologyEquiv (k := K) L B hB α hsq p).finrank_eq.symm

/-- Degrees below the forced face vanish in the actual quotient Tor. -/
theorem linearVariable_quotientBetti_zero_below (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B, ∀ v, b v ≠ 0 → v ∉ L) (α : Exponent V)
    (hsq : ∀ v, α v ≤ 1) (p : ℕ)
    (hp : p < (α.filter (fun v => v ∈ L)).support.card) :
    quotientBettiNumber (k := K) (variableMonomialFamily L ∪ B) α p=0 := by
  have hz : ∀ x : ClosedGraphDegreeCycles (k := K) (variableMonomialFamily L ∪ B) α p,x=0 := by
    intro x
    apply Subtype.ext
    let y : TotalFaceModule (k := K)
        (splitFacePredicate (fun v => v ∈ L)
          (fun F => F=(α.filter (fun v => v ∈ L)).support)
          (quotientKoszulFaces B (α.filter (fun v => v ∉ L)))) :=
      ⟨x.val.val,by rw [← linearVariableQuotient_faces_factor L B hB α hsq];exact x.val.property⟩
    have hy : y ∈ totalFacePiece _ p := by
      change x.val.val ∈ Simplicial.Chains _ p
      rw [← linearVariableQuotient_faces_factor L B hB α hsq]
      exact x.property.2
    have hzero := fixedFacePiece_eq_zero_of_lt (k := K) (fun v => v ∈ L)
      (α.filter (fun v => v ∈ L)).support
      (quotientKoszulFaces B (α.filter (fun v => v ∉ L)))
      (by
        intro v hv
        have hn := Finsupp.mem_support_iff.mp hv
        by_contra hh
        simp [Finsupp.filter_apply,hh] at hn)
      (by
        intro F hF v hv hn
        have hh := hF.1 v
        simp [faceExponent_apply,Finsupp.filter_apply,hv,hn] at hh)
      p hp y hy
    have hval := congrArg Subtype.val hzero
    exact Subtype.ext hval
  letI : Subsingleton (ClosedGraphDegreeCycles (k := K) (variableMonomialFamily L ∪ B) α p) :=
    subsingleton_of_forall_eq 0 hz
  letI : Subsingleton (ClosedGraphDegreeHomology (k := K) (variableMonomialFamily L ∪ B) α p) := by
    unfold ClosedGraphDegreeHomology
    infer_instance
  letI : Subsingleton ((quotientHomogeneousComplex (k := K) (variableMonomialFamily L ∪ B) α).homology p) :=
    (quotientCategoricalDegreeHomologyEquiv _ α p).injective.subsingleton
  rw [quotientBettiNumber_eq_homology]
  exact Module.finrank_zero_of_subsingleton

end Field
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.linearVariableDegreeHomologyEquiv
#print axioms FourPapers.Sublattice.linearVariable_quotientBetti_shift

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientBettiSupport -/
section

/-! # Exact finite support of quotient Betti tables

These are statements about the actual fine derived Tor dimensions.
They justify finite Betti-polynomial sums and removal of unused variables;
no vanishing is built into the definition of a Betti number.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem quotientBetti_eq_zero_of_total_boundaries (B : Family V) (α : Exponent V) (p : ℕ)
    (h : ∀ x : TotalFaceModule (k := k) (quotientKoszulFaces B α),
      quotientTotalDifferential B α x=0 → ∃ y,quotientTotalDifferential B α y=x) :
    quotientBettiNumber (k := k) B α p=0 := by
  letI : Subsingleton (ClosedGraphFaceHomology (k := k) B α) :=
    closedGraphHomology_subsingleton_of_boundaries _ _ h
  letI : Subsingleton (ClosedGraphDegreeHomology (k := k) B α p) :=
    (closedGraphDegreeHomologyInclusion_injective B α p).subsingleton
  letI : Subsingleton ((quotientHomogeneousComplex (k := k) B α).homology p) :=
    (quotientCategoricalDegreeHomologyEquiv B α p).injective.subsingleton
  rw [quotientBettiNumber_eq_homology]
  exact Module.finrank_zero_of_subsingleton

theorem quotientBetti_eq_zero_of_unused (B : Family V) (α : Exponent V) (p : ℕ)
    (e : V) (hB : ∀ b ∈ B,b e=0) (he : 0<α e) :
    quotientBettiNumber (k := k) B α p=0 :=
  quotientBetti_eq_zero_of_total_boundaries B α p
    (quotient_cycle_boundary_free_variable hB he)

theorem quotientBetti_eq_zero_of_not_squarefree (B : Family V)
    (hB : ∀ b ∈ B,∀ v,b v≤1) (α : Exponent V) (p : ℕ)
    (hα : ¬∀ v,α v≤1) : quotientBettiNumber (k := k) B α p=0 := by
  obtain ⟨e,he⟩ := not_forall.mp hα
  exact quotientBetti_eq_zero_of_total_boundaries B α p
    (quotient_cycle_boundary_of_two_le (fun b hb => hB b hb e) (by omega))

/-- No exterior face in a fine strand has more vertices than its support. -/
theorem quotientPiece_eq_zero_of_support_lt (B : Family V) (α : Exponent V)
    (p : ℕ) (hp : α.support.card < p)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hx : x ∈ totalFacePiece (quotientKoszulFaces B α) p) : x=0 := by
  have hb : totalFacePiece (k := k) (quotientKoszulFaces B α) p ≤ ⊥ := by
    rw [totalFacePiece_eq_basis_span]
    apply Submodule.span_le.mpr
    rintro y ⟨F,hF,rfl⟩
    have hsub : F.val ⊆ α.support := by
      intro v hv
      apply Finsupp.mem_support_iff.mpr
      have hpos : 1≤α v := by
        simpa only [faceExponent_apply,hv,ite_true] using F.property.1 v
      exact Nat.ne_of_gt (Nat.succ_le_iff.mp hpos)
    have hc := Finset.card_le_card hsub
    change F.val.card=p at hF
    exact False.elim (by omega)
  exact hb hx

theorem quotientBetti_eq_zero_of_support_lt (B : Family V) (α : Exponent V)
    (p : ℕ) (hp : α.support.card < p) : quotientBettiNumber (k := k) B α p=0 := by
  letI : Subsingleton (ClosedGraphDegreeCycles (k := k) B α p) :=
    subsingleton_of_forall_eq 0 (fun x => Subtype.ext
      (quotientPiece_eq_zero_of_support_lt B α p hp x.val x.property.2))
  letI : Subsingleton (ClosedGraphDegreeHomology (k := k) B α p) := by
    unfold ClosedGraphDegreeHomology
    infer_instance
  letI : Subsingleton ((quotientHomogeneousComplex (k := k) B α).homology p) :=
    (quotientCategoricalDegreeHomologyEquiv B α p).injective.subsingleton
  rw [quotientBettiNumber_eq_homology]
  exact Module.finrank_zero_of_subsingleton

theorem quotientBetti_zero_homological_of_ne_zero (B : Family V) (α : Exponent V)
    (hα : α≠0) : quotientBettiNumber (k := k) B α 0=0 := by
  obtain ⟨e,he⟩ : ∃ e,0<α e := by
    by_contra! hn
    apply hα
    ext e
    exact Nat.eq_zero_of_le_zero (hn e)
  have hzero : ∀ x : ClosedGraphDegreeHomology (k := k) B α 0,x=0 := by
    intro x
    obtain ⟨z,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary B α 0)).mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨y,hy,hdy⟩ := quotientCycle_boundary_degree_zero B α e he z.val z.property.2
    exact ⟨⟨y,hy⟩,Subtype.ext hdy⟩
  letI : Subsingleton (ClosedGraphDegreeHomology (k := k) B α 0) :=
    subsingleton_of_forall_eq 0 hzero
  letI : Subsingleton ((quotientHomogeneousComplex (k := k) B α).homology 0) :=
    (quotientCategoricalDegreeHomologyEquiv B α 0).injective.subsingleton
  rw [quotientBettiNumber_eq_homology]
  exact Module.finrank_zero_of_subsingleton

section DegreeZero

attribute [local instance 2000] closedGraphDegreeHomologyAddCommGroup
  closedGraphDegreeHomologyModule closedGraphFaceHomologyAddCommGroup
  closedGraphFaceHomologyModule
attribute [local irreducible] ClosedGraphDegreeHomology ClosedGraphFaceHomology

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
private theorem submoduleHomologyMap_surjective_of_full_cycles
    {M : Type*} [AddCommGroup M] [Module k M]
    (T : Submodule k M) (D : T →ₗ[k] T) (hD : D.comp D = 0)
    (U C : Submodule k T) (b : U →ₗ[k] C) (hC : C ≤ LinearMap.ker D)
    (hb : ∀ u, (b u).val = D u.val)
    (hfull : ∀ z : LinearMap.ker D, z.val ∈ C) :
    Function.Surjective (FourPapers.FilteredHomology.submoduleHomologyMap
      T D hD U C b hC hb) := by
  intro x
  obtain ⟨z, hz⟩ := (LinearMap.range (FourPapers.FilteredHomology.boundaryMap D D hD)).mkQ_surjective x
  exact ⟨Submodule.Quotient.mk ⟨z.val, hfull z⟩, hz⟩

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
private theorem degreeHomologyInclusion_surjective_of_full_piece
    (B : Family V) (α : Exponent V) (p : ℕ)
    (hpiece : ∀ x : TotalFaceModule (k := k) (quotientKoszulFaces B α),
      x ∈ totalFacePiece (quotientKoszulFaces B α) p) :
    Function.Surjective (closedGraphDegreeHomologyInclusion (k := k) B α p) := by
  unfold closedGraphDegreeHomologyInclusion ClosedGraphDegreeHomology ClosedGraphFaceHomology
  exact submoduleHomologyMap_surjective_of_full_cycles
    (TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (quotientTotalDifferential (k := k) B α) (quotientTotalDifferential_comp B α)
    (totalFacePiece (k := k) (quotientKoszulFaces B α) (p+1))
    (ClosedGraphDegreeCycles (k := k) B α p) (closedGraphDegreeBoundary B α p)
    (show ClosedGraphDegreeCycles (k := k) B α p ≤
      LinearMap.ker (quotientTotalDifferential B α) from inf_le_left)
    (fun _ => rfl) (fun z => ⟨z.property, hpiece z.val⟩)

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- The exceptional quotient summand is exactly one copy of the field,
provided that the monomial ideal is proper. -/
theorem quotientBetti_zero_zero (B : Family V) (hB : ¬Contains B 0) :
    quotientBettiNumber (k := k) B 0 0=1 := by
  let Q := quotientKoszulFaces B (0 : Exponent V)
  have hface : ∀ F : {F // Q F}, F.val=∅ :=
    fun F => (quotientKoszulFaces_zero_iff B hB F.val).mp F.property
  have hdegree : ∀ x : TotalFaceModule (k := k) Q,x ∈ totalFacePiece Q 0 := by
    intro x
    rw [totalFacePiece_eq_basis_span]
    have hspan : Submodule.span k ((totalFaceBasis (k := k) Q) '' {F | F.val.card=0})=⊤ := by
      have hset : {F : {F // Q F} | F.val.card=0}=Set.univ := by
        ext F
        simp [hface F]
      rw [hset,Set.image_univ]
      exact (totalFaceBasis (k := k) Q).span_eq
    rw [hspan]
    trivial
  have hsurj : Function.Surjective (closedGraphDegreeHomologyInclusion (k := k) B 0 0) :=
    degreeHomologyInclusion_surjective_of_full_piece B 0 0 hdegree
  let e := LinearEquiv.ofBijective (closedGraphDegreeHomologyInclusion (k := k) B 0 0)
    ⟨closedGraphDegreeHomologyInclusion_injective B 0 0,hsurj⟩
  rw [quotientBettiNumber_eq_homology,
    (quotientCategoricalDegreeHomologyEquiv (k := k) B 0 0).finrank_eq,e.finrank_eq,
    (closedGraphZeroStrandHomologyEquiv (k := k) B hB).finrank_eq]
  exact Module.finrank_self k

end DegreeZero

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientBetti_zero_zero

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientFaceBettiPolynomial -/
section

/-! # The actual quotient Betti polynomial in one squarefree fine degree

The coefficient theorem holds in every homological degree. Thus the finite
polynomial contains the complete strand, and the exterior-factor identity
has no implicit degree truncation or omitted low-degree case.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

@[simp] lemma faceExponent_support_eq (F : Finset V) : (faceExponent F).support=F := by
  ext v
  simp [Finsupp.mem_support_iff,faceExponent_apply]

lemma faceExponent_squarefree (F : Finset V) : ∀ v,(faceExponent F) v≤1 := by
  intro v
  simp only [faceExponent_apply]
  split_ifs <;> omega

@[simp] lemma faceExponent_filter_inter (F L : Finset V) :
    (faceExponent F).filter (fun v => v ∈ L)=faceExponent (F∩L) := by
  ext v
  by_cases hF : v ∈ F <;> by_cases hL : v ∈ L <;>
    simp [Finsupp.filter_apply,faceExponent_apply,hF,hL]

@[simp] lemma faceExponent_filter_sdiff (F L : Finset V) :
    (faceExponent F).filter (fun v => v ∉ L)=faceExponent (F\L) := by
  ext v
  by_cases hF : v ∈ F <;> by_cases hL : v ∈ L <;>
    simp [Finsupp.filter_apply,faceExponent_apply,hF,hL]

/-- All actual homological Betti numbers in one squarefree fine strand. -/
def quotientFaceBettiPolynomial (B : Family V) (F : Finset V) : Polynomial ℕ :=
  ∑ p ∈ Finset.range (F.card+1),
    Polynomial.monomial p (quotientBettiNumber (k := k) B (faceExponent F) p)

@[simp] theorem quotientFaceBettiPolynomial_coeff (B : Family V) (F : Finset V) (p : ℕ) :
    (quotientFaceBettiPolynomial (k := k) B F).coeff p =
      quotientBettiNumber (k := k) B (faceExponent F) p := by
  simp only [quotientFaceBettiPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,
    Finset.sum_ite_eq',Finset.mem_range]
  by_cases hp : p<F.card+1
  · rw [if_pos hp]
  · rw [if_neg hp]
    exact (quotientBetti_eq_zero_of_support_lt B (faceExponent F) p
      (by rw [faceExponent_support_eq];omega)).symm

/-- The complete exact exterior factor in a fixed fine strand. -/
theorem quotientFaceBettiPolynomial_linear_factor (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B,∀ v,b v ≠ 0 → v ∉ L) (F : Finset V) :
    quotientFaceBettiPolynomial (k := k) (variableMonomialFamily L ∪ B) F =
      Polynomial.X^(F∩L).card * quotientFaceBettiPolynomial (k := k) B (F\L) := by
  apply Polynomial.ext
  intro p
  rw [quotientFaceBettiPolynomial_coeff,Polynomial.coeff_X_pow_mul']
  by_cases hp : (F∩L).card≤p
  · rw [if_pos hp,quotientFaceBettiPolynomial_coeff]
    have h := linearVariable_quotientBetti_shift (K := k) L B hB (faceExponent F)
      (faceExponent_squarefree F) (p-(F∩L).card)
    simpa only [faceExponent_filter_inter,faceExponent_filter_sdiff,
      faceExponent_support_eq,Nat.sub_add_cancel hp] using h
  · rw [if_neg hp]
    apply linearVariable_quotientBetti_zero_below L B hB (faceExponent F)
      (faceExponent_squarefree F) p
    simpa only [faceExponent_filter_inter,faceExponent_support_eq] using Nat.lt_of_not_ge hp

lemma quotientFaceBettiPolynomial_eq_zero_of_unused (B : Family V) (F : Finset V)
    (v : V) (hv : v ∈ F) (hB : ∀ b ∈ B,b v=0) :
    quotientFaceBettiPolynomial (k := k) B F=0 := by
  apply Polynomial.ext
  intro p
  rw [quotientFaceBettiPolynomial_coeff,Polynomial.coeff_zero]
  exact quotientBetti_eq_zero_of_unused B (faceExponent F) p v hB
    (by simp [faceExponent_apply,hv])

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientFaceBettiPolynomial_coeff
#print axioms FourPapers.Sublattice.quotientFaceBettiPolynomial_linear_factor

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientBettiPolynomial -/
section

/-! # The genuine finite quotient Betti polynomial and its exterior factor

The inner polynomial variable is homological degree and the outer variable
is ordinary degree. For squarefree generators the coefficient theorem
identifies every coefficient with actual ordinary Tor; vanishing outside
the finite sum is proved from the strand contractions.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

private theorem sum_subtype_ite {I R : Type*} [Fintype I] [AddCommMonoid R]
    (P : I → Prop) [DecidablePred P] (f : I → R) :
    (∑ x : {x // P x},f x.val)=∑ x,if P x then f x else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) f).symm

private theorem sum_subtype_of_zero {I R : Type*} [Fintype I] [AddCommMonoid R]
    (P : I → Prop) [DecidablePred P] (f : I → R) (hz : ∀ x,¬P x → f x=0) :
    (∑ x : {x // P x},f x.val)=∑ x,f x := by
  rw [sum_subtype_ite]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x
  · rw [if_pos hx]
  · rw [if_neg hx,hz x hx]

/-- Squarefree exponent vectors of ordinary degree q are precisely the
q-element subsets of the literal variable set. -/
def squarefreeOrdinaryFaceEquiv (q : ℕ) :
    {α : OrdinaryFineIndex V q // ∀ v,α.val v≤1} ≃ {F : Finset V // F.card=q} where
  toFun α := ⟨α.val.val.support,by
    have h := congrArg Finsupp.degree
      (squarefreeExponent_eq_faceExponent_support α.val.val α.property)
    rw [degree_faceExponent,α.val.property] at h
    exact h⟩
  invFun F := ⟨⟨faceExponent F.val,by rw [degree_faceExponent,F.property]⟩,
    faceExponent_squarefree F.val⟩
  left_inv α := by
    apply Subtype.ext
    apply Subtype.ext
    exact squarefreeExponent_eq_faceExponent_support α.val.val α.property
  right_inv F := Subtype.ext (faceExponent_support_eq F.val)

lemma ordinaryQuotientBetti_eq_squarefreeFaces (B : Family V)
    (hB : ∀ b ∈ B,∀ v,b v≤1) (q p : ℕ) :
    ordinaryQuotientBettiNumber (k := k) B q p =
      ∑ F : {F : Finset V // F.card=q},quotientBettiNumber (k := k) B (faceExponent F.val) p := by
  rw [ordinaryQuotientBettiNumber_eq_sum,
    ← sum_subtype_of_zero (fun α : OrdinaryFineIndex V q => ∀ v,α.val v≤1)
      (fun α => quotientBettiNumber (k := k) B α.val p)
      (fun α hα => quotientBetti_eq_zero_of_not_squarefree B hB α.val p hα)]
  apply Fintype.sum_equiv (squarefreeOrdinaryFaceEquiv (V := V) q)
  intro α
  rw [show (faceExponent (squarefreeOrdinaryFaceEquiv (V := V) q α).val)=α.val.val from
    squarefreeExponent_eq_faceExponent_support α.val.val α.property]

/-- The outer variable is internal degree; its coefficients are polynomials
in homological degree. -/
def quotientBettiPolynomial (B : Family V) : Polynomial (Polynomial ℕ) :=
  ∑ F : Finset V,Polynomial.monomial F.card (quotientFaceBettiPolynomial (k := k) B F)

/-- Every coefficient, in all ordinary and homological degrees, is the
actual Betti number of the quotient. -/
theorem quotientBettiPolynomial_coeff (B : Family V)
    (hB : ∀ b ∈ B,∀ v,b v≤1) (q p : ℕ) :
    ((quotientBettiPolynomial (k := k) B).coeff q).coeff p=
      ordinaryQuotientBettiNumber (k := k) B q p := by
  rw [ordinaryQuotientBetti_eq_squarefreeFaces B hB q p,
    sum_subtype_ite (fun F : Finset V => F.card=q)
      (fun F => quotientBettiNumber (k := k) B (faceExponent F) p)]
  simp only [quotientBettiPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro F _
  by_cases hF : F.card=q
  · rw [if_pos hF,if_pos hF,quotientFaceBettiPolynomial_coeff]
  · rw [if_neg hF,if_neg hF,Polynomial.coeff_zero]

/-- Splitting a face into its killed and retained vertices is a genuine
bijection, with no multiplicities lost. -/
def splitVariableFaceEquiv (L : Finset V) :
    Finset V ≃ ({A : Finset V // A⊆L} × {G : Finset V // Disjoint G L}) where
  toFun F := (⟨F∩L,Finset.inter_subset_right⟩,⟨F\L,Finset.sdiff_disjoint⟩)
  invFun x := x.1.val∪x.2.val
  left_inv F := by
    ext v
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      ext v
      have hA : v∈x.1.val → v∈L := fun h => x.1.property h
      have hG : v∈x.2.val → v∉L := fun h => Finset.disjoint_left.mp x.2.property h
      simp only [Finset.mem_inter,Finset.mem_union]
      tauto
    · apply Subtype.ext
      ext v
      have hA : v∈x.1.val → v∈L := fun h => x.1.property h
      have hG : v∈x.2.val → v∉L := fun h => Finset.disjoint_left.mp x.2.property h
      simp only [Finset.mem_sdiff,Finset.mem_union]
      tauto

lemma quotientBettiPolynomial_unused_sum (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B,∀ v,b v≠0 → v∉L) :
    quotientBettiPolynomial (k := k) B =
      ∑ G : {G : Finset V // Disjoint G L},
        Polynomial.monomial G.val.card (quotientFaceBettiPolynomial (k := k) B G.val) := by
  unfold quotientBettiPolynomial
  symm
  apply sum_subtype_of_zero (fun F : Finset V => Disjoint F L)
    (fun F => Polynomial.monomial F.card (quotientFaceBettiPolynomial (k := k) B F))
  intro F hF
  obtain ⟨v,hvF,hvL⟩ := Finset.not_disjoint_iff.mp hF
  rw [quotientFaceBettiPolynomial_eq_zero_of_unused B F v hvF (by
    intro b hb
    by_contra hn
    exact hB b hb v hn hvL),map_zero]

private lemma exteriorFactor_sum (L : Finset V) :
    (∑ A : {A : Finset V // A⊆L},
      Polynomial.monomial A.val.card (Polynomial.X^A.val.card : Polynomial ℕ)) =
        (1+Polynomial.monomial 1 (Polynomial.X : Polynomial ℕ))^L.card := by
  rw [← Finset.sum_subtype (p := fun A : Finset V => A ⊆ L) L.powerset
    (by intro A; exact Finset.mem_powerset)
    (fun A => Polynomial.monomial A.card (Polynomial.X^A.card : Polynomial ℕ))]
  have h := Finset.prod_add_one (f := fun _ : V =>
    (Polynomial.monomial 1 (Polynomial.X : Polynomial ℕ) : Polynomial (Polynomial ℕ))) L
  simpa only [Finset.prod_const,Polynomial.monomial_pow,one_mul,add_comm] using h.symm

/-- The complete ordinary exterior factor in Lemma 6.1 and equation (6.1).
For squarefree B the coefficient theorem above identifies the two sides
with the full ordinary Betti polynomials of the indicated quotients. -/
theorem quotientBettiPolynomial_linear_factor (L : Finset V) (B : Family V)
    (hB : ∀ b ∈ B,∀ v,b v≠0 → v∉L) :
    quotientBettiPolynomial (k := k) (variableMonomialFamily L∪B) =
      (1+Polynomial.monomial 1 (Polynomial.X : Polynomial ℕ))^L.card *
        quotientBettiPolynomial (k := k) B := by
  rw [quotientBettiPolynomial,quotientBettiPolynomial_unused_sum L B hB,
    ← exteriorFactor_sum L,Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (splitVariableFaceEquiv (V := V) L)
  intro F
  have hcard : F.card=(F∩L).card+(F\L).card := by
    have h := Finset.card_union_of_disjoint (s := F∩L) (t := F\L)
      (Finset.disjoint_left.mpr (by intro v hv hv';exact (Finset.mem_sdiff.mp hv').2 (Finset.mem_inter.mp hv).2))
    have hset : (F∩L)∪(F\L)=F := (splitVariableFaceEquiv (V := V) L).left_inv F
    rw [hset] at h
    exact h
  change Polynomial.monomial F.card
      (quotientFaceBettiPolynomial (k := k) (variableMonomialFamily L∪B) F) =
    Polynomial.monomial (F∩L).card (Polynomial.X^(F∩L).card : Polynomial ℕ) *
      Polynomial.monomial (F\L).card (quotientFaceBettiPolynomial (k := k) B (F\L))
  rw [Polynomial.monomial_mul_monomial,quotientFaceBettiPolynomial_linear_factor L B hB,hcard]

/-- Changing a generating family without changing its literal monomial
ideal leaves the whole polynomial unchanged. -/
theorem quotientBettiPolynomial_eq_of_contains {B C : Family V}
    (h : ∀ α,Contains B α ↔ Contains C α) :
    quotientBettiPolynomial (k := k) B=quotientBettiPolynomial (k := k) C := by
  unfold quotientBettiPolynomial
  apply Finset.sum_congr rfl
  intro F _
  congr 1
  apply Polynomial.ext
  intro p
  rw [quotientFaceBettiPolynomial_coeff,quotientFaceBettiPolynomial_coeff,
    quotientBettiNumber_eq_homology,quotientBettiNumber_eq_homology]
  exact ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) p).mapIso
    (quotientHomogeneousIsoOfContains h (faceExponent F))).toLinearEquiv.finrank_eq

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.quotientBettiPolynomial_coeff
#print axioms FourPapers.Sublattice.quotientBettiPolynomial_linear_factor

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FirstPowerQuotientPolynomial -/
section

/-! # The full first-power quotient Betti polynomial identity

This statement includes the quotient's free summand in bidegree (0,0).
All other low-degree and negative-shift cases are proved to vanish before
the finite polynomial identity is assembled.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma ordinaryQuotientBetti_zero_internal_succ (B : Family V) (p : ℕ) :
    ordinaryQuotientBettiNumber (k := k) B 0 (p+1)=0 := by
  rw [ordinaryQuotientBettiNumber_eq_sum]
  apply Finset.sum_eq_zero
  intro α _
  have hα : α.val=0 := (Finsupp.degree_eq_zero_iff _).mp α.property
  rw [hα]
  apply quotientBetti_eq_zero_of_support_lt
  simp

lemma ordinaryQuotientBetti_zero_homological_of_pos (B : Family V) (q : ℕ) (hq : 0<q) :
    ordinaryQuotientBettiNumber (k := k) B q 0=0 := by
  rw [ordinaryQuotientBettiNumber_eq_sum]
  apply Finset.sum_eq_zero
  intro α _
  apply quotientBetti_zero_homological_of_ne_zero
  intro hα
  have hd := α.property
  rw [hα,map_zero] at hd
  omega

lemma ordinaryQuotientBetti_zero_zero (B : Family V) (hB : ¬Contains B 0) :
    ordinaryQuotientBettiNumber (k := k) B 0 0=1 := by
  letI : Unique (OrdinaryFineIndex V 0) :=
    { default := ⟨0,map_zero _⟩
      uniq := fun α => Subtype.ext ((Finsupp.degree_eq_zero_iff _).mp α.property) }
  rw [ordinaryQuotientBettiNumber_eq_sum,Fintype.sum_unique]
  exact quotientBetti_zero_zero B hB

lemma ordinaryQuotientBetti_empty_pos_internal (q p : ℕ) (hq : 0<q) :
    ordinaryQuotientBettiNumber (k := k) (∅ : Family V) q p=0 := by
  rw [ordinaryQuotientBettiNumber_eq_sum]
  apply Finset.sum_eq_zero
  intro α _
  obtain ⟨v,hv⟩ : ∃ v,0<α.val v := by
    by_contra! hn
    have hz : α.val=0 := Finsupp.ext (fun v => Nat.eq_zero_of_le_zero (hn v))
    have hd := α.property
    rw [hz,map_zero] at hd
    omega
  exact quotientBetti_eq_zero_of_unused ∅ α.val p v (by simp) hv

/-- The initial value Q₀=1 in Lemma 6.1. -/
theorem quotientBettiPolynomial_empty :
    quotientBettiPolynomial (k := k) (∅ : Family V)=1 := by
  apply Polynomial.ext
  intro q
  apply Polynomial.ext
  intro p
  rw [quotientBettiPolynomial_coeff _ (by simp)]
  cases q with
  | zero =>
      rw [Polynomial.coeff_one_zero]
      cases p with
      | zero =>
          rw [Polynomial.coeff_one_zero]
          exact ordinaryQuotientBetti_zero_zero ∅ (by simp [Contains])
      | succ p =>
          rw [Polynomial.coeff_one,if_neg (Nat.succ_ne_zero _)]
          exact ordinaryQuotientBetti_zero_internal_succ ∅ p
  | succ q =>
      rw [Polynomial.coeff_one,if_neg (Nat.succ_ne_zero _),Polynomial.coeff_zero]
      exact ordinaryQuotientBetti_empty_pos_internal _ _ (by omega)

section Rows
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

lemma finiteRowFamily_squarefree : ∀ b ∈ finiteRowFamily n E,∀ v,b v≤1 := by
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  rintro ⟨r,⟨j⟩⟩
  simp only [finiteRowExponent_apply]
  split_ifs <;> omega

lemma finitePredecessorFamily_squarefree (a : FiniteTuple n) :
    ∀ b ∈ finitePredecessorFamily n E a,∀ v,b v≤1 := by
  intro b hb
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
  intro v
  exact (tsub_le_self : finiteRowExponent n c-finiteRowExponent n a≤finiteRowExponent n c) v |>.trans
    (finiteRowFamily_squarefree (n := n) (E := E) _
      (Finset.mem_image.mpr ⟨c,(Finset.mem_filter.mp hc).1,rfl⟩) v)

lemma finiteRowFamily_not_contains_zero (hd : 0<d) : ¬Contains (finiteRowFamily n E) 0 := by
  rintro ⟨b,hb,hb0⟩
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  let r : Fin d := ⟨0,hd⟩
  have h := hb0 ⟨r,ULift.up (a r)⟩
  simp [finiteRowExponent_apply] at h

private lemma monomial_mul_coeff_of_lt {R : Type*} [Semiring R]
    (a : R) (P : Polynomial R) (d q : ℕ) (hq : q<d) :
    (Polynomial.monomial d a * P).coeff q=0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial,mul_assoc,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul',if_neg (Nat.not_le.mpr hq),mul_zero]

/-- The minimal generator-filtration identity as a literal finite polynomial,
including its constant term. The outer variable records internal degree and
the inner variable records homological degree. -/
theorem firstPowerQuotientBettiPolynomial_colon_recursion
    (hE : finiteLatticeClosed n E) (hd : 0<d) :
    quotientBettiPolynomial (k := k) (finiteRowFamily n E) =
      1+Polynomial.monomial d (Polynomial.X : Polynomial ℕ) *
        ∑ a : E,quotientBettiPolynomial (k := k) (finitePredecessorFamily n E a.val) := by
  apply Polynomial.ext
  intro q
  apply Polynomial.ext
  intro p
  rw [quotientBettiPolynomial_coeff _ finiteRowFamily_squarefree,
    Polynomial.coeff_add,Polynomial.coeff_add]
  by_cases hqd : d≤q
  · obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le hqd
    have hqt : q=t+d := by omega
    rw [hqt,Polynomial.coeff_monomial_mul]
    have hq0 : t+d≠0 := by omega
    rw [Polynomial.coeff_one,if_neg hq0,Polynomial.coeff_zero,zero_add]
    cases p with
    | zero =>
        rw [Polynomial.coeff_X_mul_zero]
        exact ordinaryQuotientBetti_zero_homological_of_pos _ _ (by omega)
    | succ p =>
        rw [Polynomial.coeff_X_mul,Polynomial.finsetSum_coeff,Polynomial.finsetSum_coeff]
        simp_rw [quotientBettiPolynomial_coeff _ (finitePredecessorFamily_squarefree _)]
        simpa only [Nat.add_comm] using firstPowerQuotientBetti_colon_sum (k := k) hE hd t p
  · have hqd' : q<d := Nat.lt_of_not_ge hqd
    rw [monomial_mul_coeff_of_lt _ _ d q hqd',Polynomial.coeff_zero,add_zero]
    cases q with
    | zero =>
        rw [Polynomial.coeff_one_zero]
        cases p with
        | zero =>
            rw [Polynomial.coeff_one_zero]
            exact ordinaryQuotientBetti_zero_zero _ (finiteRowFamily_not_contains_zero hd)
        | succ p =>
            rw [Polynomial.coeff_one,if_neg (Nat.succ_ne_zero _)]
            exact ordinaryQuotientBetti_zero_internal_succ _ p
    | succ q =>
        rw [Polynomial.coeff_one,if_neg (Nat.succ_ne_zero _),Polynomial.coeff_zero]
        cases p with
        | zero => exact ordinaryQuotientBetti_zero_homological_of_pos _ _ (by omega)
        | succ p =>
            rw [ordinaryQuotientBettiNumber_succ_eq_ideal _ _ _ (by omega)]
            simpa only [one_mul,exponentPowerFamily_one] using
              ordinaryPowerBetti_eq_zero_below (k := k) hE 1 (by omega) (q+1) p
                (by simpa using hqd')

end Rows
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.firstPowerQuotientBettiPolynomial_colon_recursion

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalRetainedColons -/
section

/-! # Literal predecessor colons after arbitrary variable restriction

A retained generator cannot cancel a variable outside the retained set.
The proof first establishes this for the exact divisibility predicates,
then identifies the actual polynomial ideals. The residual remains a
literal restriction of the original facet family.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

def restrictMonomialFamily {V : Type u} (U : Finset V) (B : Family V) : Family V := by
  classical
  exact B.filter (fun b => ∀ v, b v ≠ 0 → v ∈ U)

@[simp] theorem mem_restrictMonomialFamily {V : Type u} {U : Finset V}
    {B : Family V} {b : Exponent V} :
    b ∈ restrictMonomialFamily U B ↔ b ∈ B ∧ ∀ v, b v ≠ 0 → v ∈ U := by
  classical
  simp only [restrictMonomialFamily, Finset.mem_filter]

section General
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma contains_restrictMonomialFamily (U : Finset V) (B : Family V) (α : Exponent V) :
    Contains (restrictMonomialFamily U B) α ↔ Contains B (α.filter (fun v => v ∈ U)) := by
  constructor
  · rintro ⟨b,hb,hbα⟩
    obtain ⟨hb,hbU⟩ := mem_restrictMonomialFamily.mp hb
    refine ⟨b,hb,?_⟩
    intro v
    by_cases hv : v ∈ U
    · simpa [Finsupp.filter_apply,hv] using hbα v
    · have hz : b v=0 := by
        by_contra hh
        exact hv (hbU v hh)
      simp [hz]
  · rintro ⟨b,hb,hbα⟩
    refine ⟨b,mem_restrictMonomialFamily.mpr ⟨hb,?_⟩,?_⟩
    · intro v hv
      by_contra hn
      have h := hbα v
      simp [Finsupp.filter_apply,hn] at h
      exact hv h
    · intro v
      exact (hbα v).trans (by by_cases hv : v ∈ U <;> simp [Finsupp.filter_apply,hv])

lemma restrictMonomialFamily_union (U : Finset V) (B C : Family V) :
    restrictMonomialFamily U (B∪C) =
      restrictMonomialFamily U B ∪ restrictMonomialFamily U C := by
  simp only [restrictMonomialFamily,Finset.filter_union]

end General

section GeneralOrdered
variable {V : Type u} [Fintype V] [LinearOrder V]

lemma restrictMonomialFamily_variables (U L : Finset V) :
    restrictMonomialFamily U (variableMonomialFamily L) = variableMonomialFamily (L∩U) := by
  ext b
  constructor
  · intro hb
    obtain ⟨hb,hU⟩ := mem_restrictMonomialFamily.mp hb
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_image.mpr
    refine ⟨v,Finset.mem_inter.mpr ⟨hv,?_⟩,rfl⟩
    exact hU v (by simp)
  · intro hb
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hvL,hvU⟩ := Finset.mem_inter.mp hv
    apply mem_restrictMonomialFamily.mpr
    refine ⟨Finset.mem_image.mpr ⟨v,hvL,rfl⟩,?_⟩
    intro w hw
    by_cases hvw : v=w
    · simpa only [← hvw] using hvU
    · simp [Finsupp.single_apply,hvw] at hw

end GeneralOrdered

section Rows
variable {d : ℕ} {n : Fin d → ℕ}

def retainedRowVariables (A : ∀ r,Finset (Fin (n r))) : Finset (FiniteVariable.{u} n) :=
  Finset.univ.filter (fun v => v.2.down ∈ A v.1)

@[simp] lemma mem_retainedRowVariables (A : ∀ r,Finset (Fin (n r)))
    (r : Fin d) (j : Fin (n r)) :
    (⟨r,ULift.up j⟩ : FiniteVariable.{u} n) ∈ retainedRowVariables A ↔ j ∈ A r := by
  simp [retainedRowVariables]

lemma filter_supportedRows (A : ∀ r,Finset (Fin (n r))) (α : Exponent (FiniteVariable.{u} n)) :
    SupportedRows A (α.filter (fun v => v ∈ retainedRowVariables A)) := by
  intro r j hj
  by_contra hh
  simp [Finsupp.filter_apply,hh] at hj

lemma restrictMonomialFamily_rows (A : ∀ r,Finset (Fin (n r)))
    (E : Finset (FiniteTuple n)) :
    restrictMonomialFamily (retainedRowVariables A) (finiteRowFamily n E) =
      finiteRowFamily n (finiteRowRestriction E A) := by
  ext b
  constructor
  · intro hb
    obtain ⟨hb,hU⟩ := mem_restrictMonomialFamily.mp hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_image.mpr
    refine ⟨a,(mem_finiteRowRestriction E A a).mpr ⟨ha,?_⟩,rfl⟩
    intro r
    exact (mem_retainedRowVariables A r (a r)).mp
      (hU ⟨r,ULift.up (a r)⟩ (by simp [finiteRowExponent_apply]))
  · intro hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨haE,haA⟩ := (mem_finiteRowRestriction E A a).mp ha
    apply mem_restrictMonomialFamily.mpr
    refine ⟨Finset.mem_image.mpr ⟨a,haE,rfl⟩,?_⟩
    rintro ⟨r,⟨j⟩⟩ hj
    have he : a r=j := by
      by_contra hn
      simp [finiteRowExponent_apply,hn] at hj
    subst j
    exact (mem_retainedRowVariables A r (a r)).mpr (haA r)

lemma restrictedCoordinatePredecessor_supported
    (E : Finset (FiniteTuple n)) (A : ∀ r,Finset (Fin (n r))) (a : FiniteTuple n) :
    ∀ b ∈ finiteCoordinatePredecessorFamily (finiteRowRestriction E A) a,
      ∀ v,b v ≠ 0 → v ∈ retainedRowVariables A := by
  intro b hb
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
  have hcA := ((mem_finiteRowRestriction E A c).mp (Finset.mem_filter.mp hc).1).2
  rintro ⟨r,⟨j⟩⟩ hj
  have he : c r=j := by
    by_contra hn
    simp [Finsupp.tsub_apply,finiteRowExponent_apply,hn] at hj
  subst j
  exact (mem_retainedRowVariables A r (c r)).mpr (hcA r)

/-- Commuting a predecessor colon with restriction, for all exponent vectors,
without a support hypothesis on the test monomial. -/
theorem restrictedPredecessor_contains_filtered (E : Finset (FiniteTuple n))
    (hE : finiteLatticeClosed n E) (A : ∀ r,Finset (Fin (n r)))
    {a : FiniteTuple n} (ha : a ∈ finiteRowRestriction E A)
    (α : Exponent (FiniteVariable.{u} n)) :
    Contains (finitePredecessorFamily n (finiteRowRestriction E A) a) α ↔
      Contains (finitePredecessorFamily n E a)
        (α.filter (fun v => v ∈ retainedRowVariables A)) := by
  rw [← finiteCoordinatePredecessor_contains_iff (finiteRowRestriction_closed hE A) ha,
    ← contains_filter_iff_of_supported _ (fun v => v ∈ retainedRowVariables A)
      (restrictedCoordinatePredecessor_supported E A a) α,
    restrictedCoordinatePredecessor_contains_iff E A ha _ (filter_supportedRows A α),
    finiteCoordinatePredecessor_contains_iff hE ((mem_finiteRowRestriction E A a).mp ha).1]

end Rows

section UnitInterval
variable {d N : ℕ} {E : Finset ((Fin (d+1) → Fin N))}

def retainedFacetLinearVariables (A : ∀ r : Fin (d+1),Finset (Fin N))
    (a : (Fin (d+1) → Fin N)) : Finset (FiniteVariable.{u} (UnitIntervalRows d N)) :=
  facetLinearVariables E a ∩ retainedRowVariables A

def retainedFacetResidualFamily (A : ∀ r : Fin (d+1),Finset (Fin N))
    (a : (Fin (d+1) → Fin N)) : Family (FiniteVariable.{u} (UnitIntervalRows d N)) :=
  finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction (facetResidualFacets E a) A)

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- The exact retained colon is the sum of the retained linear variables
and the retained residual. This is the restriction clause of Lemma 6.1. -/
theorem unitIntervalRetainedPredecessor_contains_iff (hE : UnitIntervalFacetFamily E)
    (A : ∀ r : Fin (d+1),Finset (Fin N)) {a : (Fin (d+1) → Fin N)}
    (ha : a ∈ finiteRowRestriction E A) (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    Contains (finitePredecessorFamily (UnitIntervalRows d N) (finiteRowRestriction E A) a) α ↔
      Contains (variableMonomialFamily (retainedFacetLinearVariables (E := E) A a) ∪
        retainedFacetResidualFamily (E := E) A a) α := by
  rw [restrictedPredecessor_contains_filtered E hE.latticeClosed A ha α,
    unitIntervalPredecessor_contains_iff hE ((mem_finiteRowRestriction E A a).mp ha).1,
    ← contains_restrictMonomialFamily]
  have hcolon : facetColonFamily E a =
      variableMonomialFamily (facetLinearVariables E a) ∪
        finiteRowFamily (UnitIntervalRows d N) (facetResidualFacets E a) := by
    ext b
    simp only [facetColonFamily, variableMonomialFamily, Finset.mem_union, Finset.mem_image]
  rw [hcolon, restrictMonomialFamily_union,
    restrictMonomialFamily_variables (retainedRowVariables A) (facetLinearVariables E a),
    restrictMonomialFamily_rows (n := UnitIntervalRows d N) A (facetResidualFacets E a)]
  apply Iff.of_eq
  apply congrArg (fun B : Family (FiniteVariable.{u} (UnitIntervalRows d N)) => Contains B α)
  ext b
  simp only [retainedFacetLinearVariables, retainedFacetResidualFamily,
    variableMonomialFamily, Finset.mem_union, Finset.mem_image, Finset.mem_inter]

/-- Equality of the actual polynomial ideals, not just their generator data. -/
theorem unitIntervalRetainedPredecessorColon_eq {k : Type*} [CommSemiring k]
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d+1),Finset (Fin N))
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ finiteRowRestriction E A) :
    finitePredecessorColon (UnitIntervalRows d N) (k := k) (finiteRowRestriction E A) a =
      monomialIdeal k (variableMonomialFamily (retainedFacetLinearVariables (E := E) A a) ∪
        retainedFacetResidualFamily (E := E) A a) := by
  rw [finitePredecessorColon_eq]
  ext f
  simp_rw [mem_monomialIdeal_iff,unitIntervalRetainedPredecessor_contains_iff hE A ha]

lemma retainedFacetResidualFamily_disjoint (hE : UnitIntervalFacetFamily E)
    (A : ∀ r : Fin (d+1),Finset (Fin N)) (a : (Fin (d+1) → Fin N)) :
    ∀ b ∈ retainedFacetResidualFamily (E := E) A a,
      ∀ v,b v ≠ 0 → v ∉ retainedFacetLinearVariables (E := E) A a := by
  intro b hb v hv hL
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
  apply facetResidualFamily_disjoint hE a _
    (Finset.mem_image.mpr ⟨c,((mem_finiteRowRestriction _ A c).mp hc).1,rfl⟩) v hv
  exact (Finset.mem_inter.mp hL).1

/-- The residual after restriction is literally a further restriction of E. -/
theorem retainedFacetResidualFamily_eq_restriction
    (A : ∀ r : Fin (d+1),Finset (Fin N)) (a : (Fin (d+1) → Fin N)) :
    retainedFacetResidualFamily (E := E) A a =
      finiteRowFamily (UnitIntervalRows d N)
        (finiteRowRestriction E (fun r => A r ∩ facetResidualRows E a r)) := by
  apply congrArg (finiteRowFamily (UnitIntervalRows d N))
  ext b
  simp only [mem_finiteRowRestriction,facetResidualFacets_restriction,Finset.mem_inter]
  constructor
  · rintro ⟨⟨hb, hR⟩, hA⟩
    exact ⟨hb, fun r => ⟨hA r, hR r⟩⟩
  · rintro ⟨hb, h⟩
    exact ⟨⟨hb, fun r => (h r).2⟩, fun r => (h r).1⟩

/-- Every residual has strictly fewer retained generators, so the
polynomial recursion terminates at the empty family. -/
theorem retainedFacetResidual_card_lt (hE : UnitIntervalFacetFamily E)
    (A : ∀ r : Fin (d+1),Finset (Fin N))
    {a : (Fin (d+1) → Fin N)} (ha : a ∈ finiteRowRestriction E A) :
    (finiteRowRestriction (facetResidualFacets E a) A).card < (finiteRowRestriction E A).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro b hb
    obtain ⟨hb,hA⟩ := (mem_finiteRowRestriction _ A b).mp hb
    exact (mem_finiteRowRestriction E A b).mpr
      ⟨((mem_facetResidualFacets a b).mp hb).1,hA⟩
  · intro he
    have har : a ∈ finiteRowRestriction (facetResidualFacets E a) A := he.symm ▸ ha
    have hres := ((mem_finiteRowRestriction _ A a).mp har).1
    exact (facetResidualFacets_predecessor hE
      ((mem_finiteRowRestriction E A a).mp ha).1 hres).2 rfl

end UnitInterval
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.unitIntervalRetainedPredecessorColon_eq

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.VariableRestrictionBetti -/
section

/-! # Actual smaller polynomial rings for retained variables

The ordered inclusion gives a signed isomorphism of the genuine quotient
Koszul strands. The unused ambient variables contract in every degree
where they occur. Consequently the finite Betti polynomial computed in
the ambient ring agrees with that in the literal retained-variable ring.
The final comap identity identifies its ideal with I ∩ S_U.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V W k : Type u} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [Field k]

/-- Monomial generators under an actual inclusion of variable sets. -/
def embeddedMonomialFamily (e : V ↪ W) (B : Family V) : Family W :=
  B.image (fun a => a.embDomain e)

lemma contains_embeddedMonomialFamily (e : V ↪ W) (B : Family V) (α : Exponent V) :
    Contains (embeddedMonomialFamily e B) (α.embDomain e) ↔ Contains B α := by
  constructor
  · rintro ⟨c,hc,hcα⟩
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨b,hb,(Finsupp.embDomain_le_embDomain_iff_le e b α).mp hcα⟩
  · rintro ⟨b,hb,hbα⟩
    exact ⟨b.embDomain e,Finset.mem_image.mpr ⟨b,hb,rfl⟩,
      (Finsupp.embDomain_le_embDomain_iff_le e b α).mpr hbα⟩

lemma faceExponent_map_embedding (e : V ↪ W) (F : Finset V) :
    faceExponent (F.map e)=(faceExponent F).embDomain e := by
  ext w
  by_cases hw : w ∈ Set.range e
  · obtain ⟨v,rfl⟩ := hw
    rw [Finsupp.embDomain_apply_self]
    simp only [faceExponent_apply,Finset.mem_map]
    have hm : (∃ a,a∈F ∧ e a=e v) ↔ v∈F := by
      constructor
      · rintro ⟨a,ha,hav⟩
        exact e.injective hav ▸ ha
      · exact fun h => ⟨v,h,rfl⟩
    simp only [hm]
  · rw [Finsupp.embDomain_of_notMem_range _ _ _ hw]
    simp only [faceExponent_apply,ite_eq_right_iff,one_ne_zero]
    intro hm
    obtain ⟨v,hv,hvw⟩ := Finset.mem_map.mp hm
    exact hw ⟨v,hvw⟩

lemma embedded_quotientFace_range (e : V ↪o W) (B : Family V) (α : Exponent V)
    (F : Finset W) (hF : quotientKoszulFaces (embeddedMonomialFamily e.toEmbedding B)
      (α.embDomain e.toEmbedding) F) : ∃ G : Finset V,F=G.map e.toEmbedding := by
  have hrange : ∀ w∈F,w∈Set.range e := by
    intro w hw
    by_contra hn
    have hh := hF.1 w
    rw [faceExponent_apply,if_pos hw,Finsupp.embDomain_of_notMem_range _ _ _ hn] at hh
    omega
  let G := Finset.univ.filter (fun v => e v ∈ F)
  refine ⟨G,?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨v,rfl⟩ := hrange w hw
    exact Finset.mem_map.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩
  · rintro hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
    exact (Finset.mem_filter.mp hv).2

/-- A genuine isomorphism of the quotient Koszul homogeneous complexes. -/
def quotientEmbeddedComplexIso (e : V ↪o W) (B : Family V) (α : Exponent V) :
    quotientHomogeneousComplex (k := k) B α ≅
      quotientHomogeneousComplex (k := k) (embeddedMonomialFamily e.toEmbedding B)
        (α.embDomain e.toEmbedding) :=
  quotientHomogeneousRestrictionIso e B α (embeddedMonomialFamily e.toEmbedding B)
    (α.embDomain e.toEmbedding)
    (by
      intro F
      change (faceExponent (F.map e.toEmbedding)≤α.embDomain e.toEmbedding ∧
        ¬Contains (embeddedMonomialFamily e.toEmbedding B)
          (α.embDomain e.toEmbedding-faceExponent (F.map e.toEmbedding))) ↔ _
      rw [faceExponent_map_embedding,← Finsupp.embDomain_tsub,
        Finsupp.embDomain_le_embDomain_iff_le,contains_embeddedMonomialFamily]
      rfl)
    (embedded_quotientFace_range e B α)

theorem quotientBetti_embedded (e : V ↪o W) (B : Family V) (α : Exponent V) (p : ℕ) :
    quotientBettiNumber (k := k) B α p =
      quotientBettiNumber (k := k) (embeddedMonomialFamily e.toEmbedding B)
        (α.embDomain e.toEmbedding) p := by
  rw [quotientBettiNumber_eq_homology,quotientBettiNumber_eq_homology]
  exact ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) p).mapIso
    (quotientEmbeddedComplexIso (k := k) e B α)).toLinearEquiv.finrank_eq

lemma quotientFaceBettiPolynomial_embedded (e : V ↪o W) (B : Family V) (F : Finset V) :
    quotientFaceBettiPolynomial (k := k) B F =
      quotientFaceBettiPolynomial (k := k) (embeddedMonomialFamily e.toEmbedding B)
        (F.map e.toEmbedding) := by
  apply Polynomial.ext
  intro p
  rw [quotientFaceBettiPolynomial_coeff,quotientFaceBettiPolynomial_coeff,faceExponent_map_embedding]
  exact quotientBetti_embedded e B (faceExponent F) p

def embeddedFaceEquiv (e : V ↪ W) :
    Finset V ≃ {F : Finset W // ∀ w∈F,w∈Set.range e} :=
  Equiv.ofBijective (fun F => ⟨F.map e,by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
    exact ⟨v,rfl⟩⟩) ⟨by
      intro F G h
      exact Finset.map_injective e (congrArg Subtype.val h),by
      intro F
      let G := Finset.univ.filter (fun v => e v∈F.val)
      refine ⟨G,Subtype.ext ?_⟩
      ext w
      constructor
      · rintro hw
        obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
        exact (Finset.mem_filter.mp hv).2
      · intro hw
        obtain ⟨v,rfl⟩ := F.property w hw
        exact Finset.mem_map.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩⟩

/-- Adding unused polynomial variables leaves the actual Betti polynomial
unchanged, with the comparison induced by the literal variable inclusion. -/
theorem quotientBettiPolynomial_embedded (e : V ↪o W) (B : Family V) :
    quotientBettiPolynomial (k := k) B =
      quotientBettiPolynomial (k := k) (embeddedMonomialFamily e.toEmbedding B) := by
  let f := fun F : Finset W => Polynomial.monomial F.card
    (quotientFaceBettiPolynomial (k := k) (embeddedMonomialFamily e.toEmbedding B) F)
  have hz : ∑ F : {F : Finset W // ¬∀ w∈F,w∈Set.range e},f F.val=0 := by
    apply Finset.sum_eq_zero
    intro F _
    have hnot := F.property
    push_neg at hnot
    obtain ⟨w,hw,hrange⟩ := hnot
    have hzero : ∀ b ∈ embeddedMonomialFamily e.toEmbedding B,b w=0 := by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
      exact Finsupp.embDomain_of_notMem_range _ _ _ hrange
    dsimp only [f]
    rw [quotientFaceBettiPolynomial_eq_zero_of_unused _ F.val w hw hzero,map_zero]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun F : Finset W => ∀ w∈F,w∈Set.range e) f
  rw [hz,add_zero] at hs
  change (∑ F : Finset V,Polynomial.monomial F.card
    (quotientFaceBettiPolynomial (k := k) B F))=∑ F : Finset W,f F
  rw [← hs]
  apply Fintype.sum_equiv (embeddedFaceEquiv e.toEmbedding)
  intro F
  change Polynomial.monomial F.card (quotientFaceBettiPolynomial (k := k) B F) =
    Polynomial.monomial (F.map e.toEmbedding).card
      (quotientFaceBettiPolynomial (k := k) (embeddedMonomialFamily e.toEmbedding B) (F.map e.toEmbedding))
  rw [Finset.card_map, ← quotientFaceBettiPolynomial_embedded (k := k) e B F]

/-- Coefficientwise monomial membership proves the literal intersection
identity in a smaller polynomial ring. -/
theorem monomialIdeal_comap_rename (e : V ↪ W) (B : Family V) (C : Family W)
    (h : ∀ α,Contains C (α.embDomain e) ↔ Contains B α) :
    (monomialIdeal k C).comap (MvPolynomial.rename e).toRingHom=monomialIdeal k B := by
  ext f
  change MvPolynomial.rename e f ∈ monomialIdeal k C ↔ f∈monomialIdeal k B
  rw [mem_monomialIdeal_iff,mem_monomialIdeal_iff]
  constructor
  · intro hf α hα
    apply (h α).mp
    apply hf
    rw [MvPolynomial.mem_support_iff,MvPolynomial.coeff_rename_embDomain]
    exact MvPolynomial.mem_support_iff.mp hα
  · intro hf β hβ
    obtain ⟨α,hα,hc⟩ := MvPolynomial.coeff_rename_ne_zero e f β
      (MvPolynomial.mem_support_iff.mp hβ)
    rw [← Finsupp.embDomain_eq_mapDomain e α] at hα
    rw [← hα]
    exact (h α).mpr (hf α (MvPolynomial.mem_support_iff.mpr hc))

section Retained
variable (U : Finset V)

def retainedOrderEmbedding : {v : V // v∈U} ↪o V where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- The retained polynomial ring is the actual subalgebra k[U] of the
ambient polynomial ring, with its standard polynomial coordinates. -/
def retainedRingEquiv :
    MvPolynomial.supported k (U : Set V) ≃ₐ[k] MvPolynomial {v : V // v∈U} k :=
  MvPolynomial.supportedEquivMvPolynomial (U : Set V)

@[simp] theorem retainedRingEquiv_symm_X (v : {v : V // v∈U}) :
    ((retainedRingEquiv (k := k) U).symm (MvPolynomial.X v) : MvPolynomial V k) =
      MvPolynomial.X v.val :=
  MvPolynomial.supportedEquivMvPolynomial_symm_X (U : Set V) v

theorem retainedVariableInclusion_injective :
    Function.Injective (MvPolynomial.rename (retainedOrderEmbedding U) :
      MvPolynomial {v : V // v∈U} k → MvPolynomial V k) :=
  MvPolynomial.rename_injective _ (retainedOrderEmbedding U).injective

/-- Generators in the literal smaller polynomial ring k[U]. -/
def retainedGeneratorFamily (B : Family V) : Family {v : V // v∈U} :=
  (restrictMonomialFamily U B).image (Finsupp.subtypeDomain (fun v => v∈U))

lemma embedded_retainedGeneratorFamily (B : Family V) :
    embeddedMonomialFamily (retainedOrderEmbedding U).toEmbedding (retainedGeneratorFamily U B) =
      restrictMonomialFamily U B := by
  have he : ∀ b∈restrictMonomialFamily U B,
      (Finsupp.subtypeDomain (fun v => v∈U) b).embDomain (retainedOrderEmbedding U).toEmbedding=b := by
    intro b hb
    change (Finsupp.subtypeDomain (fun v => v∈U) b).embDomain (Function.Embedding.subtype _) = b
    rw [← Finsupp.extendDomain_eq_embDomain_subtype]
    apply Finsupp.extendDomain_subtypeDomain
    intro v hv
    exact (mem_restrictMonomialFamily.mp hb).2 v (Finsupp.mem_support_iff.mp hv)
  ext b
  constructor
  · intro hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    rwa [he a ha]
  · intro hb
    exact Finset.mem_image.mpr ⟨Finsupp.subtypeDomain (fun v => v∈U) b,
      Finset.mem_image.mpr ⟨b,hb,rfl⟩,he b hb⟩

/-- Actual smaller-ring and ambient-ring Betti polynomials agree. -/
theorem retainedQuotientBettiPolynomial_eq (B : Family V) :
    quotientBettiPolynomial (k := k) (retainedGeneratorFamily U B) =
      quotientBettiPolynomial (k := k) (restrictMonomialFamily U B) := by
  rw [quotientBettiPolynomial_embedded (retainedOrderEmbedding U),embedded_retainedGeneratorFamily]

/-- The smaller-ring monomial ideal is literally the inverse image of I
under the inclusion k[U] → k[V], that is I ∩ k[U]. -/
theorem retainedGeneratorFamily_ideal (B : Family V) :
    monomialIdeal k (retainedGeneratorFamily U B) =
      (monomialIdeal k B).comap (MvPolynomial.rename (retainedOrderEmbedding U)).toRingHom := by
  symm
  apply monomialIdeal_comap_rename (retainedOrderEmbedding U).toEmbedding
  intro α
  have hf : (α.embDomain (retainedOrderEmbedding U).toEmbedding).filter (fun v => v∈U)=
      α.embDomain (retainedOrderEmbedding U).toEmbedding := by
    ext v
    by_cases hv : v∈U
    · simp [Finsupp.filter_apply,hv]
    · have hn : v∉Set.range (retainedOrderEmbedding U) := by
        rintro ⟨w,rfl⟩
        exact hv w.property
      rw [Finsupp.embDomain_of_notMem_range _ _ _ hn]
      simp [Finsupp.filter_apply,hv]
  calc
    Contains B (α.embDomain (retainedOrderEmbedding U).toEmbedding) ↔
        Contains (restrictMonomialFamily U B) (α.embDomain (retainedOrderEmbedding U).toEmbedding) := by
      rw [contains_restrictMonomialFamily,hf]
    _ ↔ Contains (embeddedMonomialFamily (retainedOrderEmbedding U).toEmbedding
        (retainedGeneratorFamily U B)) (α.embDomain (retainedOrderEmbedding U).toEmbedding) := by
      rw [embedded_retainedGeneratorFamily]
    _ ↔ Contains (retainedGeneratorFamily U B) α := contains_embeddedMonomialFamily _ _ _

lemma retainedGeneratorFamily_squarefree (B : Family V) (hB : ∀ b∈B,∀ v,b v≤1) :
    ∀ b∈retainedGeneratorFamily U B,∀ v,b v≤1 := by
  intro b hb
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
  intro v
  exact hB c (mem_restrictMonomialFamily.mp hc).1 v.val

end Retained

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalCliqueCutoff -/
section

/-!
# The cutoff in Lemma 6.1 and maximal interval cliques

The proof of the colon formula uses a minimum over facets, avoiding an
arbitrary enumeration of the maximal cliques. This file proves that this
minimum is precisely the left endpoint of the first maximal interval
clique whose right endpoint reaches the last column of the given facet.
There are `d+1` rows, and the comparison with clique endpoints assumes
`1 ≤ d`, exactly the paper's requirement of at least two rows.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section

namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid
universe u
variable {d N : ℕ} {E : Finset (Fin (d+1) → Fin N)}

/-- A nonempty complete uniform family on the column interval `[l,u]`.
The witness says that the interval contains a tuple of the required size;
the second clause says that every such tuple is a facet. -/
def CompleteFacetInterval (E : Finset (Fin (d+1) → Fin N)) (l u : Fin N) : Prop :=
  (∃ a : Fin (d+1) → Fin N, StrictMono a ∧ l ≤ a 0 ∧ a (Fin.last d) ≤ u) ∧
    ∀ a : Fin (d+1) → Fin N, StrictMono a → l ≤ a 0 → a (Fin.last d) ≤ u → a ∈ E

/-- Maximality under inclusion of the actual column intervals. -/
def MaximalFacetInterval (E : Finset (Fin (d+1) → Fin N)) (l u : Fin N) : Prop :=
  CompleteFacetInterval E l u ∧
    ∀ l' u', CompleteFacetInterval E l' u' → l' ≤ l → u ≤ u' → l' = l ∧ u' = u

private def extendFacetEndpoints (a : Fin (d+1) → Fin N) (l u : Fin N)
    (i : Fin (d+1)) : Fin N :=
  if i = 0 then l else if i = Fin.last d then u else a i

private lemma extendFacetEndpoints_first (a : Fin (d+1) → Fin N) (l u : Fin N) :
    extendFacetEndpoints a l u 0 = l := by
  simp [extendFacetEndpoints]

private lemma extendFacetEndpoints_last (hd : 1 ≤ d)
    (a : Fin (d+1) → Fin N) (l u : Fin N) :
    extendFacetEndpoints a l u (Fin.last d) = u := by
  have hne : Fin.last d ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  simp [extendFacetEndpoints, hne]

private lemma extendFacetEndpoints_strictMono
    {a : Fin (d+1) → Fin N} (ha : StrictMono a) {l u : Fin N}
    (hl : l ≤ a 0) (hu : a (Fin.last d) ≤ u) :
    StrictMono (extendFacetEndpoints a l u) := by
  intro i j hij
  have hiLast : i ≠ Fin.last d := by
    intro hi
    subst i
    exact (not_lt_of_ge (Fin.le_last j)) hij
  have hjZero : j ≠ 0 := by
    intro hj
    subst j
    have hv : i.val < 0 := hij
    omega
  by_cases hiZero : i = 0
  · subst i
    by_cases hjLast : j = Fin.last d
    · subst j
      simpa [extendFacetEndpoints, hjZero] using
        hl.trans_lt ((ha hij).trans_le hu)
    · simpa [extendFacetEndpoints, hjZero, hjLast] using
        hl.trans_lt (ha hij)
  · by_cases hjLast : j = Fin.last d
    · subst j
      simpa [extendFacetEndpoints, hiZero, hiLast, hjZero] using (ha hij).trans_le hu
    · simpa [extendFacetEndpoints, hiZero, hiLast, hjZero, hjLast] using ha hij

/-- With at least two rows, a complete interval contains a facet attaining
both of its endpoints. This justifies passing from cliques to facet minima. -/
theorem CompleteFacetInterval.exists_endpoint_facet (hd : 1 ≤ d)
    {l u : Fin N} (h : CompleteFacetInterval E l u) :
    ∃ a ∈ E, a 0 = l ∧ a (Fin.last d) = u := by
  obtain ⟨a, ha, hl, hu⟩ := h.1
  let b := extendFacetEndpoints a l u
  have hb : StrictMono b := extendFacetEndpoints_strictMono ha hl hu
  have hb0 : b 0 = l := extendFacetEndpoints_first a l u
  have hblast : b (Fin.last d) = u := extendFacetEndpoints_last hd a l u
  exact ⟨b, h.2 b hb (by rw [hb0]) (by rw [hblast]), hb0, hblast⟩

theorem UnitIntervalFacetFamily.complete_interval_of_facet
    (hE : UnitIntervalFacetFamily E) {a : Fin (d+1) → Fin N} (ha : a ∈ E) :
    CompleteFacetInterval E (a 0) (a (Fin.last d)) :=
  ⟨⟨a, hE.increasing a ha, le_rfl, le_rfl⟩,
    fun b hb hl hu => hE.interval a ha b hb hl hu⟩

/-- For a unit-interval family, the complete intervals are exactly the
endpoint intervals of facets. Both directions are proved without choosing
or assuming a list of maximal cliques. -/
theorem completeFacetInterval_iff_endpoint_facet
    (hd : 1 ≤ d) (hE : UnitIntervalFacetFamily E) (l u : Fin N) :
    CompleteFacetInterval E l u ↔ ∃ a ∈ E, a 0 = l ∧ a (Fin.last d) = u := by
  constructor
  · exact fun h => h.exists_endpoint_facet hd
  · rintro ⟨a, ha, hfirst, hlast⟩
    simpa only [hfirst, hlast] using hE.complete_interval_of_facet ha

/-- Every complete interval is contained in a maximal complete interval.
The finite maximization is of interval length, not a new assumption. -/
theorem CompleteFacetInterval.exists_maximal_extension
    {l u : Fin N} (h : CompleteFacetInterval E l u) :
    ∃ l' u', MaximalFacetInterval E l' u' ∧ l' ≤ l ∧ u ≤ u' := by
  let C : Finset (Fin N × Fin N) := Finset.univ.filter
    (fun p => CompleteFacetInterval E p.1 p.2 ∧ p.1 ≤ l ∧ u ≤ p.2)
  have hC : C.Nonempty := by
    refine ⟨(l, u), ?_⟩
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h, le_rfl, le_rfl⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image C
    (fun p => N - p.1.val + p.2.val) hC
  have hp' : CompleteFacetInterval E p.1 p.2 ∧ p.1 ≤ l ∧ u ≤ p.2 :=
    (Finset.mem_filter.mp hp).2
  refine ⟨p.1, p.2, ⟨hp'.1, ?_⟩, hp'.2.1, hp'.2.2⟩
  intro l' u' h' hl' hu'
  have hmem : (l', u') ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, h', hl'.trans hp'.2.1, hp'.2.2.trans hu'⟩
  have hw : N - l'.val + u'.val ≤ N - p.1.val + p.2.val := hmax (l', u') hmem
  have hleft : l'.val ≤ p.1.val := hl'
  have hright : p.2.val ≤ u'.val := hu'
  have hlN := l'.isLt
  have hpN := p.1.isLt
  constructor <;> apply Fin.ext <;> omega

/-- The facet predicate is exactly the union of the complete uniform
families on the maximal interval cliques, as in the paper's definition. -/
theorem facet_mem_iff_maximalInterval
    (hE : UnitIntervalFacetFamily E) (a : Fin (d+1) → Fin N) :
    a ∈ E ↔ StrictMono a ∧ ∃ l u, MaximalFacetInterval E l u ∧
      l ≤ a 0 ∧ a (Fin.last d) ≤ u := by
  constructor
  · intro ha
    exact ⟨hE.increasing a ha, (hE.complete_interval_of_facet ha).exists_maximal_extension⟩
  · rintro ⟨ha, l, u, hmax, hl, hu⟩
    exact hmax.1.2 a ha hl hu

/-- The maximal interval cliques have the same strict order at both
endpoints, justifying the ordering convention in the paper. -/
theorem maximalFacetIntervals_endpoint_order
    {l₁ u₁ l₂ u₂ : Fin N}
    (h₁ : MaximalFacetInterval E l₁ u₁) (h₂ : MaximalFacetInterval E l₂ u₂) :
    l₁ < l₂ ↔ u₁ < u₂ := by
  constructor
  · intro hl
    by_contra hu
    have he := h₂.2 l₁ u₁ h₁.1 hl.le (le_of_not_gt hu)
    exact hl.ne he.1
  · intro hu
    by_contra hl
    have he := h₁.2 l₂ u₂ h₂.1 (le_of_not_gt hl) hu.le
    exact hu.ne he.2.symm

/-- The cutoff is an attained minimum of the qualifying maximal-clique
left endpoints. Together with `maximalFacetIntervals_endpoint_order`, this
is exactly the left endpoint of the first clique reaching the last column. -/
theorem facetCutoff_minimal_maximalInterval
    (hd : 1 ≤ d) (hE : UnitIntervalFacetFamily E)
    {a : Fin (d+1) → Fin N} (ha : a ∈ E) :
    (∃ u, MaximalFacetInterval E (facetCutoff ha) u ∧ a (Fin.last d) ≤ u) ∧
    (∀ l u, MaximalFacetInterval E l u → a (Fin.last d) ≤ u → facetCutoff ha ≤ l) := by
  have hmin : ∀ l u, MaximalFacetInterval E l u →
      a (Fin.last d) ≤ u → facetCutoff ha ≤ l := by
    intro l u hmax hu
    obtain ⟨b, hb, hb0, hblast⟩ := hmax.1.exists_endpoint_facet hd
    apply (facetCutoff_le_iff ha l).mpr
    exact ⟨b, hb, hb0.le, by rwa [hblast]⟩
  refine ⟨?_, hmin⟩
  have hm := Finset.min'_mem (facetCutoffCandidates E a)
    (facetCutoffCandidates_nonempty ha)
  obtain ⟨b, hb, hb0⟩ := Finset.mem_image.mp hm
  obtain ⟨hbE, hab⟩ := Finset.mem_filter.mp hb
  obtain ⟨l, u, hmax, hl, hu⟩ :=
    (hE.complete_interval_of_facet hbE).exists_maximal_extension
  have hlu : a (Fin.last d) ≤ u := hab.trans hu
  have hlc : l = facetCutoff ha := le_antisymm
    (by simpa only [facetCutoff] using hl.trans hb0.le) (hmin l u hmax hlu)
  exact ⟨u, hlc ▸ hmax, hlu⟩

/-- Independence of the choice of an explicitly listed first qualifying
clique: any such list yields precisely the cutoff used in the formal proof. -/
theorem facetCutoff_eq_first_maximalInterval
    (hd : 1 ≤ d) (hE : UnitIntervalFacetFamily E)
    {a : Fin (d+1) → Fin N} (ha : a ∈ E) {l u : Fin N}
    (hmax : MaximalFacetInterval E l u) (hu : a (Fin.last d) ≤ u)
    (hfirst : ∀ l' u', MaximalFacetInterval E l' u' →
      a (Fin.last d) ≤ u' → l ≤ l') :
    facetCutoff ha = l := by
  have h := facetCutoff_minimal_maximalInterval hd hE ha
  obtain ⟨u', hmax', hu'⟩ := h.1
  exact le_antisymm (h.2 l u hmax hu) (hfirst _ u' hmax' hu')

/-- The first-row part of the paper's displayed linear ideal `L_a`. -/
theorem facetLinearVariables_zero_cutoff
    {a : Fin (d+1) → Fin N} (ha : a ∈ E) (j : Fin N) :
    (⟨0, ULift.up j⟩ : FiniteVariable.{u} (UnitIntervalRows d N)) ∈ facetLinearVariables E a ↔
      facetCutoff ha ≤ j ∧ j < a 0 := by
  rw [facetLinearVariables_zero, ← facetCutoff_le_iff ha j]
  exact and_comm

/-- The paper's displayed residual facet inequalities, with its numeric
cutoff rather than the equivalent cover predicate. -/
theorem mem_facetResidualFacets_cutoff
    {a : Fin (d+1) → Fin N} (ha : a ∈ E) (b : Fin (d+1) → Fin N) :
    b ∈ facetResidualFacets E a ↔ b ∈ E ∧ b 0 < facetCutoff ha ∧
      ∀ r : Fin d, b r.succ ≤ a r.castSucc := by
  rw [mem_facetResidualFacets, ← facetCutoff_le_iff ha (b 0), not_le]

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.facetCutoff_minimal_maximalInterval
#print axioms FourPapers.Sublattice.facetCutoff_eq_first_maximalInterval
#print axioms FourPapers.Sublattice.maximalFacetIntervals_endpoint_order
#print axioms FourPapers.Sublattice.facetLinearVariables_zero_cutoff
#print axioms FourPapers.Sublattice.mem_facetResidualFacets_cutoff

#print axioms FourPapers.Sublattice.completeFacetInterval_iff_endpoint_facet
#print axioms FourPapers.Sublattice.facet_mem_iff_maximalInterval

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.UnitIntervalLemma61Fine -/
section

/-!
# The fine-degree consequences of Lemma 6.1

These statements concern the quotient over the literal retained-variable
polynomial ring. The ideal in that ring is `I ∩ S_U`, by
`retainedGeneratorFamily_ideal`. Arbitrary retained sets are allowed in
every row. The dimensions are those of actual derived Tor, including all
integer fine degrees and all integer ordinary degrees.

The field comparison comes from the integral zero-or-one free homology
model. The support congruence comes from homogeneous fillings of the actual
quotient Koszul cycles. Neither conclusion is inserted into the definition
of the Betti numbers.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

/-- Every subset of matrix variables is uniquely specified row by row;
this definition extracts those completely arbitrary row subsets. -/
def retainedRowsOfVariables {t : ℕ} {n : Fin t → ℕ}
    (U : Finset (FiniteVariable.{u} n)) : ∀ r, Finset (Fin (n r)) :=
  fun r => Finset.univ.filter (fun j => (⟨r, ULift.up j⟩ : FiniteVariable.{u} n) ∈ U)

@[simp] theorem retainedRowVariables_rowsOfVariables {t : ℕ} {n : Fin t → ℕ}
    (U : Finset (FiniteVariable.{u} n)) :
    retainedRowVariables (retainedRowsOfVariables U) = U := by
  ext ⟨r, ⟨j⟩⟩
  simp only [mem_retainedRowVariables, retainedRowsOfVariables,
    Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem retainedRowsOfVariables_rowVariables {t : ℕ} {n : Fin t → ℕ}
    (A : ∀ r, Finset (Fin (n r))) :
    retainedRowsOfVariables (retainedRowVariables A) = A := by
  funext r
  ext j
  simp only [retainedRowsOfVariables, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_retainedRowVariables]

variable {d N : ℕ} {E : Finset (Fin (d + 1) → Fin N)}
variable {K L : Type u} [Field K] [Field L]

/-- Every fine quotient Betti number of an arbitrary variable restriction
is independent of the field, as follows by base change from the integers. -/
theorem unitInterval_restricted_quotient_betti_field_independent
    (hE : UnitIntervalFacetFamily E)
    (A : ∀ r, Finset (Fin (UnitIntervalRows d N r)))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ) :
    quotientBettiNumber (k := K)
        (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α p =
      quotientBettiNumber (k := L)
        (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α p := by
  let R := ULift.{u} ℤ
  letI : IsDomain R := MulEquiv.isDomain ℤ (ULift.ringEquiv : R ≃+* ℤ).toMulEquiv
  letI : Algebra R K := ULift.algebra' ℤ K
  letI : Algebra R L := ULift.algebra' ℤ L
  let B := finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)
  have hfree (i : ℕ) : Module.Free R (ClosedGraphDegreeHomology (k := R) B α i) :=
    (closedGraphDegreeHomology_small_of_total (k := R) B α i
      (unitInterval_restricted_homology_small (k := R) hE A α)).free
  have hK := quotientDegreeHomology_finrank_baseChange (R := R) (S := K) B α hfree p
  have hL := quotientDegreeHomology_finrank_baseChange (R := R) (S := L) B α hfree p
  rw [quotientBettiNumber_eq_homology, quotientBettiNumber_eq_homology,
    (quotientCategoricalDegreeHomologyEquiv (k := K) B α p).finrank_eq,
    (quotientCategoricalDegreeHomologyEquiv (k := L) B α p).finrank_eq]
  exact hK.trans hL.symm

/-- Outside the residue required by Lemma 6.1 every homogeneous quotient
cycle bounds, so the actual quotient Betti number is zero. -/
theorem unitInterval_restricted_quotient_betti_zero
    (hE : UnitIntervalFacetFamily E)
    (A : ∀ r, Finset (Fin (UnitIntervalRows d N r)))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ)
    (hp : (p : ZMod d) ≠ (α.degree : ZMod d)) :
    quotientBettiNumber (k := K)
      (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α p = 0 := by
  let B := finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)
  have hzero : ∀ x : ClosedGraphDegreeHomology (k := K) B α p, x = 0 := by
    intro x
    obtain ⟨z, rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary (k := K) B α p)).mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hfill := unitInterval_restricted_residue_cycle_boundary (k := K) hE A α (p : ZMod d)
      z.val (faceResidueSpace_of_homogeneous _ p d z.property.2) z.property.1 hp
    obtain ⟨y, hy, hdy⟩ := quotient_boundary_homogeneous (k := K) B α p z.val z.property.2 hfill
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩
  letI : Subsingleton (ClosedGraphDegreeHomology (k := K) B α p) :=
    subsingleton_of_forall_eq 0 hzero
  letI : Subsingleton ((quotientHomogeneousComplex (k := K) B α).homology p) :=
    (quotientCategoricalDegreeHomologyEquiv (k := K) B α p).injective.subsingleton
  rw [quotientBettiNumber_eq_homology]
  exact Module.finrank_zero_of_subsingleton

theorem unitInterval_restricted_quotient_betti_congruence
    (hE : UnitIntervalFacetFamily E)
    (A : ∀ r, Finset (Fin (UnitIntervalRows d N r)))
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) (p : ℕ)
    (hβ : quotientBettiNumber (k := K)
      (finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A)) α p ≠ 0) :
    (α.degree : ZMod d) - (p : ZMod d) = 0 := by
  apply sub_eq_zero.mpr
  by_contra h
  exact hβ (unitInterval_restricted_quotient_betti_zero hE A α p (Ne.symm h))

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- Field independence in `S_U`, with its own polynomial variables and its
own residue field. The ideal is the literal intersection `I ∩ S_U`. -/
theorem lemma61_retained_ring_fine_field_independent
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (α : Exponent {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ retainedRowVariables A})
    (p : ℕ) :
    quotientBettiNumber (k := K)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) α p =
      quotientBettiNumber (k := L)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) α p := by
  let e := retainedOrderEmbedding (retainedRowVariables A)
  let B := retainedGeneratorFamily (retainedRowVariables A)
    (finiteRowFamily (UnitIntervalRows d N) E)
  have hK := quotientBetti_embedded (k := K) e B α p
  have hL := quotientBetti_embedded (k := L) e B α p
  have hB : embeddedMonomialFamily e.toEmbedding B =
      finiteRowFamily (UnitIntervalRows d N) (finiteRowRestriction E A) := by
    dsimp only [e, B]
    rw [embedded_retainedGeneratorFamily]
    exact restrictMonomialFamily_rows (n := UnitIntervalRows d N) A E
  rw [hB] at hK hL
  exact hK.trans ((unitInterval_restricted_quotient_betti_field_independent
    (K := K) (L := L) hE A (α.embDomain e.toEmbedding) p).trans hL.symm)

/-- The exact fine support congruence in the retained ring. Lean's `d+1`
rows correspond to the paper's `d` rows, hence the modulus is `d` here. -/
theorem lemma61_retained_ring_fine_supportCongruence
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (α : Exponent {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ retainedRowVariables A})
    (p : ℕ)
    (hβ : quotientBettiNumber (k := K)
      (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) α p ≠ 0) :
    (α.degree : ZMod d) - (p : ZMod d) = 0 := by
  rw [quotientBetti_embedded (retainedOrderEmbedding (retainedRowVariables A)),
    embedded_retainedGeneratorFamily,
    restrictMonomialFamily_rows (n := UnitIntervalRows d N) A E] at hβ
  have h := unitInterval_restricted_quotient_betti_congruence hE A _ p hβ
  simpa only [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain] using h

/-- All signed fine degrees are included: a negative coordinate gives a
zero submodule of actual Tor by integer regrading. -/
theorem lemma61_retained_ring_integer_fine_field_independent
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (α : {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ retainedRowVariables A} →₀ ℤ)
    (p : ℕ) :
    quotientIntegerBettiNumber (k := K)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) α p =
      quotientIntegerBettiNumber (k := L)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) α p := by
  by_cases hα : ∀ v, 0 ≤ α v
  · obtain ⟨a, rfl⟩ := (integerExponent_exists_iff α).mpr hα
    simp only [quotientIntegerBettiNumber_nat]
    exact lemma61_retained_ring_fine_field_independent hE A a p
  · push_neg at hα
    obtain ⟨v, hv⟩ := hα
    rw [quotientIntegerBettiNumber_negative _ _ p hv,
      quotientIntegerBettiNumber_negative _ _ p hv]

/-- The fine congruence for every integer exponent, with the ordinary
degree expressed as the sum of its signed coordinates. -/
theorem lemma61_retained_ring_integer_fine_supportCongruence
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (α : {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ retainedRowVariables A} →₀ ℤ)
    (p : ℕ)
    (hβ : quotientIntegerBettiNumber (k := K)
      (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) α p ≠ 0) :
    ((∑ v, α v : ℤ) : ZMod d) - (p : ZMod d) = 0 := by
  by_cases hα : ∀ v, 0 ≤ α v
  · obtain ⟨a, rfl⟩ := (integerExponent_exists_iff α).mpr hα
    rw [quotientIntegerBettiNumber_nat] at hβ
    have h := lemma61_retained_ring_fine_supportCongruence hE A a p hβ
    simpa only [integerExponent_apply, ← Nat.cast_sum, ← Finsupp.degree_eq_sum,
      Int.cast_natCast] using h
  · push_neg at hα
    obtain ⟨v, hv⟩ := hα
    exact (hβ (quotientIntegerBettiNumber_negative _ _ p hv)).elim

theorem lemma61_retained_ring_ordinary_field_independent
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (q p : ℕ) :
    ordinaryQuotientBettiNumber (k := K)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) q p =
      ordinaryQuotientBettiNumber (k := L)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) q p := by
  rw [ordinaryQuotientBettiNumber_eq_sum, ordinaryQuotientBettiNumber_eq_sum]
  exact Finset.sum_congr rfl (fun a _ => lemma61_retained_ring_fine_field_independent hE A a.val p)

theorem lemma61_retained_ring_ordinary_supportCongruence
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (q p : ℕ)
    (hβ : ordinaryQuotientBettiNumber (k := K)
      (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) q p ≠ 0) :
    (q : ZMod d) - (p : ZMod d) = 0 := by
  rw [ordinaryQuotientBettiNumber_eq_sum] at hβ
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  simpa only [a.property] using lemma61_retained_ring_fine_supportCongruence hE A a.val p ha

theorem lemma61_retained_ring_integer_field_independent
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (q : ℤ) (p : ℕ) :
    integerOrdinaryQuotientBettiNumber (K := K)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) q p =
      integerOrdinaryQuotientBettiNumber (K := L)
        (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) q p := by
  by_cases hq : 0 ≤ q
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    simp only [integerOrdinaryQuotientBettiNumber_nat]
    exact lemma61_retained_ring_ordinary_field_independent hE A j p
  · rw [integerOrdinaryQuotientBettiNumber_negative _ _ (lt_of_not_ge hq) p,
      integerOrdinaryQuotientBettiNumber_negative _ _ (lt_of_not_ge hq) p]

theorem lemma61_retained_ring_integer_supportCongruence
    (hE : UnitIntervalFacetFamily E) (A : ∀ r : Fin (d + 1), Finset (Fin N))
    (q : ℤ) (p : ℕ)
    (hβ : integerOrdinaryQuotientBettiNumber (K := K)
      (retainedGeneratorFamily (retainedRowVariables A) (finiteRowFamily (UnitIntervalRows d N) E)) q p ≠ 0) :
    (q : ZMod d) - (p : ZMod d) = 0 := by
  by_cases hq : 0 ≤ q
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    rw [integerOrdinaryQuotientBettiNumber_nat] at hβ
    simpa only [Int.cast_natCast] using
      lemma61_retained_ring_ordinary_supportCongruence hE A j p hβ
  · exact (hβ (integerOrdinaryQuotientBettiNumber_negative _ _ (lt_of_not_ge hq) p)).elim

/-- The same fine field comparison, stated directly for an arbitrary
subset `U` of matrix variables rather than its equivalent rowwise encoding. -/
theorem lemma61_arbitrary_variables_integer_fine_field_independent
    (hE : UnitIntervalFacetFamily E)
    (U : Finset (FiniteVariable.{u} (UnitIntervalRows d N))) :
    ∀ (α : {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ U} →₀ ℤ) (p : ℕ),
      quotientIntegerBettiNumber (k := K)
          (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) α p =
        quotientIntegerBettiNumber (k := L)
          (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) α p := by
  let P := fun U : Finset (FiniteVariable.{u} (UnitIntervalRows d N)) =>
    ∀ (α : {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ U} →₀ ℤ) (p : ℕ),
      quotientIntegerBettiNumber (k := K)
          (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) α p =
        quotientIntegerBettiNumber (k := L)
          (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) α p
  exact Eq.mp (congrArg P (retainedRowVariables_rowsOfVariables (n := UnitIntervalRows d N) U))
    (lemma61_retained_ring_integer_fine_field_independent (K := K) (L := L) hE
      (retainedRowsOfVariables U))

theorem lemma61_arbitrary_variables_integer_fine_supportCongruence
    (hE : UnitIntervalFacetFamily E)
    (U : Finset (FiniteVariable.{u} (UnitIntervalRows d N))) :
    ∀ (α : {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ U} →₀ ℤ) (p : ℕ),
      quotientIntegerBettiNumber (k := K)
        (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) α p ≠ 0 →
      ((∑ v, α v : ℤ) : ZMod d) - (p : ZMod d) = 0 := by
  let P := fun U : Finset (FiniteVariable.{u} (UnitIntervalRows d N)) =>
    ∀ (α : {v : FiniteVariable.{u} (UnitIntervalRows d N) // v ∈ U} →₀ ℤ) (p : ℕ),
      quotientIntegerBettiNumber (k := K)
        (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) α p ≠ 0 →
      ((∑ v, α v : ℤ) : ZMod d) - (p : ZMod d) = 0
  exact Eq.mp (congrArg P (retainedRowVariables_rowsOfVariables (n := UnitIntervalRows d N) U))
    (lemma61_retained_ring_integer_fine_supportCongruence (K := K) hE
      (retainedRowsOfVariables U))

theorem lemma61_arbitrary_variables_integer_field_independent
    (hE : UnitIntervalFacetFamily E)
    (U : Finset (FiniteVariable.{u} (UnitIntervalRows d N))) (q : ℤ) (p : ℕ) :
    integerOrdinaryQuotientBettiNumber (K := K)
        (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) q p =
      integerOrdinaryQuotientBettiNumber (K := L)
        (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) q p := by
  let P := fun U : Finset (FiniteVariable.{u} (UnitIntervalRows d N)) =>
    integerOrdinaryQuotientBettiNumber (K := K)
        (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) q p =
      integerOrdinaryQuotientBettiNumber (K := L)
        (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) q p
  exact Eq.mp (congrArg P (retainedRowVariables_rowsOfVariables (n := UnitIntervalRows d N) U))
    (lemma61_retained_ring_integer_field_independent (K := K) (L := L) hE
      (retainedRowsOfVariables U) q p)

theorem lemma61_arbitrary_variables_integer_supportCongruence
    (hE : UnitIntervalFacetFamily E)
    (U : Finset (FiniteVariable.{u} (UnitIntervalRows d N))) (q : ℤ) (p : ℕ)
    (hβ : integerOrdinaryQuotientBettiNumber (K := K)
      (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) q p ≠ 0) :
    (q : ZMod d) - (p : ZMod d) = 0 := by
  let P := fun U : Finset (FiniteVariable.{u} (UnitIntervalRows d N)) =>
    integerOrdinaryQuotientBettiNumber (K := K)
      (retainedGeneratorFamily U (finiteRowFamily (UnitIntervalRows d N) E)) q p ≠ 0 →
      (q : ZMod d) - (p : ZMod d) = 0
  exact (Eq.mp (congrArg P
    (retainedRowVariables_rowsOfVariables (n := UnitIntervalRows d N) U))
      (lemma61_retained_ring_integer_supportCongruence (K := K) hE
        (retainedRowsOfVariables U) q p)) hβ

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.lemma61_retained_ring_integer_fine_field_independent
#print axioms FourPapers.Sublattice.lemma61_retained_ring_integer_fine_supportCongruence
#print axioms FourPapers.Sublattice.lemma61_retained_ring_integer_field_independent
#print axioms FourPapers.Sublattice.lemma61_retained_ring_integer_supportCongruence
#print axioms FourPapers.Sublattice.retainedRowVariables_rowsOfVariables
#print axioms FourPapers.Sublattice.lemma61_arbitrary_variables_integer_fine_field_independent
#print axioms FourPapers.Sublattice.lemma61_arbitrary_variables_integer_fine_supportCongruence
#print axioms FourPapers.Sublattice.lemma61_arbitrary_variables_integer_field_independent
#print axioms FourPapers.Sublattice.lemma61_arbitrary_variables_integer_supportCongruence

end
end
end


end
