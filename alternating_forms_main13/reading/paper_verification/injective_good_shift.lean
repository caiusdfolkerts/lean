module

public import PaperVerification.DerivedConcentration
public import PaperVerification.FunctorExtension
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
public import Lean.Elab.Tactic.Omega

/-!
# A single nonzero derived image

This file develops the shift in the Leray comparison when an actual derived
image is concentrated in one degree. The argument uses Mathlib's canonical
truncation. Exactness below the chosen degree makes the successive cokernels
injective: each is a summand of the preceding injective object. Therefore
the canonical truncation is a homotopy equivalence and remains a
quasi-isomorphism after any additive functor.

The general truncation and successor-cokernel calculations follow the
proved constructions in OpenAI/math, commit
`4eaee87548250b2682affda7d05d947c05554bae`, specifically
`CycleClass/Geometric/FlasqueLowDegree` and
`HodgeConjecture/DegreeTwo/GoodShiftCohomology`. Here they are stated for
injective objects in any abelian category, independently of the geometric
applications imported by those files.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace PaperVerification.DerivedConcentration

variable {C : Type*} [Category* C] [Abelian C]

/-- The actual successor-cokernel sequence of a nonnegative complex. -/
abbrev opcyclesSuccessorSequence (K : CochainComplex C ℕ) (n : ℕ) :
    ShortComplex C :=
  ShortComplex.mk (K.fromOpcycles n (n + 1)) (K.pOpcycles (n + 1)) (by
    rw [← cancel_epi (K.pOpcycles n), comp_zero,
      HomologicalComplex.p_fromOpcycles_assoc, HomologicalComplex.d_pOpcycles])

lemma opcyclesSuccessorSequence_exact (K : CochainComplex C ℕ) (n : ℕ) :
    (opcyclesSuccessorSequence K n).Exact := by
  let S := ShortComplex.mk (K.d n (n + 1)) (K.pOpcycles (n + 1))
    (K.d_pOpcycles n (n + 1))
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (K.opcyclesIsCokernel n (n + 1) (by simp))
  let φ : S ⟶ opcyclesSuccessorSequence K n :=
    { τ₁ := K.pOpcycles n
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, opcyclesSuccessorSequence]
      comm₂₃ := by simp [S, opcyclesSuccessorSequence] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS

lemma opcyclesSuccessorSequence_shortExact (K : CochainComplex C ℕ) (n : ℕ)
    (h : K.ExactAt n) : (opcyclesSuccessorSequence K n).ShortExact := by
  have hm : Mono (K.fromOpcycles n (n + 1)) :=
    CategoryTheory.Preadditive.mono_of_isZero_kernel' _ (K.homologyIsKernel n (n + 1) (by simp))
      h.isZero_homology
  exact ShortComplex.ShortExact.mk' (opcyclesSuccessorSequence_exact K n)
    hm inferInstance

lemma injective_third_of_shortExact (S : ShortComplex C) (hS : S.ShortExact)
    [Injective S.X₁] [Injective S.X₂] : Injective S.X₃ := by
  let σ := hS.splittingOfInjective
  exact (show Retract S.X₃ S.X₂ from
    { i := σ.s
      r := S.g
      retract := σ.s_g }).injective

/-- All successive cokernels through the first possible cohomology degree
are injective. No claim is made for later cokernels. -/
lemma injective_opcycles_of_exact_below (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (k : ℕ)
    (he : ∀ n, n < k → K.ExactAt n) :
    ∀ n, n ≤ k → Injective (K.opcycles n) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact Injective.of_iso K.opcycles₀Iso inferInstance
  | succ n ih =>
      intro hn
      haveI := ih (Nat.le_of_succ_le hn)
      exact injective_third_of_shortExact (opcyclesSuccessorSequence K n)
        (opcyclesSuccessorSequence_shortExact K n (he n (Nat.lt_of_succ_le hn)))

/-- Reindexing by `n ↦ k + n`, as an embedding of cochain shapes. -/
def degreeShiftEmbedding (k : ℕ) :
    (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => k + n)
    (fun _ _ h => Nat.add_left_cancel h)
    (by intro i j; change (i + 1 = j) ↔ (k + i + 1 = k + j); omega)

instance (k : ℕ) : (degreeShiftEmbedding k).IsRelIff where
  rel' i j h := by
    change k + i + 1 = k + j at h
    change i + 1 = j
    omega

instance (k : ℕ) : (degreeShiftEmbedding k).IsTruncGE where
  mem_next {j l} h := by
    refine ⟨j + 1, ?_⟩
    change k + j + 1 = l at h
    change k + (j + 1) = l
    omega

/-- The good shift has degree `n` cohomology equal to the original degree
`k+n` cohomology, including at the new left endpoint. -/
def goodShiftHomologyIso (K : CochainComplex C ℕ) (k n : ℕ) :
    (K.truncGE' (degreeShiftEmbedding k)).homology n ≅ K.homology (k + n) := by
  let e := degreeShiftEmbedding k
  haveI : QuasiIsoAt (HomologicalComplex.πTruncGE K e) (k + n) := HomologicalComplex.quasiIsoAt_πTruncGE K e (j := n) rfl
  exact ((K.truncGE' e).extendHomologyIso e (j := n) (j' := k + n) rfl).symm ≪≫
    (isoOfQuasiIsoAt (HomologicalComplex.πTruncGE K e) (k + n)).symm

lemma goodTruncation_quasiIso (K : CochainComplex C ℕ) (k : ℕ)
    (he : ∀ n, n < k → K.ExactAt n) :
    QuasiIso (HomologicalComplex.πTruncGE K (degreeShiftEmbedding k)) := by
  apply (HomologicalComplex.quasiIso_πTruncGE_iff_isSupported K (degreeShiftEmbedding k)).mpr
  constructor
  intro n hn
  apply he n
  by_contra h
  have heq : (degreeShiftEmbedding k).f (n - k) = n := by
    change k + (n - k) = n
    omega
  exact hn (n - k) heq

lemma injective_goodShift (K : CochainComplex C ℕ) [∀ n, Injective (K.X n)]
    (k : ℕ) (he : ∀ n, n < k → K.ExactAt n) (n : ℕ) :
    Injective ((K.truncGE' (degreeShiftEmbedding k)).X n) := by
  by_cases hn : (degreeShiftEmbedding k).BoundaryGE n
  · have hn0 : n = 0 := by
      cases n with
      | zero => rfl
      | succ n => exact False.elim ((degreeShiftEmbedding k).not_boundaryGE_next
          (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl) hn)
    subst n
    haveI := injective_opcycles_of_exact_below K k he k le_rfl
    exact Injective.of_iso
      (K.truncGE'XIsoOpcycles (degreeShiftEmbedding k) (i' := k) rfl hn).symm
      inferInstance
  · exact Injective.of_iso
      (K.truncGE'XIso (degreeShiftEmbedding k) rfl hn).symm inferInstance

section AdditiveFunctor

variable {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- A good truncation below which the original injective complex is exact
remains a quasi-isomorphism after an arbitrary additive functor. -/
lemma map_goodTruncation_quasiIso (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (k : ℕ)
    (he : ∀ n, n < k → K.ExactAt n) :
    QuasiIso ((G.mapHomologicalComplex _).map (HomologicalComplex.πTruncGE K (degreeShiftEmbedding k))) := by
  haveI : ∀ n, Injective ((K.truncGE' (degreeShiftEmbedding k)).X n) :=
    injective_goodShift K k he
  haveI : ∀ n, Injective ((HomologicalComplex.truncGE K (degreeShiftEmbedding k)).X n) :=
    fun n => inferInstanceAs
      (Injective (((K.truncGE' (degreeShiftEmbedding k)).extend (degreeShiftEmbedding k)).X n))
  exact homotopyEquivalences_le_quasiIso _ _ _
    (G.homotopyEquivalences_mapHomologicalComplex_map _
      ((CochainComplex.quasiIso_iff_of_injective _).mp
        (goodTruncation_quasiIso K k he)))

/-- Cohomology after mapping an injective complex may be computed from
the good shift whenever the removed lower cohomology vanishes. -/
def mapGoodShiftHomologyIso (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (k : ℕ)
    (he : ∀ n, n < k → K.ExactAt n) (n : ℕ) :
    ((G.mapHomologicalComplex _).obj K).homology (k + n) ≅
      ((G.mapHomologicalComplex _).obj
        (K.truncGE' (degreeShiftEmbedding k))).homology n := by
  let e := degreeShiftEmbedding k
  let L := K.truncGE' e
  haveI := map_goodTruncation_quasiIso G K k he
  exact isoOfQuasiIsoAt ((G.mapHomologicalComplex _).map (HomologicalComplex.πTruncGE K e)) (k + n) ≪≫
    (homologyFunctor D _ (k + n)).mapIso (mapExtendIso G e L) ≪≫
      ((G.mapHomologicalComplex _).obj L).extendHomologyIso e (j := n) (j' := k + n) rfl

end AdditiveFunctor

/-- A complex of injectives concentrated in one cohomological degree,
after its canonical good shift, is an injective resolution of that actual
cohomology object. -/
def concentratedResolution (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (k : ℕ)
    (he : ∀ n, n ≠ k → K.ExactAt n) : InjectiveResolution (K.homology k) := by
  let L := K.truncGE' (degreeShiftEmbedding k)
  have hbelow : ∀ n, n < k → K.ExactAt n := fun n hn => he n (Nat.ne_of_lt hn)
  haveI : ∀ n, Injective (L.X n) := injective_goodShift K k hbelow
  have hL : ∀ n, L.ExactAt (n + 1) := by
    intro n
    rw [exactAt_iff_isZero_homology]
    exact (he (k + (n + 1)) (by omega)).isZero_homology.of_iso
      (goodShiftHomologyIso K k (n + 1))
  let I := cyclesResolution L hL
  let e : L.cycles 0 ≅ K.homology k :=
    CochainComplex.isoHomologyπ₀ L ≪≫ goodShiftHomologyIso K k 0
  exact
    { cocomplex := L
      ι := (CochainComplex.single₀ C).map e.inv ≫ I.ι
      quasiIso := by infer_instance }

section DerivedFunctor

variable [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- The homology of an additive functor applied to a concentrated
injective complex is the corresponding right derived functor of its sole
cohomology object, with the required shift. -/
def concentratedCohomologyIso (K : CochainComplex C ℕ)
    [∀ n, Injective (K.X n)] (k : ℕ)
    (he : ∀ n, n ≠ k → K.ExactAt n) (n : ℕ) :
    ((G.mapHomologicalComplex _).obj K).homology (k + n) ≅
      (G.rightDerived n).obj (K.homology k) :=
  mapGoodShiftHomologyIso G K k (fun q hq => he q (Nat.ne_of_lt hq)) n ≪≫
    ((concentratedResolution K k he).isoRightDerivedObj G n).symm

end DerivedFunctor

section Composition

variable [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D] [HasInjectiveResolutions D]
  {E : Type*} [Category* E] [Abelian E]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects]
  (G : D ⥤ E) [G.Additive]

/-- Single-degree Leray concentration, proved from actual injective
resolutions. In the projective-line application, `k` is zero or one and
the concentration hypothesis is supplied by the geometric Čech theorem. -/
def compositionConcentratedIso (X : C) (k : ℕ)
    (hX : ∀ q, q ≠ k → IsZero ((F.rightDerived q).obj X)) (n : ℕ) :
    ((F ⋙ G).rightDerived (k + n)).obj X ≅
      (G.rightDerived n).obj ((F.rightDerived k).obj X) := by
  let I := injectiveResolution X
  let K := (F.mapHomologicalComplex _).obj I.cocomplex
  haveI : ∀ q, Injective (K.X q) := fun q =>
    Functor.PreservesInjectiveObjects.injective_obj (I.injective q)
  have he : ∀ q, q ≠ k → K.ExactAt q := by
    intro q hq
    rw [exactAt_iff_isZero_homology]
    exact (hX q hq).of_iso (I.isoRightDerivedObj F q).symm
  exact I.isoRightDerivedObj (F ⋙ G) (k + n) ≪≫
    concentratedCohomologyIso G K k he n ≪≫
      (G.rightDerived n).mapIso (I.isoRightDerivedObj F k).symm

end Composition

end PaperVerification.DerivedConcentration
