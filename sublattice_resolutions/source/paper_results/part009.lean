module
public import graph_foundation.part012
public import shared_results.part010
public import paper_results.part008

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceJoinContraction -/
section

/-! # The vertical incidence-cover contraction in the original variables

The target is the actual submodule of the coefficient ring equal to the
whole ring on nerve faces and zero otherwise. Its inclusion into the ring
is therefore a common ambient projection on every cover intersection.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.IncidenceJoin
open Classical CommAlg CommAlg.Simplicial HomologicalPerturbation
universe u
variable {L R k : Type u} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  [CommRing k] {M : ℕ} (left : Fin M → L) (right : Fin M → R)

abbrev V := FiniteVariable.{u} (IncidenceRows M)

def rowSupport (p : Fin (Fintype.card L)) (v : V (M := M)) : Prop :=
  Fintype.equivFin L (left v.1)=p ∧ v.2.down≠2

def zeroBlock (p : Fin (Fintype.card L)) : Finset (V (M := M)) :=
  incidenceZeroBlock left ((Fintype.equivFin L).symm p)

def oneBlock (Q : Finset R) (p : Fin (Fintype.card L)) : Finset (V (M := M)) :=
  incidenceOneBlock left right Q ((Fintype.equivFin L).symm p)

theorem support_disjoint (p q : Fin (Fintype.card L)) (hpq : p≠q)
    (v : V (M := M)) (hp : rowSupport left p v) : ¬rowSupport left q v :=
  fun hq => hpq (hp.1.symm.trans hq.1)

theorem zero_supported (p : Fin (Fintype.card L)) (v : V (M := M))
    (hv : v∈zeroBlock left p) : rowSupport left p v := by
  obtain ⟨hleft,hlevel⟩ := (Finset.mem_filter.mp hv).2
  exact ⟨by simpa only [hleft,Equiv.apply_symm_apply],
    by simpa only [hlevel] using (by decide : (0 : Fin 3) ≠ 2)⟩

theorem one_supported (Q : Finset R) (p : Fin (Fintype.card L)) (v : V (M := M))
    (hv : v∈oneBlock left right Q p) : rowSupport left p v := by
  obtain ⟨hleft,hlevel,hQ⟩ := (Finset.mem_filter.mp hv).2
  exact ⟨by simpa only [hleft,Equiv.apply_symm_apply],
    by simpa only [hlevel] using (by decide : (1 : Fin 3) ≠ 2)⟩

theorem zero_one_disjoint (Q : Finset R) (p : Fin (Fintype.card L)) :
    Disjoint (zeroBlock left p) (oneBlock left right Q p) :=
  incidenceZeroOne_disjoint left right Q ((Fintype.equivFin L).symm p)

private theorem level_zero_or_one (v : V (M := M)) (hv : v.2.down≠2) :
    v.2.down=0 ∨ v.2.down=1 := by
  have hlt : v.2.down.val < 3 := v.2.down.isLt
  have hne : v.2.down.val ≠ 2 := fun h => hv (Fin.ext h)
  have h : v.2.down.val = 0 ∨ v.2.down.val = 1 := by omega
  rcases h with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

private theorem variable_eq_level (v : V (M := M)) (j : Fin 3)
    (h : v.2.down = j) : v = ⟨v.1,ULift.up j⟩ := by
  rcases v with ⟨e,⟨a⟩⟩
  change a = j at h
  subst a
  rfl

/-- Literal equality of the incidence intersection with its disjoint-row
join, including all omitted one-level vertices. -/
theorem faces_iff (Q : Finset R) (F : Finset (V (M := M))) :
    JoinedTwoSimplex.Faces (rowSupport left) (zeroBlock left) (oneBlock left right Q) F ↔
      incidenceRowIntersectionFaces left right Q F := by
  constructor
  · rintro ⟨hcover,hrows⟩
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro v hv
      obtain ⟨p,hp⟩ := hcover v hv
      exact (incidenceLowerSupport_mem v).mpr hp.2
    · intro e f hef he hf
      let p := Fintype.equivFin L (left e)
      have hze : (⟨e,ULift.up 0⟩ : V (M := M))∈F.filter (rowSupport left p) := by
        exact Finset.mem_filter.mpr ⟨he,rfl,(by decide : (0 : Fin 3) ≠ 2)⟩
      have hxf : (⟨f,ULift.up 1⟩ : V (M := M))∈F.filter (rowSupport left p) := by
        exact Finset.mem_filter.mpr ⟨hf,by simp only [p,hef],(by decide : (1 : Fin 3) ≠ 2)⟩
      rcases hrows p with hz | hx
      · have hh := (Finset.mem_filter.mp (hz hxf)).2.2
        exact (by decide : (1 : Fin 3)≠0) hh
      · have hh := (Finset.mem_filter.mp (hx hze)).2.2.1
        exact (by decide : (0 : Fin 3)≠1) hh
    · intro e heQ heF
      let p := Fintype.equivFin L (left e)
      have hxe : (⟨e,ULift.up 1⟩ : V (M := M))∈F.filter (rowSupport left p) :=
        Finset.mem_filter.mpr ⟨heF,rfl,(by decide : (1 : Fin 3) ≠ 2)⟩
      rcases hrows p with hz | hx
      · exact (by decide : (1 : Fin 3)≠0) (Finset.mem_filter.mp (hz hxe)).2.2
      · exact (Finset.mem_filter.mp (hx hxe)).2.2.2 heQ
  · rintro ⟨⟨hF,hsep⟩,hQ⟩
    refine ⟨fun v hv => ⟨Fintype.equivFin L (left v.1),rfl,
      (incidenceLowerSupport_mem v).mp (hF hv)⟩,?_⟩
    intro p
    by_cases hz : ∃e : Fin M,Fintype.equivFin L (left e)=p ∧
        (⟨e,ULift.up 0⟩ : V (M := M))∈F
    · left
      intro v hv
      obtain ⟨hvF,hvp,hvlow⟩ := Finset.mem_filter.mp hv
      obtain ⟨e,hep,heF⟩ := hz
      have hleft : left v.1=(Fintype.equivFin L).symm p := by
        apply (Fintype.equivFin L).injective
        simpa only [Equiv.apply_symm_apply] using hvp
      have h0 : v.2.down=0 := by
        rcases level_zero_or_one v hvlow with h0 | h1
        · exact h0
        · have heq : left e=left v.1 := (Fintype.equivFin L).injective (hep.trans hvp.symm)
          have hv1 : (⟨v.1,ULift.up 1⟩ : V (M := M))∈F := by
            have hvEq : v=⟨v.1,ULift.up 1⟩ := variable_eq_level v 1 h1
            simpa only [hvEq] using hvF
          exact (hsep e v.1 heq heF hv1).elim
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hleft,h0⟩
    · right
      intro v hv
      obtain ⟨hvF,hvp,hvlow⟩ := Finset.mem_filter.mp hv
      have hleft : left v.1=(Fintype.equivFin L).symm p := by
        apply (Fintype.equivFin L).injective
        simpa only [Equiv.apply_symm_apply] using hvp
      have h1 : v.2.down=1 := by
        rcases level_zero_or_one v hvlow with h0 | h1
        · apply False.elim
          apply hz
          refine ⟨v.1,hvp,?_⟩
          have hvEq : v=⟨v.1,ULift.up 0⟩ := variable_eq_level v 0 h0
          simpa only [hvEq] using hvF
        · exact h1
      have hv1 : (⟨v.1,ULift.up 1⟩ : V (M := M))∈F := by
        have hvEq : v=⟨v.1,ULift.up 1⟩ := variable_eq_level v 1 h1
        simpa only [hvEq] using hvF
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hleft,h1,fun hr => hQ v.1 hr hv1⟩

def sourceEquiv (Q : Finset R) :
    TotalFaceModule (k := k) (JoinedTwoSimplex.Faces (rowSupport left)
      (zeroBlock left) (oneBlock left right Q)) ≃ₗ[k]
        TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q) :=
  LinearEquiv.ofEq _ _ (congrArg (TotalFaceModule (k := k))
    (funext fun F => propext (faces_iff left right Q F)))

theorem sourceEquiv_piece (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k := k) (JoinedTwoSimplex.Faces (rowSupport left)
      (zeroBlock left) (oneBlock left right Q))) :
    x∈totalFacePiece (JoinedTwoSimplex.Faces (rowSupport left)
      (zeroBlock left) (oneBlock left right Q)) j ↔
      sourceEquiv left right Q x∈totalFacePiece (incidenceRowIntersectionFaces left right Q) j := by
  change x.val∈Chains _ j ↔ (sourceEquiv left right Q x).val∈Chains _ j
  simp only [sourceEquiv,LinearEquiv.coe_ofEq_apply]
  generalize x.val = z
  rw [show JoinedTwoSimplex.Faces (rowSupport left) (zeroBlock left)
    (oneBlock left right Q)=incidenceRowIntersectionFaces left right Q from
      funext fun F => propext (faces_iff left right Q F)]

theorem sourceEquiv_symm_piece (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q))
    (hx : x∈totalFacePiece (incidenceRowIntersectionFaces left right Q) j) :
    (sourceEquiv left right Q).symm x∈totalFacePiece
      (JoinedTwoSimplex.Faces (rowSupport left) (zeroBlock left) (oneBlock left right Q)) j :=
  (sourceEquiv_piece (k := k) left right Q j _).mpr
    (by simpa only [LinearEquiv.apply_symm_apply] using hx)

theorem downward (Q : Finset R) : Downward (incidenceRowIntersectionFaces left right Q) := by
  intro F H hHF hF
  exact (faces_iff left right Q H).mp
    (JoinedTwoSimplex.downward _ _ _ hHF ((faces_iff left right Q F).mpr hF))

def omitted (r : R) : Finset (V (M := M)) :=
  Finset.univ.filter fun v => v.2.down=1 ∧ right v.1=r

theorem cech_intersection_iff (Q : Finset R) (F : Finset (V (M := M))) :
    CechFace.intersectionFaces (incidenceRowJoinFaces left) (omitted right) Q F ↔
      incidenceRowIntersectionFaces left right Q F := by
  constructor
  · rintro ⟨hB,hQ⟩
    refine ⟨hB,fun e he heF => ?_⟩
    exact Finset.disjoint_left.mp (hQ (right e) he) heF (by simp [omitted])
  · rintro ⟨hB,hQ⟩
    refine ⟨hB,fun r hr => Finset.disjoint_left.mpr ?_⟩
    intro v hvF hvU
    obtain ⟨hlevel,hright⟩ := (Finset.mem_filter.mp hvU).2
    have hvEq : v=⟨v.1,ULift.up 1⟩ := variable_eq_level v 1 hlevel
    exact hQ v.1 (hright ▸ hr) (by simpa only [hvEq] using hvF)

theorem nerve_iff_nonempty (Q : Finset R) :
    incidenceNerveFaces left right Q ↔ ∀p,(oneBlock left right Q p).Nonempty := by
  constructor
  · intro h p
    exact (incidenceOneBlock_nonempty_iff left right Q _).mpr (h _)
  · intro h a
    simpa only [oneBlock,Equiv.symm_apply_apply] using
      (incidenceOneBlock_nonempty_iff left right Q _).mp (h (Fintype.equivFin L a))

def nerveLine (Q : Finset R) : Submodule k k :=
  if incidenceNerveFaces left right Q then ⊤ else ⊥

def lineEquiv (Q : Finset R) (hQ : incidenceNerveFaces left right Q) :
    nerveLine (k := k) left right Q ≃ₗ[k] k :=
  (LinearEquiv.ofEq _ _ (if_pos hQ)).trans Submodule.topEquiv

def verticalProjection (Q : Finset R) :
    TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q) →ₗ[k] k :=
  (JoinedTwoSimplex.projection (rowSupport left) (zeroBlock left) (oneBlock left right Q)
    (support_disjoint left) (zero_supported left) (one_supported left right Q)).comp
      (sourceEquiv left right Q).symm.toLinearMap

variable (hl : Function.Surjective left)

def zeroVertex (p : Fin (Fintype.card L)) : V (M := M) :=
  (incidenceZeroBlock_nonempty left hl ((Fintype.equivFin L).symm p)).choose

theorem zeroVertex_mem (p : Fin (Fintype.card L)) : zeroVertex left hl p∈zeroBlock left p :=
  (incidenceZeroBlock_nonempty left hl ((Fintype.equivFin L).symm p)).choose_spec

/-- Every incidence intersection is strongly contracted to its literal
nerve coefficient line over any commutative coefficient ring. -/
def contraction (Q : Finset R) : LinearContraction (R := k)
    (M := TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q))
    (H := nerveLine (k := k) left right Q) := by
  by_cases hQ : incidenceNerveFaces left right Q
  · let hn := (nerve_iff_nonempty left right Q).mp hQ
    let e := fun p => (hn p).choose
    let C := JoinedTwoSimplex.contraction (k := k) (rowSupport left) (zeroBlock left)
      (oneBlock left right Q) (support_disjoint left) (zero_supported left)
      (one_supported left right Q) (zero_one_disjoint left right Q)
      (zeroVertex left hl) e (zeroVertex_mem left hl) (fun p => (hn p).choose_spec)
    exact (C.changeTarget (lineEquiv left right Q hQ).symm).changeSource (sourceEquiv left right Q)
  · have hn : ¬∀p,(oneBlock left right Q p).Nonempty :=
      fun h => hQ ((nerve_iff_nonempty left right Q).mpr h)
    let a := Classical.choose (not_forall.mp hn)
    have ha : oneBlock left right Q a=∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (Classical.choose_spec (not_forall.mp hn))
    let C := JoinedTwoSimplex.zeroContraction (k := k) (rowSupport left) (zeroBlock left)
      (oneBlock left right Q) (support_disjoint left) (zero_supported left)
      a ha (zeroVertex left hl a) (zeroVertex_mem left hl a)
    let e : (⊥ : Submodule k k) ≃ₗ[k] nerveLine left right Q :=
      LinearEquiv.ofEq _ _ (by simp only [nerveLine,if_neg hQ])
    exact (C.changeTarget e).changeSource (sourceEquiv left right Q)

theorem contraction_d (Q : Finset R) :
    (contraction (k := k) left right hl Q).d=idealTotalDifferential (downward left right Q) := by
  unfold contraction
  split_ifs with hQ
  all_goals
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearContraction.changeSource,LinearContraction.changeTarget,
      LinearMap.comp_apply,LinearEquiv.coe_coe,JoinedTwoSimplex.contraction_d,
      JoinedTwoSimplex.zeroContraction_d,idealTotalDifferential_val,
      sourceEquiv,LinearEquiv.coe_ofEq_apply,LinearEquiv.ofEq_symm]

theorem contraction_projection_val (Q : Finset R)
    (x : TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q)) :
    ((contraction left right hl Q).projection x).val=verticalProjection left right Q x := by
  unfold contraction
  split_ifs with hQ
  · rfl
  · dsimp [LinearContraction.changeSource,LinearContraction.changeTarget]
    change 0=JoinedTwoSimplex.projection (rowSupport left) (zeroBlock left)
      (oneBlock left right Q) (support_disjoint left) (zero_supported left)
      (one_supported left right Q) ((sourceEquiv left right Q).symm x)
    have hn : ¬∀p,(oneBlock left right Q p).Nonempty :=
      fun h => hQ ((nerve_iff_nonempty left right Q).mpr h)
    obtain ⟨a,ha⟩ := not_forall.mp hn
    rw [JoinedTwoSimplex.projection_zero_of_empty _ _ _ _ _ _ a
      (Finset.not_nonempty_iff_eq_empty.mp ha)]
    rfl

def intersectionInclusion (P Q : Finset R) (hPQ : P⊆Q) :
    TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q) →ₗ[k]
      TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right P) :=
  Submodule.inclusion (Submodule.span_le.mpr (by
    rintro x ⟨F,hF,rfl⟩
    exact Submodule.subset_span ⟨F,⟨hF.1,fun e he => hF.2 e (hPQ he)⟩,rfl⟩))

theorem oneBlock_antitone (P Q : Finset R) (hPQ : P⊆Q) (p : Fin (Fintype.card L)) :
    oneBlock left right Q p⊆oneBlock left right P p := by
  intro v hv
  obtain ⟨hl,hlevel,hQ⟩ := (Finset.mem_filter.mp hv).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl,hlevel,fun hP => hQ (hPQ hP)⟩

theorem verticalProjection_natural (P Q : Finset R) (hPQ : P⊆Q)
    (x : TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q)) :
    verticalProjection left right P (intersectionInclusion left right P Q hPQ x)=
      verticalProjection left right Q x := by
  have h := LinearMap.congr_fun (JoinedTwoSimplex.projection_natural (k := k)
    (rowSupport left) (zeroBlock left) (oneBlock left right Q) (oneBlock left right P)
    (support_disjoint left) (zero_supported left) (one_supported left right Q)
    (one_supported left right P) (oneBlock_antitone left right P Q hPQ)
    (zero_one_disjoint left right P)) ((sourceEquiv left right Q).symm x)
  have hxy : (sourceEquiv left right P).symm (intersectionInclusion left right P Q hPQ x)=
      JoinedTwoSimplex.inclusion (rowSupport left) (zeroBlock left)
        (oneBlock left right Q) (oneBlock left right P) (oneBlock_antitone left right P Q hPQ)
          ((sourceEquiv left right Q).symm x) := by
    apply Subtype.ext
    rfl
  change JoinedTwoSimplex.projection (k := k) (rowSupport left) (zeroBlock left)
    (oneBlock left right P) (support_disjoint left) (zero_supported left)
    (one_supported left right P)
    ((sourceEquiv left right P).symm (intersectionInclusion left right P Q hPQ x)) = _
  rw [hxy]
  exact h

theorem projection_zero_off_degree (Q : Finset R) (j : ℕ) (hj : j≠Fintype.card L)
    (x : TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q))
    (hx : x∈totalFacePiece (incidenceRowIntersectionFaces left right Q) j) :
    (contraction left right hl Q).projection x=0 := by
  apply Subtype.ext
  rw [contraction_projection_val]
  exact JoinedTwoSimplex.projection_zero_off_degree (rowSupport left) (zeroBlock left)
    (oneBlock left right Q) (support_disjoint left) (zero_supported left)
    (one_supported left right Q) j hj _ (sourceEquiv_symm_piece (k := k) left right Q j x hx)

theorem homotopy_raises (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q))
    (hx : x∈totalFacePiece (incidenceRowIntersectionFaces left right Q) j) :
    (contraction left right hl Q).h x∈totalFacePiece (incidenceRowIntersectionFaces left right Q) (j+1) := by
  unfold contraction
  split_ifs with hQ
  · exact (sourceEquiv_piece (k := k) left right Q _ _).mp
      (JoinedTwoSimplex.homotopy_raises (rowSupport left) (zeroBlock left)
        (oneBlock left right Q) (support_disjoint left) (zero_supported left)
        (one_supported left right Q) (zero_one_disjoint left right Q)
        (zeroVertex left hl) _ (zeroVertex_mem left hl) _ j _
          (sourceEquiv_symm_piece (k := k) left right Q j x hx))
  · have hn : ¬∀p,(oneBlock left right Q p).Nonempty :=
      fun h => hQ ((nerve_iff_nonempty left right Q).mpr h)
    let a := Classical.choose (not_forall.mp hn)
    have ha : oneBlock left right Q a=∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (Classical.choose_spec (not_forall.mp hn))
    apply (sourceEquiv_piece (k := k) left right Q _ _).mp
    apply creation_mem_of_cone
    · intro s hs
      exact JoinedTwoSimplex.insert_vertex (rowSupport left) (zeroBlock left)
        (oneBlock left right Q) (support_disjoint left) (zero_supported left)
        a ha (zeroVertex left hl a) (zeroVertex_mem left hl a) hs
    · exact sourceEquiv_symm_piece (k := k) left right Q j x hx

theorem inclusion_degree (Q : Finset R) (r : nerveLine (k := k) left right Q) :
    (contraction left right hl Q).inclusion r∈
      totalFacePiece (incidenceRowIntersectionFaces left right Q) (Fintype.card L) := by
  unfold contraction
  split_ifs with hQ
  · exact (sourceEquiv_piece (k := k) left right Q _ _).mp
      (JoinedTwoSimplex.inclusion_degree (rowSupport left) (zeroBlock left)
        (oneBlock left right Q) (support_disjoint left) (zero_supported left)
        (one_supported left right Q) (zero_one_disjoint left right Q)
        (zeroVertex left hl) _ (zeroVertex_mem left hl) _ _)
  · change sourceEquiv (k := k) left right Q 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _

end FourPapers.Sublattice.IncidenceJoin
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceCechVertical -/
section

/-! # The expanded incidence Čech complex retracts onto the actual nerve -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice

/-- The incidence nerve is downward closed without an order on the auxiliary
sum of left vertices and incidences. This proof leaves every simplicial
chain orientation unchanged. -/
theorem incidenceRowNerve_downward
    {L R T : Type*} [Fintype L] [Fintype R] [Fintype T]
    [DecidableEq L] [DecidableEq R] (left : T → L) (right : T → R) :
    CommAlg.Simplicial.Downward (incidenceNerveFaces left right) := by
  intro Q P hPQ hQ a
  obtain ⟨t,ht,htr⟩ := hQ a
  exact ⟨t,ht,fun hp => htr (hPQ hp)⟩

end FourPapers.Sublattice

namespace FourPapers.Sublattice.IncidenceJoin
open Classical CommAlg CommAlg.Simplicial HomologicalPerturbation
universe u
variable {L R k : Type u} [Fintype L] [Fintype R] [DecidableEq L] [LinearOrder R]
  [CommRing k] {M : ℕ} (left : Fin M → L) (right : Fin M → R)
  (hl : Function.Surjective left)

theorem join_downward : Downward (incidenceRowJoinFaces left) := by
  intro F H hHF hF
  exact ⟨hHF.trans hF.1,fun e f hef he hf => hF.2 e f hef (hHF he) (hHF hf)⟩

def cechSourceEquiv (Q : Finset R) :
    TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q) ≃ₗ[k]
      TotalFaceModule (k := k) (CechFace.intersectionFaces
        (incidenceRowJoinFaces left) (omitted right) Q) :=
  LinearEquiv.ofEq _ _ (congrArg (TotalFaceModule (k := k))
    (funext fun F => propext (cech_intersection_iff left right Q F).symm))

theorem cechSourceEquiv_piece (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k := k) (incidenceRowIntersectionFaces left right Q)) :
    x∈totalFacePiece (incidenceRowIntersectionFaces left right Q) j ↔
      cechSourceEquiv left right Q x∈totalFacePiece
        (CechFace.intersectionFaces (incidenceRowJoinFaces left) (omitted right) Q) j := by
  change x.val∈Chains _ j ↔ (cechSourceEquiv left right Q x).val∈Chains _ j
  simp only [cechSourceEquiv,LinearEquiv.coe_ofEq_apply]
  generalize x.val = z
  rw [show CechFace.intersectionFaces (incidenceRowJoinFaces left) (omitted right) Q=
      incidenceRowIntersectionFaces left right Q from
    funext fun F => propext (cech_intersection_iff left right Q F)]

theorem cechSourceEquiv_symm_piece (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k := k) (CechFace.intersectionFaces
      (incidenceRowJoinFaces left) (omitted right) Q))
    (hx : x∈totalFacePiece (CechFace.intersectionFaces
      (incidenceRowJoinFaces left) (omitted right) Q) j) :
    (cechSourceEquiv left right Q).symm x∈totalFacePiece (incidenceRowIntersectionFaces left right Q) j :=
  (cechSourceEquiv_piece (k := k) left right Q j _).mpr
    (by simpa only [LinearEquiv.apply_symm_apply] using hx)

def cechContraction (Q : Finset R) : LinearContraction (R := k)
    (M := TotalFaceModule (k := k) (CechFace.intersectionFaces
      (incidenceRowJoinFaces left) (omitted right) Q))
    (H := CoefficientLineSum.line (k := k) (incidenceNerveFaces left right) Q) :=
  (contraction left right hl Q).changeSource (cechSourceEquiv left right Q)

theorem cechContraction_d (Q : Finset R) :
    (cechContraction (k := k) left right hl Q).d=idealTotalDifferential
      (CechFace.intersectionFaces_downward (incidenceRowJoinFaces left) (omitted right)
        (join_downward left) Q) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((cechSourceEquiv left right Q)
    ((contraction left right hl Q).d ((cechSourceEquiv left right Q).symm x))).val=_
  rw [contraction_d]
  rfl

theorem cechProjection_natural (P Q : Finset R) (hPQ : P⊆Q)
    (x : TotalFaceModule (k := k) (CechFace.intersectionFaces
      (incidenceRowJoinFaces left) (omitted right) Q)) :
    ((cechContraction left right hl P).projection
      (CechFace.NerveReduction.intersectionInclusion (incidenceRowJoinFaces left)
        (omitted right) P Q hPQ x)).val=
      ((cechContraction left right hl Q).projection x).val := by
  change ((contraction left right hl P).projection
    (intersectionInclusion left right P Q hPQ ((cechSourceEquiv left right Q).symm x))).val=
      ((contraction left right hl Q).projection ((cechSourceEquiv left right Q).symm x)).val
  rw [contraction_projection_val,contraction_projection_val]
  exact verticalProjection_natural left right P Q hPQ ((cechSourceEquiv left right Q).symm x)

theorem cechHomotopy_raises (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k := k) (CechFace.intersectionFaces
      (incidenceRowJoinFaces left) (omitted right) Q))
    (hx : x∈totalFacePiece _ j) :
    (cechContraction left right hl Q).h x∈totalFacePiece _ (j+1) := by
  apply (cechSourceEquiv_piece (k := k) left right Q (j+1) _).mp
  exact homotopy_raises left right hl Q j _
    (cechSourceEquiv_symm_piece (k := k) left right Q j x hx)

theorem cechInclusion_degree (Q : Finset R)
    (r : CoefficientLineSum.line (k := k) (incidenceNerveFaces left right) Q) :
    (cechContraction left right hl Q).inclusion r∈totalFacePiece _ (Fintype.card L) := by
  apply (cechSourceEquiv_piece (k := k) left right Q (Fintype.card L) _).mp
  exact inclusion_degree left right hl Q r

theorem cechProjection_zero_off_degree (Q : Finset R) (j : ℕ) (hj : j≠Fintype.card L)
    (x : TotalFaceModule (k := k) (CechFace.intersectionFaces
      (incidenceRowJoinFaces left) (omitted right) Q)) (hx : x∈totalFacePiece _ j) :
    (cechContraction left right hl Q).projection x=0 := by
  exact projection_zero_off_degree left right hl Q j hj _
    (cechSourceEquiv_symm_piece (k := k) left right Q j x hx)

def cechDeformation : LinearDeformationRetract (R := k)
    (M := CechFace.totalModule (k := k) (incidenceRowJoinFaces left) (omitted right))
    (H := TotalFaceModule (k := k) (incidenceNerveFaces left right)) :=
  CechFace.NerveReduction.totalDeformation (incidenceRowJoinFaces left) (omitted right)
    (incidenceNerveFaces left right) (cechContraction left right hl)
    (join_downward left) (cechContraction_d left right hl)

theorem cechDeformation_target :
    (cechDeformation (k := k) left right hl).targetD=
      idealTotalDifferential (incidenceRowNerve_downward left right) :=
  CechFace.NerveReduction.totalDeformation_target (incidenceRowJoinFaces left) (omitted right)
    (incidenceNerveFaces left right) (cechContraction left right hl) (join_downward left)
    (incidenceRowNerve_downward left right) (cechContraction_d left right hl)
    (cechProjection_natural left right hl)

theorem cechDeformation_source :
    (cechDeformation (k := k) left right hl).sourceD=
      CechFace.horizontal (incidenceRowJoinFaces left) (omitted right)+
        CechFace.vertical (incidenceRowJoinFaces left) (omitted right) (join_downward left) :=
  CechFace.NerveReduction.totalDeformation_source (incidenceRowJoinFaces left) (omitted right)
    (incidenceNerveFaces left right) (cechContraction left right hl) (join_downward left)
    (cechContraction_d left right hl)

end FourPapers.Sublattice.IncidenceJoin
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteComplexIncidence -/
section

/-! # The exact incidence construction for every finite complex

Minimal nonfaces are taken from the actual downward-closed face predicate.
Every original vertex occurs in one of them precisely when it is not a
cone vertex. The resulting incidence nerve is proved equal to the given
complex, and the coordinate count is the sum of minimal-nonface sizes.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.FiniteComplexIncidence
open Classical CommAlg
universe u
variable {R : Type u} [Fintype R] [LinearOrder R] (K : Finset R → Prop)

def MinimalNonface (F : Finset R) : Prop := ¬K F ∧ ∀G : Finset R,G⊂F → K G

theorem exists_minimal_nonface (F : Finset R) :
    ¬K F → ∃N : Finset R,N⊆F ∧ MinimalNonface K N := by
  induction F using Finset.strongInductionOn with
  | _ F ih =>
      intro hF
      by_cases hm : ∀G : Finset R,G⊂F → K G
      · exact ⟨F,Finset.Subset.refl _,hF,hm⟩
      · push_neg at hm
        obtain ⟨G,hGF,hG⟩ := hm
        obtain ⟨N,hNG,hN⟩ := ih G hGF hG
        exact ⟨N,hNG.trans hGF.1,hN⟩

theorem face_iff_avoids_minimal (hK : Simplicial.Downward K) (F : Finset R) :
    K F ↔ ∀N : Finset R,MinimalNonface K N → ¬N⊆F := by
  constructor
  · intro hF N hN hNF
    exact hN.1 (hK hNF hF)
  · intro h
    by_contra hF
    obtain ⟨N,hNF,hN⟩ := exists_minimal_nonface K F hF
    exact h N hN hNF

abbrev Nonfaces := {F : Finset R // MinimalNonface K F}
abbrev Edges := Σ F : Nonfaces K,{r : R // r∈F.val}

def rowCount : ℕ := Fintype.card (Edges K)

def left (e : Fin (rowCount K)) : Nonfaces K := ((Fintype.equivFin (Edges K)).symm e).1
def right (e : Fin (rowCount K)) : R := ((Fintype.equivFin (Edges K)).symm e).2.val

theorem right_enumerate (e : Edges K) :
    right K ((Fintype.equivFin (Edges K)) e) = e.2.val := by
  change (((Fintype.equivFin (Edges K)).symm
    ((Fintype.equivFin (Edges K)) e)).2.val) = _
  exact congrArg (fun z : Edges K => z.2.val)
    ((Fintype.equivFin (Edges K)).symm_apply_apply e)

theorem minimal_nonempty (hEmpty : K ∅) (F : Nonfaces K) : F.val.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hF
  exact F.property.1 (by simpa only [hF] using hEmpty)

theorem left_surjective (hEmpty : K ∅) : Function.Surjective (left K) := by
  intro F
  obtain ⟨r,hr⟩ := minimal_nonempty K hEmpty F
  refine ⟨Fintype.equivFin (Edges K) ⟨F,r,hr⟩,?_⟩
  simp only [left,Equiv.symm_apply_apply]

/-- The no-cone-vertex hypothesis is stated in its literal face form. -/
def NoConeVertices : Prop := ∀r : R,∃F : Finset R,K F ∧ ¬K (insert r F)

theorem right_surjective (hK : Simplicial.Downward K) (hnc : NoConeVertices K) :
    Function.Surjective (right K) := by
  intro r
  obtain ⟨F,hF,hbad⟩ := hnc r
  obtain ⟨N,hNsub,hN⟩ := exists_minimal_nonface K (insert r F) hbad
  have hr : r∈N := by
    by_contra hr
    have hNF : N⊆F := by
      intro s hs
      rcases Finset.mem_insert.mp (hNsub hs) with hsr | hsF
      · exact False.elim (hr (hsr ▸ hs))
      · exact hsF
    exact hN.1 (hK hNF hF)
  refine ⟨Fintype.equivFin (Edges K) ⟨⟨N,hN⟩,r,hr⟩,?_⟩
  exact right_enumerate K ⟨⟨N,hN⟩,r,hr⟩

theorem rowCount_eq_sum : rowCount K=∑F : Nonfaces K,F.val.card := by
  rw [rowCount,Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun F _ => Fintype.card_coe _)

/-- There is no realization assumption in this identification: the
incidence condition is exactly avoidance of the minimal nonfaces. -/
theorem nerve_iff_face (hK : Simplicial.Downward K) (Q : Finset R) :
    incidenceNerveFaces (left K) (right K) Q ↔ K Q := by
  rw [face_iff_avoids_minimal K hK Q]
  constructor
  · intro h N hN hNQ
    obtain ⟨e,he,heQ⟩ := h ⟨N,hN⟩
    apply heQ
    have hmem : right K e∈(left K e).val := ((Fintype.equivFin (Edges K)).symm e).2.property
    exact hNQ (by simpa only [he] using hmem)
  · intro h F
    have hn : ¬F.val⊆Q := h F.val F.property
    obtain ⟨r,hrN,hrQ⟩ := Finset.not_subset.mp hn
    refine ⟨Fintype.equivFin (Edges K) ⟨F,r,hrN⟩,?_,?_⟩
    · simp only [left,Equiv.symm_apply_apply]
    · rw [right_enumerate]
      exact hrQ

def lattice : Finset (FiniteTuple (IncidenceRows (rowCount K))) :=
  incidenceSublattice (left K) (right K)

theorem lattice_closed : finiteLatticeClosed (IncidenceRows (rowCount K)) (lattice K) :=
  incidenceSublattice_closed (left K) (right K)

theorem lattice_card (hK : Simplicial.Downward K) (hEmpty : K ∅) (hnc : NoConeVertices K) :
    (lattice K).card=2^(Fintype.card (Nonfaces K))+2^(Fintype.card R)-1 :=
  incidenceSublattice_card (left K) (right K) (left_surjective K hEmpty) (right_surjective K hK hnc)

theorem rowCount_pos [Nonempty R] (hK : Simplicial.Downward K) (hnc : NoConeVertices K) :
    0<rowCount K := by
  obtain ⟨e,he⟩ := right_surjective K hK hnc (Classical.arbitrary R)
  exact lt_of_le_of_lt (Nat.zero_le e.val) e.isLt

theorem nonfaces_nonempty [Nonempty R] (hK : Simplicial.Downward K) (hnc : NoConeVertices K) :
    Nonempty (Nonfaces K) := by
  obtain ⟨e,he⟩ := right_surjective K hK hnc (Classical.arbitrary R)
  exact ⟨left K e⟩

theorem nonfaces_card_pos [Nonempty R] (hK : Simplicial.Downward K) (hnc : NoConeVertices K) :
    0<Fintype.card (Nonfaces K) := by
  letI := nonfaces_nonempty K hK hnc
  exact Fintype.card_pos

end FourPapers.Sublattice.FiniteComplexIncidence
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceRealization -/
section

/-! # Integral realization in the actual fine Tor groups of every power

The displayed degree is the literal monomial with exponent one at row
levels zero and one and exponent m at level two. The shift uses augmented
face-cardinality degree q, hence the usual reduced degree q-1.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {L R k : Type u} [Fintype L] [Fintype R] [DecidableEq L] [LinearOrder R]
  [CommRing k] {M : ℕ} (left : Fin M → L) (right : Fin M → R)

theorem incidenceOutsideCover_iff (F : Finset (FiniteVariable.{u} (IncidenceRows M))) :
    CechFace.outsideCover (IncidenceJoin.omitted right) (incidenceLowerSupport (M := M)) F ↔
      incidenceRowCoverFaces right F := by
  constructor
  · rintro ⟨hF,⟨r,hr⟩⟩
    refine ⟨hF,r,fun e he heF => ?_⟩
    have hdis := (CechFace.mem_missing (IncidenceJoin.omitted right) F r).mp hr
    exact Finset.disjoint_left.mp hdis heF (by simp [IncidenceJoin.omitted,he])
  · rintro ⟨hF,r,hr⟩
    refine ⟨hF,r,(CechFace.mem_missing (IncidenceJoin.omitted right) F r).mpr ?_⟩
    apply Finset.disjoint_left.mpr
    intro v hvF hvU
    obtain ⟨hlevel,hright⟩ := (Finset.mem_filter.mp hvU).2
    have hvEq : v=⟨v.1,ULift.up 1⟩ := by
      rcases v with ⟨e,⟨a⟩⟩
      change a = 1 at hlevel
      subst a
      rfl
    exact hr v.1 hright (by simpa only [hvEq] using hvF)

theorem incidenceGamma_eq_cover :
    supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M))=
      CechFace.coverUnion (incidenceRowJoinFaces left) (IncidenceJoin.omitted right)
        (incidenceLowerSupport (M := M)) := by
  funext F
  apply propext
  rw [incidenceExpandedAlexander_faces,CechFace.coverUnion,incidenceOutsideCover_iff]

/-- The full integral incidence-cover calculation in the original row
variables, with its actual chain-degree shift. -/
def incidenceExpandedAlexanderNerveEquiv (hM : 0<M) (hl : Function.Surjective left) (q : ℕ) :
    AugmentedFaceHomology (k := k)
      (supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M)))
      (supportedAlexanderDualFaces_downward _ _) (q+Fintype.card L) ≃ₗ[k]
        AugmentedFaceHomology (k := k) (incidenceNerveFaces left right)
          (incidenceRowNerve_downward left right) q := by
  let a : FiniteVariable.{u} (IncidenceRows M) := ⟨⟨0,hM⟩,ULift.up 0⟩
  have he := CechFace.NerveReduction.coverHomologyEquiv (k := k)
    (incidenceRowJoinFaces left) (IncidenceJoin.omitted right) (incidenceNerveFaces left right)
    (IncidenceJoin.cechContraction left right hl) (IncidenceJoin.join_downward left)
    (incidenceRowNerve_downward left right) (IncidenceJoin.cechContraction_d left right hl)
    (IncidenceJoin.cechProjection_natural left right hl) (Fintype.card L)
    (IncidenceJoin.cechHomotopy_raises left right hl)
    (IncidenceJoin.cechInclusion_degree left right hl)
    (by
      intro Q F hF
      exact congrArg Subtype.val (IncidenceJoin.cechProjection_zero_off_degree left right hl Q
        F.val.card hF (totalFaceBasis (k := k) _ F) (by
          change (totalFaceBasis (k := k) _ F).val ∈ Simplicial.Chains _ F.val.card
          rw [totalFaceBasis_val]
          exact Simplicial.basis_mem F.property rfl)))
    (incidenceLowerSupport (M := M)) (fun F hF => hF.1) a
    (by simp [a,incidenceLowerSupport_mem])
    (by intro r; simp [a,IncidenceJoin.omitted]) q
  exact (augmentedFaceHomologyEquivOfFaces (k := k)
    (supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M)))
    (CechFace.coverUnion (incidenceRowJoinFaces left) (IncidenceJoin.omitted right)
      (incidenceLowerSupport (M := M)))
    (supportedAlexanderDualFaces_downward _ _)
    (CechFace.coverUnion_downward (incidenceRowJoinFaces left) (IncidenceJoin.omitted right)
      (incidenceLowerSupport (M := M)) (IncidenceJoin.join_downward left))
    (incidenceGamma_eq_cover left right) (q+Fintype.card L)).trans he

/-- Genuine fine Tor of I_E^m, with no coefficient field hypothesis. -/
def incidencePowerRealizationEquiv [Nontrivial k]
    (hM : 0<M) (hl : Function.Surjective left) (hr : Function.Surjective right)
    (m : ℕ) (hm : 0< m) (q : ℕ) :
    gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows M) (incidenceSublattice left right)) m)
      (incidenceRealizationDegree (M := M) m) (q+Fintype.card L+1) ≃ₗ[k]
        AugmentedFaceHomology (k := k) (incidenceNerveFaces left right)
          (incidenceRowNerve_downward left right) q := by
  let A := incidencePowerTopTorEquiv (k := k) (incidenceSublattice_closed left right)
    (incidenceTop_mem left right) m hm (q+Fintype.card L+1)
  let B := quotientHomologyEquivOfContains (k := k)
    (finitePredecessorFamily (IncidenceRows M) (incidenceSublattice left right) incidenceTop)
    (incidenceTopFamily left right) (incidenceResidualDegree (M := M))
    (incidenceTopFamily_contains_iff left right hM hr) (q+Fintype.card L+1)
  let e : FiniteVariable.{u} (IncidenceRows M) := ⟨⟨0,hM⟩,ULift.up 0⟩
  have C : (quotientHomogeneousComplex (k := k) (incidenceTopFamily left right)
      (incidenceResidualDegree (M := M))).homology (q+Fintype.card L+1) ≃ₗ[k]
      AugmentedFaceHomology (k := k)
        (supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M)))
        (supportedAlexanderDualFaces_downward _ _) (q+Fintype.card L) := by
    rw [incidenceResidualDegree_eq_face]
    exact supportedSquarefreeAlexanderDuality (k := k) _ _ e (by simp [e,incidenceLowerSupport_mem]) _
  exact A.trans (B.trans (C.trans (incidenceExpandedAlexanderNerveEquiv left right hM hl q)))

theorem incidenceExpandedAlexander_zero_below (hM : 0<M) (hl : Function.Surjective left)
    (p : ℕ) (hp : p<Fintype.card L) :
    Subsingleton (AugmentedFaceHomology (k := k)
      (supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M)))
      (supportedAlexanderDualFaces_downward _ _) p) := by
  let a : FiniteVariable.{u} (IncidenceRows M) := ⟨⟨0,hM⟩,ULift.up 0⟩
  have he := CechFace.NerveReduction.coverHomology_subsingleton_below (k := k)
    (incidenceRowJoinFaces left) (IncidenceJoin.omitted right) (incidenceNerveFaces left right)
    (IncidenceJoin.cechContraction left right hl) (IncidenceJoin.join_downward left)
    (IncidenceJoin.cechContraction_d left right hl) (Fintype.card L)
    (IncidenceJoin.cechHomotopy_raises left right hl)
    (by
      intro Q F hF
      exact congrArg Subtype.val (IncidenceJoin.cechProjection_zero_off_degree left right hl Q
        F.val.card hF (totalFaceBasis (k := k) _ F) (by
          change (totalFaceBasis (k := k) _ F).val ∈ Simplicial.Chains _ F.val.card
          rw [totalFaceBasis_val]
          exact Simplicial.basis_mem F.property rfl)))
    (incidenceLowerSupport (M := M)) (fun F hF => hF.1) a
    (by simp [a,incidenceLowerSupport_mem])
    (by intro r; simp [a,IncidenceJoin.omitted]) p hp
  letI := he
  let e := augmentedFaceHomologyEquivOfFaces (k := k)
    (supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M)))
    (CechFace.coverUnion (incidenceRowJoinFaces left) (IncidenceJoin.omitted right)
      (incidenceLowerSupport (M := M)))
    (supportedAlexanderDualFaces_downward _ _)
    (CechFace.coverUnion_downward (incidenceRowJoinFaces left) (IncidenceJoin.omitted right)
      (incidenceLowerSupport (M := M)) (IncidenceJoin.join_downward left))
    (incidenceGamma_eq_cover left right) p
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

private theorem quotient_zero_degree {W : Type u} [Fintype W] [LinearOrder W]
    (B : Family W) (α : Exponent W) (e : W) (he : 0<α e) :
    Subsingleton ((quotientHomogeneousComplex (k := k) B α).homology 0) := by
  letI : Subsingleton (ClosedGraphDegreeHomology (k := k) B α 0) := by
    constructor
    intro x y
    obtain ⟨z,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary (k := k) B α 0)).mkQ_surjective x
    obtain ⟨w,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary (k := k) B α 0)).mkQ_surjective y
    apply (Submodule.Quotient.eq _).mpr
    obtain ⟨a,ha,hda⟩ := quotientCycle_boundary_degree_zero (k := k) B α e he (z.val-w.val)
      (Submodule.sub_mem _ z.property.2 w.property.2)
    exact ⟨⟨a,ha⟩,Subtype.ext hda⟩
  exact (quotientCategoricalDegreeHomologyEquiv (k := k) B α 0).injective.subsingleton

theorem incidencePowerRealization_zero_below [Nontrivial k]
    (hM : 0<M) (hl : Function.Surjective left) (hr : Function.Surjective right)
    (m : ℕ) (hm : 0< m) (p : ℕ) (hp : p<Fintype.card L+1) :
    Subsingleton (gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows M) (incidenceSublattice left right)) m)
      (incidenceRealizationDegree (M := M) m) p) := by
  let A := incidencePowerTopTorEquiv (k := k) (incidenceSublattice_closed left right)
    (incidenceTop_mem left right) m hm p
  let B := quotientHomologyEquivOfContains (k := k)
    (finitePredecessorFamily (IncidenceRows M) (incidenceSublattice left right) incidenceTop)
    (incidenceTopFamily left right) (incidenceResidualDegree (M := M))
    (incidenceTopFamily_contains_iff left right hM hr) p
  let e : FiniteVariable.{u} (IncidenceRows M) := ⟨⟨0,hM⟩,ULift.up 0⟩
  cases p with
  | zero =>
      letI := quotient_zero_degree (k := k) (incidenceTopFamily left right)
        (incidenceResidualDegree (M := M)) e (by simp [e,incidenceResidualDegree_apply])
      exact (A.trans B).injective.subsingleton
  | succ p =>
      letI := incidenceExpandedAlexander_zero_below (k := k) left right hM hl p (by omega)
      have C : (quotientHomogeneousComplex (k := k) (incidenceTopFamily left right)
          (incidenceResidualDegree (M := M))).homology (p+1) ≃ₗ[k]
          AugmentedFaceHomology (k := k)
            (supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M)))
            (supportedAlexanderDualFaces_downward _ _) p := by
        rw [incidenceResidualDegree_eq_face]
        exact supportedSquarefreeAlexanderDuality (k := k) _ _ e (by simp [e,incidenceLowerSupport_mem]) _
      exact (A.trans (B.trans C)).injective.subsingleton

/-- Full integer-indexed realization, including every low homological
degree. The right side is genuine augmented-chain reduced homology. -/
def incidencePowerReducedRealizationEquiv [Nontrivial k]
    (hM : 0<M) (hl : Function.Surjective left) (hr : Function.Surjective right)
    (m : ℕ) (hm : 0< m) (p : ℕ) :
    gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows M) (incidenceSublattice left right)) m)
      (incidenceRealizationDegree (M := M) m) p ≃ₗ[k]
        ReducedFaceHomology (k := k) (incidenceNerveFaces left right)
          (incidenceRowNerve_downward left right) ((p:ℤ)-Fintype.card L-2) := by
  by_cases hp : Fintype.card L+1≤p
  · let q := p-(Fintype.card L+1)
    have hpq : p=q+Fintype.card L+1 := by dsimp [q]; omega
    have ht : (p:ℤ)-Fintype.card L-2+1=(q:ℤ) := by omega
    change gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows M) (incidenceSublattice left right)) m)
      (incidenceRealizationDegree (M := M) m) p ≃ₗ[k]
        IntegerAugmentedFaceHomology (k := k) (incidenceNerveFaces left right)
          (incidenceRowNerve_downward left right) ((p : ℤ)-Fintype.card L-2+1)
    rw [ht,hpq]
    exact (incidencePowerRealizationEquiv (k := k) left right hM hl hr m hm q).trans
      (integerAugmentedNatEquiv (k := k) _ _ q).symm
  · letI := incidencePowerRealization_zero_below (k := k) left right hM hl hr m hm p (by omega)
    letI := integerAugmented_negative (k := k) (incidenceNerveFaces left right)
      (incidenceRowNerve_downward left right) ((p:ℤ)-Fintype.card L-2+1) (by omega)
    exact LinearEquiv.ofSubsingleton _ _

namespace FiniteComplexIncidence
variable [Nonempty R] (K : Finset R → Prop) (hK : Simplicial.Downward K) (hEmpty : K ∅)
  (hnc : NoConeVertices K)

/-- Corollary 10.3 in the nonnegative augmented degree convention.
The complementary low degrees are covered by the vanishing theorem. -/
def theorem103_realization [Nontrivial k] (m : ℕ) (hm : 0< m) (q : ℕ) :
    gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows (rowCount K)) (lattice K)) m)
      (incidenceRealizationDegree (M := rowCount K) m)
      (q+Fintype.card (Nonfaces K)+1) ≃ₗ[k]
        AugmentedFaceHomology (k := k) K hK q := by
  have h := incidencePowerRealizationEquiv (k := k) (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)
    (rowCount_pos K hK hnc) (left_surjective K hEmpty) (right_surjective K hK hnc) m hm q
  have hfaces : incidenceNerveFaces (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)=K :=
    funext fun Q => propext (nerve_iff_face K hK Q)
  exact h.trans (augmentedFaceHomologyEquivOfFaces (k := k)
    (incidenceNerveFaces (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)) K
    (incidenceRowNerve_downward (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)) hK hfaces q)

/-- Corollary 10.3 with its original quantification over every i≥0 and
the exact reduced integral degree i-|N|-2. -/
def theorem103_all_degrees [Nontrivial k] (m : ℕ) (hm : 0< m) (p : ℕ) :
    gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows (rowCount K)) (lattice K)) m)
      (incidenceRealizationDegree (M := rowCount K) m) p ≃ₗ[k]
        ReducedFaceHomology (k := k) K hK ((p:ℤ)-Fintype.card (Nonfaces K)-2) := by
  have h := incidencePowerReducedRealizationEquiv (k := k) (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)
    (rowCount_pos K hK hnc) (left_surjective K hEmpty) (right_surjective K hK hnc) m hm p
  have hfaces : incidenceNerveFaces (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)=K :=
    funext fun Q => propext (nerve_iff_face K hK Q)
  exact h.trans (reducedFaceHomologyEquivOfFaces (k := k)
    (incidenceNerveFaces (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)) K
    (incidenceRowNerve_downward (FiniteComplexIncidence.left K) (FiniteComplexIncidence.right K)) hK hfaces
    ((p:ℤ)-Fintype.card (Nonfaces K)-2))

include hEmpty hnc in
theorem theorem103_field_betti {k : Type u} [Field k] [Nonempty R] (m : ℕ) (hm : 0< m) (q : ℕ) :
    Module.finrank k (gradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows (rowCount K)) (lattice K)) m)
      (incidenceRealizationDegree (M := rowCount K) m)
      (q+Fintype.card (Nonfaces K)+1))=
        Module.finrank k (AugmentedFaceHomology (k := k) K hK q) :=
  (theorem103_realization (k := k) K hK hEmpty hnc m hm q).finrank_eq

end FiniteComplexIncidence
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceRealizationStatements -/
section

/-! # The printed all-degree field statement of Corollary 10.3

The realization theorem is already an equivalence over every nontrivial
commutative coefficient ring. These small consequences expose its exact
field-dimension statement at every homological degree, together with the
literal full squarefree degree at the first power.
-/

section
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

/-- At the first power the displayed degree is exactly the product of
all three variables in every incidence row. -/
theorem incidenceRealizationDegree_one {M : ℕ} :
    incidenceRealizationDegree (M := M) 1 =
      faceExponent (Finset.univ : Finset (FiniteVariable.{u} (IncidenceRows M))) := by
  ext v
  simp only [incidenceRealizationDegree_apply, faceExponent_apply,
    Finset.mem_univ, if_true, ite_self]

namespace FiniteComplexIncidence
variable {R k : Type u} [Fintype R] [LinearOrder R] [Field k]
  (K : Finset R → Prop) (hK : Simplicial.Downward K) (hEmpty : K ∅)
  (hnc : NoConeVertices K)

include hEmpty hnc in
/-- The field assertion of Corollary 10.3 at every p≥0, including the
low degrees where the reduced homology index is negative. -/
theorem theorem103_field_betti_all_degrees [Nonempty R] (m : ℕ) (hm : 0 < m) (p : ℕ) :
    bettiNumber (k := k)
      (exponentPowerFamily (finiteRowFamily (IncidenceRows (rowCount K)) (lattice K)) m)
      (incidenceRealizationDegree (M := rowCount K) m) p =
        Module.finrank k (ReducedFaceHomology (k := k) K hK
          ((p : ℤ) - Fintype.card (Nonfaces K) - 2)) :=
  (theorem103_all_degrees (k := k) K hK hEmpty hnc m hm p).finrank_eq

end FiniteComplexIncidence
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem41 -/
section

/-! # Theorem 4.1 with both actual localization conventions

The paper localizes the powers of each minimal prime; `radicalSymbolicPower`
is exactly that construction. The customary construction localizing powers of
the ideal itself is `symbolicPower`. This endpoint displays both, together with
the exact minimal-cover intersection supplied by the network theorem.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice.RowCutNetwork

open Classical MvPolynomial
universe u v
variable {ι : Type u} [Fintype ι] (n : ι → ℕ)
  {k : Type v} [Field k]
local instance : DecidableEq ι := Classical.decEq ι

/-- **Theorem 4.1.** Every ordinary power equals the paper's minimal-prime
localized symbolic power, the ideal-power localization convention, and the
intersection of the indicated coordinate-prime powers. The result also covers
the empty sublattice and power zero. -/
theorem theorem41
    (E : Finset (Tuple n))
    (hinf : ∀ a ∈ E, ∀ b ∈ E, a ⊓ b ∈ E)
    (hsup : ∀ a ∈ E, ∀ b ∈ E, a ⊔ b ∈ E) (s : ℕ) :
    (monomialIdeal n k E)^s = FourPapers.radicalSymbolicPower (monomialIdeal n k E) s ∧
    (monomialIdeal n k E)^s = FourPapers.symbolicPower (monomialIdeal n k E) s ∧
    (monomialIdeal n k E)^s =
      ⨅ C : {C : Finset (Label n) // IsMinimalCover n E C}, coordinateIdeal C.val ^ s := by
  let ord : LinearOrder (Label n) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let wf : @WellFoundedGT (Label n) ord.toLT :=
    @Finite.to_wellFoundedGT (Label n) inferInstance ord.toPreorder
  let m : MonomialOrder (Label n) := @MonomialOrder.lex (Label n) ord wf
  have hinit := initialIdeal_monomialIdeal n (k:=k) m E
  exact ⟨(verified_theorem_4_1 n E hinf hsup s).1,
    (symbolicPower_eq_power n m _ E hinf hsup hinit s).symm,
    power_eq_iInf_minimalCover n E hinf hsup s⟩

end FourPapers.Sublattice.RowCutNetwork

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ExteriorPartitionCocycle -/
section

/-!
# A detecting cocycle for a partition of the variables

For a map of variables to a finite set of blocks, the induced exterior map
kills every word longer than the number of blocks. In that top degree it
also kills every face missing a block. Consequently it annihilates the
actual quotient boundaries when the allowed faces are precisely the faces
meeting every block. A transversal is a closed, detected nonzero class.

This is an explicit integral cycle and detector, not an appeal to the
complete-intersection theorem or to a fieldwise dimension count.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u v
variable {V k : Type u} {W : Type v} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [CommRing k]

def variablePartitionLinear (f : V → W) : (V → k) →ₗ[k] (W → k) :=
  (Pi.basisFun k V).constr k (fun v => Pi.basisFun k W (f v))

@[simp] lemma variablePartitionLinear_basis (f : V → W) (v : V) :
    variablePartitionLinear (k := k) f (Pi.basisFun k V v) = Pi.basisFun k W (f v) := by
  simp [variablePartitionLinear]

def exteriorPartition (f : V → W) : Simplicial.Ambient V k →ₐ[k] Simplicial.Ambient W k :=
  ExteriorAlgebra.map (variablePartitionLinear f)

lemma exteriorPartition_basis_word (f : V → W) (F : Finset V) :
    exteriorPartition (k := k) f (Simplicial.basis F) =
      ((F.sort.map f).map (fun w => ExteriorAlgebra.ι k (Pi.basisFun k W w))).prod := by
  rw [Simplicial.basis, Module.Basis.exteriorAlgebra_eq_prod_map_sort,
    map_list_prod, List.map_map]
  simp only [exteriorPartition, ExteriorAlgebra.map_apply_ι, variablePartitionLinear_basis,
    List.map_map, Function.comp_apply]
  congr 1
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp_apply, ExteriorAlgebra.map_apply_ι, variablePartitionLinear_basis]

lemma exteriorPartition_basis_unit (f : V → W) (F : Finset V)
    (hf : Set.InjOn f (F : Set V)) :
    ∃ ε : ℤˣ, exteriorPartition (k := k) f (Simplicial.basis F) =
      ε • Simplicial.basis (F.image f) := by
  rw [exteriorPartition_basis_word]
  have hn : (F.sort.map f).Nodup := (F.sort_nodup _).map_on
    (by
      intro a ha b hb hab
      exact hf (by simpa only [Finset.mem_sort, Finset.mem_coe] using ha)
        (by simpa only [Finset.mem_sort, Finset.mem_coe] using hb) hab)
  obtain ⟨ε, hε⟩ := exterior_word_unit_basis (Pi.basisFun k W) (F.sort.map f) hn
  have hset : (F.sort.map f).toFinset = F.image f := by
    ext w
    simp
  exact ⟨ε, by simpa only [hset, Simplicial.basis] using hε⟩

lemma exteriorPartition_basis_zero (f : V → W) (F : Finset V)
    (hf : ¬Set.InjOn f (F : Set V)) :
    exteriorPartition (k := k) f (Simplicial.basis F) = 0 := by
  have he : exteriorPartition (k := k) f (Simplicial.basis F) =
      ExteriorAlgebra.ιMulti k F.card
        (fun i => Pi.basisFun k W (f (F.orderIsoOfFin rfl i).val)) := by
    rw [exteriorPartition_basis_word, ExteriorAlgebra.ιMulti_apply]
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map, List.getElem_ofFn, Finset.coe_orderIsoOfFin_apply,
      Finset.orderEmbOfFin_apply, Fin.getElem_fin]
  rw [he]
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  intro hinj
  apply hf
  intro a ha b hb hab
  let i := (F.orderIsoOfFin rfl).symm ⟨a, ha⟩
  let j := (F.orderIsoOfFin rfl).symm ⟨b, hb⟩
  have hij : i = j := hinj (by
    dsimp only [i, j]
    simp only [OrderIso.apply_symm_apply]
    exact congrArg (Pi.basisFun k W) hab)
  have hv := congrArg (fun t => (F.orderIsoOfFin rfl t).val) hij
  simpa only [i, j, OrderIso.apply_symm_apply] using hv

lemma exteriorPartition_basis_zero_of_card (f : V → W) (F : Finset V)
    (hF : Fintype.card W < F.card) :
    exteriorPartition (k := k) f (Simplicial.basis F) = 0 := by
  apply exteriorPartition_basis_zero
  intro hinj
  have hh : F.card ≤ Fintype.card W := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_univ _
  omega

lemma exteriorPartition_basis_zero_of_missing (f : V → W) (F : Finset V)
    (hcard : F.card = Fintype.card W) (hmiss : F.image f ≠ Finset.univ) :
    exteriorPartition (k := k) f (Simplicial.basis F) = 0 := by
  apply exteriorPartition_basis_zero
  intro hinj
  apply hmiss
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn hinj, hcard]

lemma variablePartitionLinear_pullback (f : V → W) :
    (Fintype.linearCombination k (fun _ : W => (1 : k))).comp (variablePartitionLinear f) =
      Fintype.linearCombination k (fun _ : V => (1 : k)) := by
  apply (Pi.basisFun k V).ext
  intro v
  simp only [LinearMap.comp_apply, variablePartitionLinear_basis]
  simp [Fintype.linearCombination_apply,
    Pi.basisFun_apply, Pi.single_apply, ite_mul]

lemma exteriorPartition_boundary (f : V → W) (x : Simplicial.Ambient V k) :
    exteriorPartition f (Simplicial.boundary x) =
      Simplicial.boundary (exteriorPartition f x) := by
  rw [Simplicial.boundary, exteriorPartition, ExteriorAlgebra.contractLeft_map,
    variablePartitionLinear_pullback]

section Quotient
variable (B : Family V) (α : Exponent V) (f : V → W)
  (hQ : ∀ F, fullKoszulFaces α F →
    (quotientKoszulFaces B α F ↔ F.image f = Finset.univ))

include hQ in
lemma exteriorPartition_quotient_boundary_basis
    (F : {F // quotientKoszulFaces B α F})
    (hcard : F.val.card = Fintype.card W + 1) :
    exteriorPartition (k := k) f
      (quotientTotalDifferential B α (totalFaceBasis _ F)).val = 0 := by
  have hfull : fullKoszulFaces α F.val := F.property.1
  have hproj : exteriorPartition (k := k) f
      (quotientTotalDifferential B α (totalFaceBasis _ F)).val =
      exteriorPartition f (Simplicial.boundary (Simplicial.basis F.val)) := by
    rw [quotientTotalDifferential_basis, Submodule.coe_sum, map_sum,
      face_boundary_basis_sum, map_sum]
    apply Finset.sum_congr rfl
    intro v _
    have hfull' := fullKoszulFaces_downward α (Finset.erase_subset v.val F.val) hfull
    have hcard' : (F.val.erase v.val).card = Fintype.card W := by
      rw [Finset.card_erase_of_mem v.property, hcard]
      omega
    split_ifs with hq
    · simp only [Submodule.coe_smul_of_tower, totalFaceBasis_val, map_zsmul_unit]
    · have hz := exteriorPartition_basis_zero_of_missing (k := k) f (F.val.erase v.val)
        hcard' (fun he => hq ((hQ _ hfull').mpr he))
      simp only [ZeroMemClass.coe_zero, map_zero, map_zsmul_unit, hz, smul_zero]
  rw [hproj, exteriorPartition_boundary,
    exteriorPartition_basis_zero_of_card f F.val (by omega), map_zero]

include hQ in
lemma exteriorPartition_quotient_boundary (x : totalFacePiece (k := k)
    (quotientKoszulFaces B α) (Fintype.card W + 1)) :
    exteriorPartition (k := k) f (closedGraphDegreeBoundary B α (Fintype.card W) x).val.val = 0 := by
  have hz : ((exteriorPartition (k := k) f).toLinearMap.comp
      (TotalFaceModule (k := k) (quotientKoszulFaces B α)).subtype).comp
        ((ClosedGraphDegreeCycles (k := k) B α (Fintype.card W)).subtype.comp
          (closedGraphDegreeBoundary B α (Fintype.card W))) = 0 := by
    apply (quotientTotalPieceBasis (k := k) B α (Fintype.card W + 1)).ext
    intro F
    change exteriorPartition f (quotientTotalDifferential B α
      (quotientTotalPieceBasis B α (Fintype.card W + 1) F).val).val = 0
    rw [quotientTotalPieceBasis_val]
    exact exteriorPartition_quotient_boundary_basis B α f hQ
      ⟨F.val, F.property.1⟩ F.property.2
  exact LinearMap.congr_fun hz x

include hQ in
lemma transversal_quotient_cycle (F : Finset V)
    (hF : quotientKoszulFaces B α F) (hcard : F.card = Fintype.card W) :
    quotientTotalDifferential (k := k) B α (totalFaceBasis _ ⟨F, hF⟩) = 0 := by
  rw [quotientTotalDifferential_basis]
  apply Finset.sum_eq_zero
  intro v _
  have hnot : ¬quotientKoszulFaces B α (F.erase v.val) := by
    intro hq
    have he := (hQ _ hq.1).mp hq
    have hc := Finset.card_image_le (f := f) (s := F.erase v.val)
    rw [he, Finset.card_univ, Finset.card_erase_of_mem v.property, hcard] at hc
    have hpos : 0 < Fintype.card W := by
      rw [← hcard]
      exact Finset.card_pos.mpr ⟨v.val, v.property⟩
    omega
  rw [dif_neg hnot]


include hQ in
/-- A transversal gives an actual nonzero class in the exact homogeneous
cycle/boundary quotient, over every nonzero coefficient ring. -/
theorem transversal_quotient_homology_nontrivial [Nontrivial k]
    (F : Finset V) (hF : quotientKoszulFaces B α F)
    (hcard : F.card = Fintype.card W) :
    Nontrivial (ClosedGraphDegreeHomology (k := k) B α (Fintype.card W)) := by
  have himage : F.image f = Finset.univ := (hQ F hF.1).mp hF
  have hinj : Set.InjOn f (F : Set V) := Finset.injOn_of_card_image_eq (by
    rw [himage, Finset.card_univ, hcard])
  obtain ⟨ε, hε⟩ := exteriorPartition_basis_unit (k := k) f F hinj
  have hdetect : exteriorPartition (k := k) f (Simplicial.basis F) ≠ 0 := by
    rw [hε]
    intro hz
    have hh := congrArg (fun z : Simplicial.Ambient W k => ε⁻¹ • z) hz
    have hb : Simplicial.basis (k := k) (F.image f) = 0 := by
      simpa only [inv_smul_smul, smul_zero] using hh
    exact (Simplicial.basis (k := k)).ne_zero (F.image f) hb
  let z : ClosedGraphDegreeCycles (k := k) B α (Fintype.card W) :=
    ⟨totalFaceBasis (quotientKoszulFaces B α) ⟨F, hF⟩,
      ⟨transversal_quotient_cycle B α f hQ F hF hcard,
        by
          change (totalFaceBasis (k := k) (quotientKoszulFaces B α) ⟨F, hF⟩).val ∈
            Simplicial.Chains (k := k) (quotientKoszulFaces B α) (Fintype.card W)
          rw [totalFaceBasis_val]
          exact Simplicial.basis_mem hF hcard⟩⟩
  have hz : (Submodule.Quotient.mk z : ClosedGraphDegreeHomology (k := k) B α
      (Fintype.card W)) ≠ 0 := by
    intro he
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp he
    have hh := congrArg (fun t : ClosedGraphDegreeCycles (k := k) B α (Fintype.card W) =>
      exteriorPartition f t.val.val) hy
    rw [exteriorPartition_quotient_boundary B α f hQ] at hh
    exact hdetect (by simpa only [z, totalFaceBasis_val] using hh.symm)
  exact ⟨⟨Submodule.Quotient.mk z, 0, hz⟩⟩

include hQ in
theorem quotientBetti_nonzero_of_transversal {K : Type u} [Field K]
    (F : Finset V) (hF : quotientKoszulFaces B α F)
    (hcard : F.card = Fintype.card W) :
    quotientBettiNumber (k := K) B α (Fintype.card W) ≠ 0 := by
  letI := transversal_quotient_homology_nontrivial (k := K) B α f hQ F hF hcard
  letI : Module.Finite K (ClosedGraphDegreeHomology (k := K) B α (Fintype.card W)) :=
    Module.Finite.equiv (quotientCategoricalDegreeHomologyEquiv B α (Fintype.card W))
  rw [quotientBettiNumber_eq_homology,
    (quotientCategoricalDegreeHomologyEquiv B α (Fintype.card W)).finrank_eq]
  exact ne_of_gt Module.finrank_pos

end Quotient
end FourPapers.Sublattice
end


end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.DisjointSquarefreeTopHomology -/
section

/-!
# Nonzero top Koszul homology of disjoint squarefree monomials

The fine degree is the sum of the actual monomial exponents.  Its quotient
faces meet every support block.  Choosing one variable from each block
provides the transversal detected by the induced exterior map.  All
hypotheses are checked explicitly for the maximal-chain coefficient ideal
in the next module.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u v
variable {V k : Type u} {I : Type v} [Fintype V] [LinearOrder V]
  [Fintype I] [LinearOrder I] [Nonempty I] [CommRing k]
variable (g : I → Exponent V)
  (hnonzero : ∀ i, g i ≠ 0)
  (hsquare : ∀ i x, g i x ≤ 1)
  (hdisjoint : Pairwise (fun i j => Disjoint (g i).support (g j).support))

def blockTotalExponent : Exponent V := ∑ i, g i

include hsquare in
lemma blockExponent_eq_one {i : I} {x : V} (hx : x ∈ (g i).support) :
    g i x = 1 := by
  have hpos := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)
  have hle := hsquare i x
  omega

include hsquare hdisjoint in
lemma blockTotalExponent_at {i : I} {x : V} (hx : x ∈ (g i).support) :
    blockTotalExponent g x = 1 := by
  rw [blockTotalExponent, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · exact blockExponent_eq_one g hsquare hx
  · intro j _ hji
    apply Finsupp.notMem_support_iff.mp
    intro hj
    exact Finset.disjoint_left.mp (hdisjoint hji) hj hx
  · simp

lemma blockTotalExponent_support {x : V} (hx : 0 < blockTotalExponent g x) :
    ∃ i, x ∈ (g i).support := by
  have hh : (∑ i, g i x) ≠ 0 := by
    simpa only [blockTotalExponent, Finsupp.finsetSum_apply] using ne_of_gt hx
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
  exact ⟨i, Finsupp.mem_support_iff.mpr hi⟩

def supportBlock (x : V) : I :=
  if h : ∃ i, x ∈ (g i).support then Classical.choose h else Classical.choice inferInstance

include hdisjoint in
lemma supportBlock_eq {i : I} {x : V} (hx : x ∈ (g i).support) :
    supportBlock g x = i := by
  rw [supportBlock, dif_pos ⟨i, hx⟩]
  by_contra hne
  have hy := Classical.choose_spec (show ∃ i, x ∈ (g i).support from ⟨i, hx⟩)
  exact Finset.disjoint_left.mp (hdisjoint hne) hy hx

include hdisjoint in
lemma mem_supportBlock {x : V} (hx : 0 < blockTotalExponent g x) :
    x ∈ (g (supportBlock g x)).support := by
  obtain ⟨i, hi⟩ := blockTotalExponent_support g hx
  rwa [supportBlock_eq g hdisjoint hi]

def supportWitness (i : I) : V :=
  Classical.choose (Finsupp.support_nonempty_iff.mpr (hnonzero i))

lemma supportWitness_mem (i : I) : supportWitness g hnonzero i ∈ (g i).support :=
  Classical.choose_spec (Finsupp.support_nonempty_iff.mpr (hnonzero i))

include hdisjoint in
@[simp] lemma supportBlock_supportWitness (i : I) :
    supportBlock g (supportWitness g hnonzero i) = i :=
  supportBlock_eq g hdisjoint (supportWitness_mem g hnonzero i)

include hdisjoint in
lemma supportWitness_injective : Function.Injective (supportWitness g hnonzero) := by
  intro i j hij
  have hh := congrArg (supportBlock g) hij
  simpa only [supportBlock_supportWitness g hnonzero hdisjoint] using hh

def blockTransversal : Finset V := Finset.univ.image (supportWitness g hnonzero)

include hdisjoint in
lemma blockTransversal_card : (blockTransversal g hnonzero).card = Fintype.card I := by
  rw [blockTransversal, Finset.card_image_of_injective _ (supportWitness_injective g hnonzero hdisjoint),
    Finset.card_univ]

include hdisjoint in
lemma blockTransversal_image : (blockTransversal g hnonzero).image (supportBlock g) = Finset.univ := by
  ext i
  simp [blockTransversal, Finset.mem_image, supportBlock_supportWitness g hnonzero hdisjoint]

include hsquare hdisjoint in
lemma blockTransversal_full : fullKoszulFaces (blockTotalExponent g) (blockTransversal g hnonzero) := by
  intro x
  by_cases hx : x ∈ blockTransversal g hnonzero
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [faceExponent_apply, if_pos hx, blockTotalExponent_at g hsquare hdisjoint
      (supportWitness_mem g hnonzero i)]
  · rw [faceExponent_apply, if_neg hx]
    exact Nat.zero_le _

variable (B : Family V)
  (hB : ∀ a : Exponent V, Contains B a ↔ ∃ i, g i ≤ a)

include hsquare hdisjoint hB in
/-- The exact fine quotient faces are precisely the full faces hitting every
block. This also accounts for all unused ambient variables. -/
theorem disjointSquarefree_quotientFaces (F : Finset V)
    (hfull : fullKoszulFaces (blockTotalExponent g) F) :
    quotientKoszulFaces B (blockTotalExponent g) F ↔
      F.image (supportBlock g) = Finset.univ := by
  constructor
  · intro hF
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    apply hF.2
    apply (hB _).mpr
    refine ⟨i, ?_⟩
    intro x
    by_cases hx : x ∈ (g i).support
    · have hxF : x ∉ F := by
        intro hxF
        exact hi (Finset.mem_image.mpr ⟨x, hxF, supportBlock_eq g hdisjoint hx⟩)
      rw [blockExponent_eq_one g hsquare hx, Finsupp.tsub_apply,
        blockTotalExponent_at g hsquare hdisjoint hx, faceExponent_apply, if_neg hxF]
    · rw [Finsupp.notMem_support_iff.mp hx]
      exact Nat.zero_le _
  · intro hF
    refine ⟨hfull, ?_⟩
    intro hcontains
    obtain ⟨i, hi⟩ := (hB _).mp hcontains
    obtain ⟨x, hxF, hxi⟩ := Finset.mem_image.mp (hF.symm ▸ Finset.mem_univ i)
    have hxpos : 0 < blockTotalExponent g x := by
      have hh := hfull x
      rw [faceExponent_apply, if_pos hxF] at hh
      exact Nat.zero_lt_one.trans_le hh
    have hx : x ∈ (g i).support := by
      rw [← hxi]
      exact mem_supportBlock g hdisjoint hxpos
    have hbad := hi x
    rw [blockExponent_eq_one g hsquare hx, Finsupp.tsub_apply,
      blockTotalExponent_at g hsquare hdisjoint hx, faceExponent_apply, if_pos hxF] at hbad
    omega

include hnonzero hsquare hdisjoint hB in
theorem disjointSquarefree_quotient_homology_nontrivial [Nontrivial k] :
    Nontrivial (ClosedGraphDegreeHomology (k := k) B (blockTotalExponent g) (Fintype.card I)) := by
  have hQ := disjointSquarefree_quotientFaces g hsquare hdisjoint B hB
  have hF := (hQ _ (blockTransversal_full g hnonzero hsquare hdisjoint)).mpr
    (blockTransversal_image g hnonzero hdisjoint)
  exact transversal_quotient_homology_nontrivial B (blockTotalExponent g) (supportBlock g)
    hQ (blockTransversal g hnonzero) hF (blockTransversal_card g hnonzero hdisjoint)

include hnonzero hsquare hdisjoint hB in
theorem disjointSquarefree_quotientBetti_nonzero {K : Type u} [Field K] :
    quotientBettiNumber (k := K) B (blockTotalExponent g) (Fintype.card I) ≠ 0 := by
  have hQ := disjointSquarefree_quotientFaces g hsquare hdisjoint B hB
  have hF := (hQ _ (blockTransversal_full g hnonzero hsquare hdisjoint)).mpr
    (blockTransversal_image g hnonzero hdisjoint)
  exact quotientBetti_nonzero_of_transversal B (blockTotalExponent g) (supportBlock g)
    hQ (blockTransversal g hnonzero) hF (blockTransversal_card g hnonzero hdisjoint)

end FourPapers.Sublattice
end


end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralTheorem71 -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-!
# Theorem 7.1: public statements and correspondence

The positive-power endpoint includes every integer fine degree and every
multichain. Its coefficient ideals are the proved sums of actual predecessor
colons, and its source ideal is the actual ordinary ideal power. The family
endpoint includes auxiliary degree zero and extends the natural fine grading
by its proved zero components outside the nonnegative orthant.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped Polynomial
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Faithfulness of the source: the exponent family denotes the actual
ordinary power of the paper's row-monomial ideal. -/
theorem theorem71_sourceIdeal (m : ℕ) :
    monomialIdeal k (exponentPowerFamily (finiteRowFamily n E) m) =
      finiteSublatticeIdeal n (k := k) E ^ m :=
  finitePowerFamily_ideal n E m

/-- Faithfulness of the coefficients: `C_w` is the sum of the genuine ideal
colons from the lexicographic filtration, not an assumed replacement ideal. -/
theorem theorem71_coefficientIdeal {m : ℕ} (w : FiniteMultichain n E m) :
    monomialIdeal k (finiteChainCoefficientFamily n w) =
      ⨆ s, finitePredecessorColon n (k := k) E (w.val s).val :=
  finiteChainCoefficientFamily_ideal n w

/-- Equation (7.1), over the integers, with unrestricted fine degree and every
multichain present in the direct sum. -/
def theorem71_integral (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m)
    (α : FiniteVariable.{0} n →₀ ℤ) :
    HomotopyEquiv
      (integerHomogeneousComplex (k := ℤ)
        (exponentPowerFamily (finiteRowFamily n E) m) α)
      (⨁ (fun w : FiniteMultichain n E m =>
        quotientIntegerHomogeneousComplex (k := ℤ) (finiteChainCoefficientFamily n w)
          (α - integerExponent (finiteChainShift n w)))) :=
  integralIntegerPowerKoszulHomotopyEquiv hE m hm α

/-- Equation (7.1) directly on the literal integer-degree subcomplexes
of the coefficient–exterior bases. The comparison with the case-based
presentation is proved in `IntegralIntegerKoszulStrands`. -/
def theorem71_actualIntegral (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m)
    (α : FiniteVariable.{0} n →₀ ℤ) :
    HomotopyEquiv
      (actualIntegerHomogeneousComplex (k:=ℤ)
        (exponentPowerFamily (finiteRowFamily n E) m) α)
      (⨁ (fun w : FiniteMultichain n E m =>
        actualQuotientIntegerHomogeneousComplex (k:=ℤ) (finiteChainCoefficientFamily n w)
          (α-integerExponent (finiteChainShift n w)))) :=
  HomotopyEquiv.ofIso
    ((integerHomogeneousActualIso _ α).symm ≪≫ integralIntegerPowerKoszulIso hE m hm α ≪≫
      biproduct.mapIso (fun w : FiniteMultichain n E m =>
        quotientIntegerHomogeneousActualIso (finiteChainCoefficientFamily n w)
          (α-integerExponent (finiteChainShift n w))))

def integerFamilyKoszulComplex (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : FiniteVariable.{u} n →₀ ℤ) : ChainComplex (ModuleCat.{u} k[X]) ℕ :=
  integerComplexExtension (fun a => (familyStrandComplexData (k := k) m a hE).complex) α

def integerConstantFamilyComplex (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    ChainComplex (ModuleCat.{u} k[X]) ℕ :=
  integerComplexExtension (fun a => (constantChainComplexData (E := E) (k := k) m a).complex) α

/-- The family assertion in Theorem 7.1, including all auxiliary degrees and
all integer fine degrees. -/
def theorem71_familyIso (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : FiniteVariable.{u} n →₀ ℤ) :
    integerConstantFamilyComplex (E := E) (k := k) m α ≅
      integerFamilyKoszulComplex (k := k) hE m α := by
  unfold integerConstantFamilyComplex integerFamilyKoszulComplex integerComplexExtension
  split_ifs with h
  · exact integralFamilyKoszulIsoAll m (Classical.choose h) hE
  · exact Iso.refl _

def theorem71_family (hE : finiteLatticeClosed n E) (m : ℕ)
    (α : FiniteVariable.{u} n →₀ ℤ) :
    HomotopyEquiv (integerConstantFamilyComplex (E := E) (k := k) m α)
      (integerFamilyKoszulComplex (k := k) hE m α) :=
  HomotopyEquiv.ofIso (theorem71_familyIso hE m α)

/-- Equation (7.2), for every commutative ring, including the zero ring.
These are actual derived Tor modules over the polynomial ring. -/
def theorem71_baseChange (hE : finiteLatticeClosed n E) (m : ℕ) (hm : 0 < m)
    (α : FiniteVariable.{u} n →₀ ℤ) (p : ℕ) :
    ModuleCat.of k (paperIntegerGradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) α p) ≅
      ModuleCat.of k (Π₀ w : FiniteMultichain n E m,
        quotientPaperIntegerGradedTor (k := k) (finiteChainCoefficientFamily n w)
          (α - integerExponent (finiteChainShift n w)) p) :=
  integralPowerTorIso hE m hm α p

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.theorem71_integral
#print axioms FourPapers.Sublattice.theorem71_family
#print axioms FourPapers.Sublattice.theorem71_baseChange

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralSignedWeightTheorem -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-!
# The full signed-weight refinement in Theorem 7.1

The actual family is defined inside a Laurent parameter monoid algebra and
is proved free over the polynomial parameter ring. Its strand differential
is the genuine variable-multiplication Koszul differential. The only weight
hypotheses are the signed strict inequalities of the displayed monic Rees
relations. All fine degrees, including negative ones, and all nonnegative
auxiliary degrees are included.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped Polynomial
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def integerSignedFamilyKoszulComplex (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    ChainComplex (ModuleCat.{u} k[X]) ℕ :=
  integerComplexExtension
    (fun a => (signedFamilyStrandComplexData (k := k) hE ω hω m a).complex) α

/-- The signed-weight family assertion of Theorem 7.1. Over `ℤ` this is the
integral refinement; the same proved isomorphism works over every commutative
base ring, including the zero ring. -/
def theorem71_signedFamilyIso (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    integerConstantFamilyComplex (E := E) (k := k) m α ≅
      integerSignedFamilyKoszulComplex (k := k) hE ω hω m α := by
  unfold integerConstantFamilyComplex integerSignedFamilyKoszulComplex integerComplexExtension
  split_ifs with h
  · exact signedFamilyKoszulIsoAll hE ω hω m (Classical.choose h)
  · exact Iso.refl _

def theorem71_signedFamily (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    HomotopyEquiv (integerConstantFamilyComplex (E := E) (k := k) m α)
      (integerSignedFamilyKoszulComplex (k := k) hE ω hω m α) :=
  HomotopyEquiv.ofIso (theorem71_signedFamilyIso hE ω hω m α)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.theorem71_signedFamily

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralIntegerFamilyStrands -/
section

/-!
# Literal integer fine-degree strands of the signed Rees family

The integer component is defined first as the span of the actual tensor
basis vectors of that degree. Its vanishing at a negative coordinate is
proved from their exponents. The case-based extension used in the public
statement is then identified with this actual strand, including its
exterior-degree terms and its genuine Koszul differential.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped Polynomial
universe u
variable {k : Type u} [CommRing k]
  {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (hE : finiteLatticeClosed n E) (ω : FiniteReesVariable.{u} E → ℤ)
  (hω : SignedFiniteReesWeightAdmissible hE ω) (m : ℕ)

def integerFamilyStrandPredicate (α : FiniteVariable.{u} n →₀ ℤ)
    (a : FamilyTensorIndex (E:=E)) : Prop :=
  a.1.val none=m ∧ integerExponent (familyFineExponent a.1+faceExponent a.2)=α

def actualIntegerSignedFamilyTotal (α : FiniteVariable.{u} n →₀ ℤ) :
    Submodule k[X] (SignedFamilyKoszulTensorAlgebra (k:=k) hE ω hω) :=
  Submodule.span k[X] ((signedFamilyTensorBasis hE ω hω) ''
    {a | integerFamilyStrandPredicate m α a})

instance actualIntegerSignedFamilyTotalAddCommGroup (α : FiniteVariable.{u} n →₀ ℤ) :
    AddCommGroup (actualIntegerSignedFamilyTotal (k := k) hE ω hω m α) :=
  Module.addCommMonoidToAddCommGroup k[X]

def actualIntegerSignedFamilyPiece (α : FiniteVariable.{u} n →₀ ℤ) (p : ℕ) :
    Submodule k[X] (SignedFamilyKoszulTensorAlgebra (k:=k) hE ω hω) :=
  Submodule.span k[X] ((signedFamilyTensorBasis hE ω hω) ''
    {a | integerFamilyStrandPredicate m α a ∧ a.2.card=p})

theorem integerFamilyStrandPredicate_nat (a : Exponent (FiniteVariable.{u} n))
    (b : FamilyTensorIndex (E:=E)) :
    integerFamilyStrandPredicate m (integerExponent a) b↔familyStrandPredicate m a b := by
  simp only [integerFamilyStrandPredicate,familyStrandPredicate,
    integerExponent_injective.eq_iff]

theorem actualIntegerSignedFamilyTotal_nat (a : Exponent (FiniteVariable.{u} n)) :
    actualIntegerSignedFamilyTotal (k:=k) hE ω hω m (integerExponent a)=
      signedFamilyStrandTotal hE ω hω m a := by
  unfold actualIntegerSignedFamilyTotal signedFamilyStrandTotal
  simp only [integerFamilyStrandPredicate_nat]

theorem actualIntegerSignedFamilyTotal_eq_bot (α : FiniteVariable.{u} n →₀ ℤ)
    (hα : ¬∃ a,integerExponent a=α) :
    actualIntegerSignedFamilyTotal (k:=k) hE ω hω m α=⊥ := by
  unfold actualIntegerSignedFamilyTotal
  have he : {a : FamilyTensorIndex (E:=E) | integerFamilyStrandPredicate m α a}=∅ := by
    ext a
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    exact fun ha => hα ⟨familyFineExponent a.1+faceExponent a.2,ha.2⟩
  rw [he,Set.image_empty,Submodule.span_empty]

theorem actualIntegerSignedFamilyTotal_negative (α : FiniteVariable.{u} n →₀ ℤ)
    {v : FiniteVariable.{u} n} (hv : α v<0) :
    actualIntegerSignedFamilyTotal (k:=k) hE ω hω m α=⊥ := by
  apply actualIntegerSignedFamilyTotal_eq_bot hE ω hω m α
  rintro ⟨a,rfl⟩
  exact (not_lt_of_ge (integerExponent_nonneg a v)) hv

theorem actualIntegerSignedFamilyPiece_eq_bot (α : FiniteVariable.{u} n →₀ ℤ)
    (hα : ¬∃ a,integerExponent a=α) (p : ℕ) :
    actualIntegerSignedFamilyPiece (k:=k) hE ω hω m α p=⊥ := by
  apply le_antisymm _ bot_le
  rw [← actualIntegerSignedFamilyTotal_eq_bot hE ω hω m α hα]
  apply Submodule.span_mono
  exact Set.image_mono (fun _ h => h.1)

/-- Natural-degree chain groups already constructed from normal forms
are precisely the literal exterior-degree pieces in the tensor algebra. -/
theorem signedFamilyStrandComplexData_piece_image (a : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ((signedFamilyStrandComplexData (k:=k) hE ω hω m a).piece p).map
      (signedFamilyStrandTotal hE ω hω m a).subtype=
        actualIntegerSignedFamilyPiece hE ω hω m (integerExponent a) p := by
  rw [signedFamilyStrandComplexData_piece]
  unfold basisDegreePiece actualIntegerSignedFamilyPiece
  rw [Submodule.map_span,Set.image_image]
  congr 1
  ext z
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨familyFaceEmbedding m a hE b,⟨?_,hb⟩,?_⟩
    · exact (integerFamilyStrandPredicate_nat m a _).mpr (familyFaceEmbedding_mem m a hE b)
    · exact (signedFamilyStrandBasis_val hE ω hω m a b).symm
  · rintro ⟨b,⟨hb,hp⟩,rfl⟩
    have hbn := (integerFamilyStrandPredicate_nat m a b).mp hb
    obtain ⟨c,rfl⟩ := (Set.ext_iff.mp (familyFaceEmbedding_range m a hE) b).mpr hbn
    exact ⟨c,hp,signedFamilyStrandBasis_val hE ω hω m a c⟩

def signedIntegerNaturalEquiv (α : FiniteVariable.{u} n →₀ ℤ)
    (hα : ∃ a,integerExponent a=α) :
    signedFamilyStrandTotal (k:=k) hE ω hω m (Classical.choose hα) ≃ₗ[k[X]]
      actualIntegerSignedFamilyTotal (k := k) hE ω hω m α :=
  LinearEquiv.ofEq
    (signedFamilyStrandTotal (k := k) hE ω hω m (Classical.choose hα))
    (actualIntegerSignedFamilyTotal (k := k) hE ω hω m α) (by
    exact (actualIntegerSignedFamilyTotal_nat (k := k) hE ω hω m
      (Classical.choose hα)).symm.trans
        (congrArg (actualIntegerSignedFamilyTotal (k := k) hE ω hω m)
          (Classical.choose_spec hα)))

/-- Actual integer strand data. The zero branch is used only after the
underlying span has been proved to be zero; the following two theorems
identify all terms and the differential independently of this packaging. -/
def actualIntegerSignedFamilyData (α : FiniteVariable.{u} n →₀ ℤ) :
    FourPapers.SubmoduleComplexData k[X] (actualIntegerSignedFamilyTotal (k:=k) hE ω hω m α) :=
  if hα : ∃ a,integerExponent a=α then
    transportComplexData (signedFamilyStrandComplexData hE ω hω m (Classical.choose hα))
      (signedIntegerNaturalEquiv hE ω hω m α hα)
  else
    { piece := fun _ => ⊥
      d := 0
      square_zero := by simp
      lowers := fun _ _ _ => Submodule.zero_mem _ }

theorem actualIntegerSignedFamilyData_d (α : FiniteVariable.{u} n →₀ ℤ)
    (z : actualIntegerSignedFamilyTotal (k:=k) hE ω hω m α) :
    ((actualIntegerSignedFamilyData hE ω hω m α).d z).val=
      signedFamilyKoszulDifferential hE ω hω z.val := by
  unfold actualIntegerSignedFamilyData
  split_ifs with hα
  · change (((signedIntegerNaturalEquiv hE ω hω m α hα)
      ((signedFamilyStrandComplexData hE ω hω m (Classical.choose hα)).d
        ((signedIntegerNaturalEquiv hE ω hω m α hα).symm z)))).val=_
    change ((signedFamilyStrandComplexData hE ω hω m (Classical.choose hα)).d
      ((signedIntegerNaturalEquiv hE ω hω m α hα).symm z)).val=_
    rw [signedFamilyStrandComplexData_d]
    rfl
  · have hz : z.val=0 := by
      have hz' : z.val ∈ (⊥ : Submodule k[X]
          (SignedFamilyKoszulTensorAlgebra (k := k) hE ω hω)) := by
        simpa only [actualIntegerSignedFamilyTotal_eq_bot hE ω hω m α hα] using z.property
      exact hz'
    simp only [LinearMap.zero_apply,ZeroMemClass.coe_zero,hz,map_zero]

theorem actualIntegerSignedFamilyData_piece (α : FiniteVariable.{u} n →₀ ℤ) (p : ℕ) :
    ((actualIntegerSignedFamilyData (k:=k) hE ω hω m α).piece p).map
      (actualIntegerSignedFamilyTotal hE ω hω m α).subtype=
        actualIntegerSignedFamilyPiece hE ω hω m α p := by
  unfold actualIntegerSignedFamilyData
  split_ifs with hα
  · change (((signedFamilyStrandComplexData hE ω hω m (Classical.choose hα)).piece p).map
      (signedIntegerNaturalEquiv hE ω hω m α hα).toLinearMap).map _=_
    rw [← Submodule.map_comp]
    have he : (actualIntegerSignedFamilyTotal (k := k) hE ω hω m α).subtype.comp
        (signedIntegerNaturalEquiv (k := k) hE ω hω m α hα).toLinearMap=
      (signedFamilyStrandTotal (k := k) hE ω hω m (Classical.choose hα)).subtype := by
      apply LinearMap.ext
      intro x
      rfl
    rw [he,signedFamilyStrandComplexData_piece_image,Classical.choose_spec hα]
  · rw [actualIntegerSignedFamilyPiece_eq_bot hE ω hω m α hα p]
    exact Submodule.map_bot _

def integerSignedFamilyActualIso (α : FiniteVariable.{u} n →₀ ℤ) :
    integerSignedFamilyKoszulComplex (k:=k) hE ω hω m α ≅
      (actualIntegerSignedFamilyData hE ω hω m α).complex := by
  unfold integerSignedFamilyKoszulComplex integerComplexExtension actualIntegerSignedFamilyData
  split_ifs with hα
  · exact transportComplexIso
      (signedFamilyStrandComplexData hE ω hω m (Classical.choose hα))
      (signedIntegerNaturalEquiv hE ω hω m α hα)
  · apply (isZero_zero _).iso
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact z.property

/-- The signed-weight refinement with its target now the actual integer
fine/auxiliary Koszul strand, whose terms and differential are identified
above by literal basis degrees and variable multiplication. -/
def theorem71_actualSignedFamily (α : FiniteVariable.{u} n →₀ ℤ) :
    HomotopyEquiv (integerConstantFamilyComplex (E:=E) (k:=k) m α)
      (actualIntegerSignedFamilyData (k:=k) hE ω hω m α).complex :=
  HomotopyEquiv.ofIso
    (theorem71_signedFamilyIso hE ω hω m α ≪≫ integerSignedFamilyActualIso hE ω hω m α)

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralConstantFamilyStrands -/
section

/-!
# The literal constant complex in the integral family comparison

The constant matrix is identified with the direct sum of the actual
coefficient-quotient Koszul complexes over the parameter ring. In particular,
neither side of the final family equivalence is specified merely by extending
a definition by zero. All integer fine degrees and auxiliary degree zero are
included. The matrix comparison below uses the actual integral exterior signs.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped Polynomial
universe u
variable {k : Type u} [CommRing k]
  {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

/-- The coefficients of the special differential are literal integral
exterior signs, so polynomial extension gives the same differential. -/
theorem chainSpecialMatrix_polynomial :
    (chainSpecialMatrix (E:=E) (k:=k) m α).map Polynomial.C=
      chainSpecialMatrix (E:=E) (k:=k[X]) m α := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply,chainSpecialMatrix,LinearMap.toMatrix_apply,
    chainTotalSpecialDifferential_basis,map_sum,Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hq
  · simp only [map_zsmul_unit,Finsupp.smul_apply,Module.Basis.repr_self,
      Finsupp.single_apply]
    split_ifs <;> simp
  · simp

def constantChainTotalData : FourPapers.SubmoduleComplexData k[X]
    (ChainTotalModule n E m α k[X]) :=
  FourPapers.dfinsuppComplexData (fun w : AdmissibleChain n E m α =>
    quotientTotalData (k:=k[X]) (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val))

theorem constantChainTotalData_piece (p : ℕ) (x : ChainTotalModule n E m α k[X]) :
    x∈(constantChainTotalData (E:=E) (k:=k) m α).piece p ↔
      x∈chainTotalPiece n E m α k[X] p := by
  change x∈FourPapers.dfinsuppPiece _ ↔ _
  rw [FourPapers.mem_dfinsuppPiece,chainTotalPiece_iff]
  rfl

/-- Coordinates of the actual finite direct sum, with its actual exterior
degrees and its block quotient differential. -/
def constantChainCoordinateIso :
    (constantChainTotalData (E:=E) (k:=k) m α).complex ≅
      (constantChainComplexData (E:=E) (k:=k) m α).complex := by
  let b := chainTotalBasis n E m α k[X]
  let c := Pi.basisFun k[X] (ChainFaceIndex n E m α)
  have hb (a : ChainFaceIndex n E m α) : b.equivFun (b a)=c a := by
    apply _root_.funext
    intro j
    rw [Module.Basis.equivFun_self]
    change (if a = j then (1 : k[X]) else 0) =
      Pi.basisFun k[X] (ChainFaceIndex n E m α) a j
    rw [Pi.basisFun_apply]
    by_cases h : a = j
    · subst j
      simp
    · simp [h, Ne.symm h, Pi.single_eq_of_ne]
  have hi (a : ChainFaceIndex n E m α) : b.equivFun.symm (c a)=b a := by
    rw [← hb,b.equivFun.symm_apply_apply]
  apply FourPapers.SubmoduleComplexData.isoOfTotal _ _ b.equivFun
  · intro p x hx
    apply FourPapers.map_mem_piece_of_basis b c
      (chainMatrixDegree m α) (chainMatrixDegree m α) b.equivFun.toLinearMap
      (fun a => ?_) p ((constantChainTotalData_piece m α p x).mp hx)
    rw [LinearEquiv.coe_coe,hb]
    exact Submodule.subset_span ⟨a,rfl,rfl⟩
  · intro p x hx
    apply (constantChainTotalData_piece m α p _).mpr
    apply FourPapers.map_mem_piece_of_basis c b
      (chainMatrixDegree m α) (chainMatrixDegree m α) b.equivFun.symm.toLinearMap
      (fun a => ?_) p hx
    rw [LinearEquiv.coe_coe,hi]
    exact Submodule.subset_span ⟨a,rfl,rfl⟩
  · apply LinearMap.ext
    intro x
    apply _root_.funext
    intro j
    change (((chainSpecialMatrix (E:=E) (k:=k) m α).map Polynomial.C).mulVec
      (b.repr x)) j=(b.repr (chainTotalSpecialDifferential n E m α k[X] x)) j
    rw [chainSpecialMatrix_polynomial]
    exact congrFun (LinearMap.toMatrix_mulVec_repr b b
      (chainTotalSpecialDifferential n E m α k[X]) x) j

def constantChainQuotientIso :
    (constantChainComplexData (E:=E) (k:=k) m α).complex ≅
      ⨁ (fun w : AdmissibleChain n E m α =>
        quotientHomogeneousComplex (k:=k[X]) (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)) :=
  (constantChainCoordinateIso (E:=E) (k:=k) m α).symm ≪≫
  FourPapers.dfinsuppComplexIso (fun w : AdmissibleChain n E m α =>
    quotientTotalData (k:=k[X]) (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)) ≪≫
  FourPapers.finiteDirectSumBiproductIso (fun w : AdmissibleChain n E m α =>
    (quotientTotalData (k:=k[X]) (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val)).complex) ≪≫
  biproduct.mapIso (fun w : AdmissibleChain n E m α =>
    quotientTotalKoszulIso (k:=k[X]) (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val))

/-- Every multichain occurs in the constant family. Nonadmissible shifts
are removed only after the actual quotient strand is proved to be zero. -/
def integerConstantFamilyQuotientIso (β : FiniteVariable.{u} n →₀ ℤ) :
    integerConstantFamilyComplex (E:=E) (k:=k) m β ≅
      ⨁ (fun w : FiniteMultichain n E m =>
        quotientIntegerHomogeneousComplex (k:=k[X]) (finiteChainCoefficientFamily n w)
          (β-integerExponent (finiteChainShift n w))) := by
  by_cases hβ : ∀v,0≤β v
  · let hex := (integerExponent_exists_iff β).mpr hβ
    let a := Classical.choose hex
    have ha : integerExponent a=β := Classical.choose_spec hex
    rw [← ha]
    let F := fun w : FiniteMultichain n E m =>
      quotientIntegerHomogeneousComplex (k:=k[X]) (finiteChainCoefficientFamily n w)
        (integerExponent a-integerExponent (finiteChainShift n w))
    let e := biproductZeroExtensionIso F (fun w => finiteChainShift n w≤a) (by
      intro w hw
      dsimp [F]
      rw [quotientIntegerHomogeneousComplex_shift_zero _ _ _ hw]
      exact isZero_zero _)
    exact eqToIso (integerComplexExtension_nat _ _) ≪≫
      constantChainQuotientIso m a ≪≫
      biproduct.mapIso (fun w : AdmissibleChain n E m a =>
        eqToIso (quotientIntegerHomogeneousComplex_shift
          (finiteChainCoefficientFamily n w.val) a (finiteChainShift n w.val) w.property).symm) ≪≫ e
  · have hex : ∃v,β v<0 := by simpa only [not_forall,not_le] using hβ
    let v := Classical.choose hex
    have hv : β v<0 := Classical.choose_spec hex
    have hl : IsZero (integerConstantFamilyComplex (E:=E) (k:=k) m β) := by
      dsimp [integerConstantFamilyComplex]
      rw [integerComplexExtension_negative _ β hv]
      exact isZero_zero _
    have hr (w : FiniteMultichain n E m) : IsZero
        (quotientIntegerHomogeneousComplex (k:=k[X]) (finiteChainCoefficientFamily n w)
          (β-integerExponent (finiteChainShift n w))) := by
      dsimp [quotientIntegerHomogeneousComplex]
      rw [integerComplexExtension_negative _ _ (v:=v) (by
        change β v-((finiteChainShift n w) v:ℤ)<0
        exact (sub_le_self _ (Int.ofNat_nonneg _)).trans_lt hv)]
      exact isZero_zero _
    apply hl.iso
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro w
    exact (hr w).eq_of_tgt _ _

/-- The literal direct sum of polynomial-quotient Koszul strands in the
constant family. Every term is defined by its actual integer basis degree. -/
def actualConstantFamilyComplex (β : FiniteVariable.{u} n →₀ ℤ) :
    ChainComplex (ModuleCat.{u} k[X]) ℕ :=
  ⨁ (fun w : FiniteMultichain n E m =>
    actualQuotientIntegerHomogeneousComplex (k:=k[X]) (finiteChainCoefficientFamily n w)
      (β-integerExponent (finiteChainShift n w)))

def integerConstantFamilyActualIso (β : FiniteVariable.{u} n →₀ ℤ) :
    integerConstantFamilyComplex (E:=E) (k:=k) m β ≅
      actualConstantFamilyComplex (E:=E) (k:=k) m β :=
  integerConstantFamilyQuotientIso m β ≪≫
    biproduct.mapIso (fun w : FiniteMultichain n E m =>
      quotientIntegerHomogeneousActualIso (k:=k[X]) (finiteChainCoefficientFamily n w)
        (β-integerExponent (finiteChainShift n w)))

/-- Full Theorem 7.1 family refinement with both sides identified as literal
Koszul complexes. This includes arbitrary commutative coefficients, arbitrary
admissible signed weights, all integer fine degrees, and auxiliary degree zero. -/
def theorem71_literalSignedFamily (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (β : FiniteVariable.{u} n →₀ ℤ) :
    HomotopyEquiv (actualConstantFamilyComplex (E:=E) (k:=k) m β)
      (actualIntegerSignedFamilyData (k:=k) hE ω hω m β).complex :=
  HomotopyEquiv.ofIso ((integerConstantFamilyActualIso m β).symm ≪≫
    theorem71_signedFamilyIso hE ω hω m β ≪≫ integerSignedFamilyActualIso hE ω hω m β)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.theorem71_actualIntegral
#print axioms FourPapers.Sublattice.theorem71_baseChange
#print axioms FourPapers.Sublattice.theorem71_literalSignedFamily
#print axioms FourPapers.Sublattice.actualIntegerSignedFamilyData_d
#print axioms FourPapers.Sublattice.actualIntegerSignedFamilyData_piece

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem71ArbitraryFamily -/
section

/-!
# Theorem 7.1 for the literal weight-homogenized generator image

The hypothesis is the signed-weight initial-ideal equality for the
original polynomial Rees presentation. It implies admissibility by a
proved theorem. The target below uses the actual weighted-generator
image, and its differential is proved to be multiplication by the
original base variables followed by exterior contraction.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped Polynomial TensorProduct

universe u
variable {k : Type u} [CommRing k]
  {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  (hE : finiteLatticeClosed n E) (ω : FiniteReesVariable.{u} E → ℤ)
  (hω : SignedFiniteReesWeightAdmissible hE ω)

/-- The identification is the identity on actual Laurent polynomials.
Explicit subtype maps keep all inherited coefficient structures fixed. -/
def literalFamilyEquiv :
    signedReesFamily (k := k) hE ω hω ≃ₐ[k[X]]
      LiteralWeightFamily.family (k := k) (finitePresentedHom E) ω where
  toFun x := ⟨x.val, by rw [literalReesFamily_eq_signedReesFamily hE ω hω]; exact x.property⟩
  invFun x := ⟨x.val, by rw [← literalReesFamily_eq_signedReesFamily hE ω hω]; exact x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def literalFamilyBaseVariable (v : FiniteVariable.{u} n) :
    LiteralWeightFamily.family (k := k) (finitePresentedHom E) ω :=
  (LiteralWeightFamily.presentationMap (k := k) (finitePresentedHom E) ω).rangeRestrict
    (MvPolynomial.X (Sum.inl v))

theorem signedStandardWeight_baseVariable (v : FiniteVariable.{u} n) :
    signedStandardWeight hE ω (familyBaseIndex (E := E) v) = ω (Sum.inl v) := by
  have hc : finiteCanonicalExponent hE (familyBaseIndex (E := E) v) =
      Finsupp.single (Sum.inl v) 1 := by
    apply finiteReesStandard_image_injective hE
      (finiteCanonicalExponent_standard hE _) (familyBaseIndex_standard hE v)
    exact finiteCanonicalExponent_image hE _
  rw [signedStandardWeight,hc,Finsupp.weight_single,one_nsmul]

theorem literalFamilyBaseVariable_val (v : FiniteVariable.{u} n) :
    (signedFamilyBaseVariable (k := k) hE ω hω v).val =
      (literalFamilyBaseVariable (k := k) ω v).val := by
  change (signedFamilyBaseVariable (k := k) hE ω hω v).val =
    LiteralWeightFamily.presentationMap (finitePresentedHom E) ω (MvPolynomial.X (Sum.inl v))
  rw [LiteralWeightFamily.presentationMap,MvPolynomial.aeval_X]
  calc
    _ = signedWeightedMonomial (k := k) (signedStandardWeight hE ω) (familyBaseIndex v) :=
      signedWeightedMonoidBasis_val (signedStandardWeight hE ω)
        (signedStandardWeight_zero hE ω) (signedStandardWeight_subadd hE ω hω) _
    _ = _ := by
      rw [signedWeightedMonomial, signedStandardWeight_baseVariable]
      rfl

theorem literalFamilyEquiv_baseVariable (v : FiniteVariable.{u} n) :
    literalFamilyEquiv (k := k) hE ω hω (signedFamilyBaseVariable hE ω hω v) =
      literalFamilyBaseVariable (k := k) ω v := by
  apply Subtype.ext
  exact literalFamilyBaseVariable_val (k := k) hE ω hω v

/-- The same value-preserving identification with its linear structure
recorded directly, for tensor-coordinate transport. -/
def literalFamilyLinearEquiv :
    signedReesFamily (k := k) hE ω hω ≃ₗ[k[X]]
      LiteralWeightFamily.family (k := k) (finitePresentedHom E) ω where
  toFun x := ⟨x.val, by rw [literalReesFamily_eq_signedReesFamily hE ω hω]; exact x.property⟩
  invFun x := ⟨x.val, by rw [← literalReesFamily_eq_signedReesFamily hE ω hω]; exact x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem literalFamilyLinearEquiv_base_mul (v : FiniteVariable.{u} n)
    (a : signedReesFamily (k := k) hE ω hω) :
    literalFamilyLinearEquiv hE ω hω (signedFamilyBaseVariable hE ω hω v * a) =
      literalFamilyBaseVariable (k := k) ω v * literalFamilyLinearEquiv hE ω hω a := by
  apply Subtype.ext
  change (signedFamilyBaseVariable (k := k) hE ω hω v).val * a.val =
    (literalFamilyBaseVariable (k := k) ω v).val * a.val
  exact congrArg (fun z : AddMonoidAlgebra (LaurentPolynomial k)
      (finiteReesExponentMonoid.{u} E) => z * a.val)
    (literalFamilyBaseVariable_val (k := k) hE ω hω v)

attribute [local irreducible] literalFamilyEquiv literalFamilyLinearEquiv

abbrev LiteralFamilyTensor :=
  LiteralWeightFamily.family (k := k) (finitePresentedHom E) ω ⊗[k[X]]
    Simplicial.Ambient (FiniteVariable.{u} n) k[X]

def literalFamilyTensorEquiv :
    SignedFamilyKoszulTensorAlgebra (k := k) hE ω hω ≃ₗ[k[X]]
      LiteralFamilyTensor (k := k) (E := E) ω :=
  TensorProduct.congr (literalFamilyLinearEquiv hE ω hω) (LinearEquiv.refl _ _)

def literalFamilyKoszulDifferential : Module.End k[X]
    (LiteralFamilyTensor (k := k) (E := E) ω) :=
  ∑ v : FiniteVariable.{u} n,
    TensorProduct.map (LinearMap.mulLeft k[X] (literalFamilyBaseVariable (k := k) ω v))
      (Simplicial.contraction v)

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency true in
theorem literalFamilyTensorEquiv_d
    (x : SignedFamilyKoszulTensorAlgebra (k := k) hE ω hω) :
    literalFamilyTensorEquiv hE ω hω (signedFamilyKoszulDifferential hE ω hω x) =
      literalFamilyKoszulDifferential ω (literalFamilyTensorEquiv hE ω hω x) := by
  have he := TensorMultiplicationNaturality.linear_congr_differential
    (S := k[X]) (U := signedReesFamily (k := k) hE ω hω)
    (W := LiteralWeightFamily.family (k := k) (finitePresentedHom E) ω)
    (E := Simplicial.Ambient (FiniteVariable.{u} n) k[X]) (V := FiniteVariable.{u} n)
    (literalFamilyLinearEquiv (k := k) hE ω hω)
    (fun v => LinearMap.mulLeft k[X] (signedFamilyBaseVariable (k := k) hE ω hω v))
    (fun v => LinearMap.mulLeft k[X] (literalFamilyBaseVariable (k := k) ω v))
    (fun v => Simplicial.contraction (k := k[X]) v)
    (literalFamilyLinearEquiv_base_mul (k := k) hE ω hω) x
  simpa only [literalFamilyTensorEquiv, signedFamilyKoszulDifferential,
    literalFamilyKoszulDifferential] using he

def literalFamilyTensorBasis : Module.Basis (FamilyTensorIndex (E := E)) k[X]
    (LiteralFamilyTensor (k := k) (E := E) ω) :=
  (signedFamilyTensorBasis hE ω hω).map (literalFamilyTensorEquiv hE ω hω)

def literalIntegerFamilyTotal (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    Submodule k[X] (LiteralFamilyTensor (k := k) (E := E) ω) :=
  (actualIntegerSignedFamilyTotal hE ω hω m α).map
    (literalFamilyTensorEquiv hE ω hω).toLinearMap

instance literalIntegerFamilyTotalAddCommGroup
    (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    AddCommGroup (literalIntegerFamilyTotal (k := k) hE ω hω m α) :=
  Module.addCommMonoidToAddCommGroup k[X]

theorem literalIntegerFamilyTotal_eq_span (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    literalIntegerFamilyTotal (k := k) hE ω hω m α =
      Submodule.span k[X] ((literalFamilyTensorBasis hE ω hω) ''
        {a | integerFamilyStrandPredicate m α a}) := by
  rw [literalIntegerFamilyTotal,actualIntegerSignedFamilyTotal,Submodule.map_span,
    Set.image_image]
  rfl

def literalIntegerFamilyEquiv (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    actualIntegerSignedFamilyTotal (k := k) hE ω hω m α ≃ₗ[k[X]]
      literalIntegerFamilyTotal (k := k) hE ω hω m α :=
  (literalFamilyTensorEquiv hE ω hω).submoduleMap
    (actualIntegerSignedFamilyTotal hE ω hω m α)

def literalIntegerFamilyData (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    FourPapers.SubmoduleComplexData k[X]
      (literalIntegerFamilyTotal (k := k) hE ω hω m α) :=
  transportComplexData (actualIntegerSignedFamilyData hE ω hω m α)
    (literalIntegerFamilyEquiv hE ω hω m α)

theorem literalIntegerFamilyData_d (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ)
    (x : literalIntegerFamilyTotal (k := k) hE ω hω m α) :
    ((literalIntegerFamilyData hE ω hω m α).d x).val =
      literalFamilyKoszulDifferential ω x.val := by
  change literalFamilyTensorEquiv hE ω hω
    (((actualIntegerSignedFamilyData hE ω hω m α).d
      ((literalIntegerFamilyEquiv hE ω hω m α).symm x)).val) = _
  rw [actualIntegerSignedFamilyData_d,literalFamilyTensorEquiv_d]
  apply congrArg (literalFamilyKoszulDifferential (k := k) (E := E) ω)
  exact congrArg Subtype.val ((literalIntegerFamilyEquiv hE ω hω m α).apply_symm_apply x)

theorem literalIntegerFamilyData_piece (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ)
    (p : ℕ) :
    ((literalIntegerFamilyData (k := k) hE ω hω m α).piece p).map
      (literalIntegerFamilyTotal hE ω hω m α).subtype =
      Submodule.span k[X] ((literalFamilyTensorBasis hE ω hω) ''
        {a | integerFamilyStrandPredicate m α a ∧ a.2.card = p}) := by
  change (((actualIntegerSignedFamilyData hE ω hω m α).piece p).map
    (literalIntegerFamilyEquiv hE ω hω m α).toLinearMap).map _ = _
  rw [← Submodule.map_comp]
  have he : (literalIntegerFamilyTotal (k := k) hE ω hω m α).subtype.comp
      (literalIntegerFamilyEquiv (k := k) hE ω hω m α).toLinearMap =
      (literalFamilyTensorEquiv (k := k) hE ω hω).toLinearMap.comp
        (actualIntegerSignedFamilyTotal (k := k) hE ω hω m α).subtype := rfl
  rw [he,Submodule.map_comp,actualIntegerSignedFamilyData_piece,
    actualIntegerSignedFamilyPiece,Submodule.map_span,Set.image_image]
  rfl

set_option maxHeartbeats 100000 in
/-- The coefficient-value identification induces an actual chain isomorphism. -/
def literalIntegerFamilyComplexIso (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    (actualIntegerSignedFamilyData (k := k) hE ω hω m α).complex ≅
      (literalIntegerFamilyData (k := k) hE ω hω m α).complex := by
  let e := literalIntegerFamilyEquiv (k := k) hE ω hω m α
  exact transportComplexIso (actualIntegerSignedFamilyData (k := k) hE ω hω m α) e

/-- The parameter-family clause of Theorem 7.1 on the actual generator
image, for every admissible signed weight and every integer strand. -/
def theorem71_generatorFamily (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    HomotopyEquiv (actualConstantFamilyComplex (E := E) (k := k) m α)
      (literalIntegerFamilyData hE ω hω m α).complex := by
  let h := theorem71_literalSignedFamily (k := k) m hE ω hω α
  let e := HomotopyEquiv.ofIso (literalIntegerFamilyComplexIso (k := k) hE ω hω m α)
  exact h.trans e

/-- The exact signed initial-ideal hypothesis of the paper, with no
admissibility, positivity, or field assumption added. -/
def theorem71_arbitraryWeightFamily
    (hB : SignedWeightInitial.initialIdeal ω
      (RingHom.ker (finiteReesPresentationMap E ℤ).toRingHom) = finiteReesInitialIdeal ℤ E)
    (m : ℕ) (α : FiniteVariable.{u} n →₀ ℤ) :
    HomotopyEquiv (actualConstantFamilyComplex (E := E) (k := k) m α)
      (literalIntegerFamilyData hE ω (signedAdmissible_of_weightInitialIdeal hE ω hB) m α).complex :=
  theorem71_generatorFamily hE ω (signedAdmissible_of_weightInitialIdeal hE ω hB) m α

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.literalIntegerFamilyData_d
#print axioms FourPapers.Sublattice.literalIntegerFamilyData_piece
#print axioms FourPapers.Sublattice.theorem71_arbitraryWeightFamily


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.Theorem12 -/
section

/-!
# The two assertions of Theorem 1.2 in one statement

The Betti formula ranges over every integer fine degree and every multichain,
including repetitions. The second conjunct is generation of the actual
Rees-image Koszul homology algebra by actual Rees-degree-one classes.
The two conclusions share the same literal ideal-power and grading
identifications established in the imported supporting modules.
-/

section
set_option autoImplicit false
noncomputable section

namespace FourPapers.Sublattice

open CommAlg CommAlg.Koszul CommAlg.Polymatroid

universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
  {K : Type u} [Field K]

/-- Both conclusions of Theorem 1.2, including its
multiplicative conclusion, for an arbitrary field. -/
theorem theorem12 (hE : finiteLatticeClosed n E) :
    (∀ (m : ℕ),0< m→∀ (p : ℕ) (α : FiniteVariable.{u} n →₀ ℤ),
      integerBettiNumber (k:=K) (exponentPowerFamily (finiteRowFamily n E) m) α p=
        ∑ w : FiniteMultichain n E m,
          quotientIntegerBettiNumber (k:=K) (finiteChainCoefficientFamily n w)
            (α-integerExponent (finiteChainShift n w)) p) ∧
      Algebra.adjoin K (actualFirstReesClasses (k:=K) hE)=⊤ := by
  exact ⟨fun m hm p α => allPowersIntegerBettiFormula hE K m hm p α,
    reesKoszulHomology_generated_in_degree_one hE⟩

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PowerHomologyClasses -/
section

/-! # Literal product classes and their degree-zero factors

The maps into the Rees homology detect precisely the boundary range in their
own fine component. Degree-zero exterior cycles are scalars in the exterior
algebra, so their Rees classes are central. These facts justify removing such
factors from an ordered nonzero product without assuming commutativity of the
remaining Koszul classes.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

section Ring
variable {k : Type u} [CommRing k]

lemma reesHomologyPieceMap_eq_zero_iff (hE : finiteLatticeClosed n E)
    (g : ReesFineDegree.{u} n)
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) g.1 g.2)) :
    reesHomologyPieceMap (k := k) hE g z = 0 ↔
      z.val ∈ LinearMap.range (powerFaceDifferential g.1 g.2) := by
  change (reesKoszulCoordinateDifferential (k := k) hE).classMap
    (reesCycleSingle hE g z) = 0 ↔ _
  rw [ParityDifferential.classMap_eq_zero]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨reesKoszulCoefficient hE g y, ?_⟩
    rw [reesKoszulCoefficient_differential, hy]
    apply Subtype.ext
    change (AddMonoidAlgebra.single g z.val.val).coeff g = z.val.val
    simp
  · rintro ⟨y, hy⟩
    refine ⟨reesKoszulSingle hE g y, ?_⟩
    rw [reesKoszulSingle_differential, hy]
    rfl

lemma reesHomologyPieceMap_product (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n))
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α))
    (β : Fin m → Exponent (FiniteVariable.{u} n))
    (x : ∀ i, LinearMap.ker (powerFaceDifferential (E := E) (k := k) 1 (β i)))
    (hβ : (∑ i, β i) = α)
    (hz : z.val.val = (List.ofFn (fun i => (x i).val.val)).prod) :
    reesHomologyPieceMap (k := k) hE (m, α) z =
      (List.ofFn (fun i => reesHomologyPieceMap (k := k) hE (1, β i) (x i))).prod := by
  let y (i : Fin m) := reesCycleSingle (k := k) hE (1, β i) (x i)
  have he : reesCycleSingle (k := k) hE (m, α) z = (List.ofFn y).prod := by
    apply Subtype.ext
    apply Subtype.ext
    let v := (reesKoszulCoordinateAlgebra (k := k) hE).val.comp
      (reesKoszulCoordinateDifferential (k := k) hE).cycles.val
    change AddMonoidAlgebra.single (m, α) z.val.val = v ((List.ofFn y).prod)
    rw [map_list_prod, List.map_ofFn]
    change AddMonoidAlgebra.single (m, α) z.val.val =
      (List.ofFn (fun i => AddMonoidAlgebra.single (1, β i) (x i).val.val)).prod
    rw [rees_single_list_prod, hβ, hz]
  change (reesKoszulCoordinateDifferential (k := k) hE).classMap
      (reesCycleSingle hE (m, α) z) = _
  rw [he, map_list_prod, List.map_ofFn]
  rfl

def firstPowerCycleProduct (hE : finiteLatticeClosed n E) (m : ℕ)
    (β : Fin m → Exponent (FiniteVariable.{u} n))
    (x : ∀ i, LinearMap.ker (powerFaceDifferential (E := E) (k := k) 1 (β i))) :
    LinearMap.ker (powerFaceDifferential (E := E) (k := k) m (∑ i, β i)) :=
  ⟨⟨(List.ofFn (fun i => (x i).val.val)).prod,
    idealPowerFace_list_mul_mem hE m β (fun i => (x i).val.val)
      (fun i => (x i).val.property)⟩, by
    apply Subtype.ext
    apply boundary_list_product_eq_zero
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact congrArg Subtype.val (x i).property⟩

lemma firstPowerCycleProduct_degree (hE : finiteLatticeClosed n E) (m : ℕ)
    (β : Fin m → Exponent (FiniteVariable.{u} n))
    (x : ∀ i, LinearMap.ker (powerFaceDifferential (E := E) (k := k) 1 (β i)))
    (degree : Fin m → ℕ)
    (hx : ∀ i, (x i).val ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) (β i)) (degree i)) :
    (firstPowerCycleProduct hE m β x).val ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) (∑ i, β i))
        (∑ i, degree i) := by
  apply faceDegree_of_support _ _ (firstPowerCycleProduct hE m β x).val.property
  exact faceDegree_ordered_product m degree (fun i => (x i).val.val)
    (fun i => faceDegree_forget _ _ (hx i))

lemma exterior_degree_zero_scalar {V : Type u} [Fintype V] [LinearOrder V]
    (P : Finset V → Prop) (z : TotalFaceModule (k := k) P)
    (hz : z ∈ totalFacePiece P 0) :
    ∃ c : k, z.val = c • (1 : Simplicial.Ambient V k) := by
  have h : z.val ∈ Submodule.span k ({1} : Set (Simplicial.Ambient V k)) := by
    apply Submodule.span_le.mpr ?_ hz
    rintro y ⟨F, ⟨_, hF⟩, rfl⟩
    have he : F = ∅ := Finset.card_eq_zero.mp hF
    rw [he, faceBasis_empty]
    exact Submodule.subset_span (Set.mem_singleton 1)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  exact ⟨c, hc.symm⟩

lemma reesHomologyPieceMap_zero_degree_central (hE : finiteLatticeClosed n E)
    (g : ReesFineDegree.{u} n)
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) g.1 g.2))
    (hz : z.val ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) g.1) g.2) 0)
    (w : ReesKoszulCoordinateHomology (k := k) hE) :
    Commute (reesHomologyPieceMap (k := k) hE g z) w := by
  obtain ⟨c, hc⟩ := exterior_degree_zero_scalar _ z.val hz
  obtain ⟨y, rfl⟩ := (reesKoszulCoordinateDifferential (k := k) hE).classMap_surjective w
  have hcentral : Commute (reesCycleSingle (k := k) hE g z) y := by
    apply Subtype.ext
    apply Subtype.ext
    change Commute (AddMonoidAlgebra.single g z.val.val) y.val.val
    apply AddMonoidAlgebra.single_commute (AddCommute.all g)
    intro a
    rw [hc]
    change (c • (1 : Simplicial.Ambient (FiniteVariable.{u} n) k)) * a =
      a * (c • (1 : Simplicial.Ambient (FiniteVariable.{u} n) k))
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  exact hcentral.map (reesKoszulCoordinateDifferential (k := k) hE).classMap

end Ring

section Field
variable {k : Type u} [Field k]

theorem powerBetti_nonzero_of_class (hE : finiteLatticeClosed n E)
    (m : ℕ) (α : Exponent (FiniteVariable.{u} n)) (p : ℕ)
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) m α))
    (hz : z.val ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) p)
    (hclass : reesHomologyPieceMap (k := k) hE (m, α) z ≠ 0) :
    bettiNumber (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α p ≠ 0 := by
  apply Nat.ne_of_gt
  apply (bettiNumber_pos_iff_faces _ α p).mpr
  refine ⟨z.val.val, hz, congrArg Subtype.val z.property, ?_⟩
  intro y hy he
  apply hclass
  apply (reesHomologyPieceMap_eq_zero_iff hE (m, α) z).mpr
  exact ⟨⟨y, chains_mem_basisSpan hy⟩, Subtype.ext he⟩

theorem firstPowerClass_zero_degree_internal (hE : finiteLatticeClosed n E)
    (α : Exponent (FiniteVariable.{u} n))
    (z : LinearMap.ker (powerFaceDifferential (E := E) (k := k) 1 α))
    (hz : z.val ∈ totalFacePiece
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) α) 0)
    (hclass : reesHomologyPieceMap (k := k) hE (1, α) z ≠ 0) : α.degree = d := by
  apply monomial_zero_betti_degree (exponentPowerFamily (finiteRowFamily n E) 1) d
    (fun a ha => ?_) α (powerBetti_nonzero_of_class hE 1 α 0 z hz hclass)
  obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
  have hb0 : b = 0 := by simpa only [exponentPowerFamily, Finset.mem_singleton] using hb
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
  simp only [hb0, zero_add, finiteRowExponent_degree]

end Field
end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.reesHomologyPieceMap_eq_zero_iff
#print axioms FourPapers.Sublattice.firstPowerClass_zero_degree_internal

end
end
end


end
