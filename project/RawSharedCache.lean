module
prelude
public import RawIncidenceRows
public import EdgeDisagreementRows
public import ProperFaceComplementRows
public import RawFacetEmbedding

@[expose] public section

/-!
# Shared literal cache for a complete rooted facet universe

Only actual incidences are listed in the transpose certificates. Incompatibility
is justified by the short proper-face list and induced-edge disagreement.
Neither a quadratic compatibility table nor a completeness assertion about an
external search is assumed. The exhaustive node checker still checks that its
listed branches cover every candidate that these sound rows do not exclude.
-/

namespace Papers.RationalityTen.RawSharedCache

open ConcreteGrowth GrowthDAG GrowthBitsets BatchedGrowthPruning FiniteMaskSets
open RawGrowthCacheCertificate RawNatGrowthSoundness RawIncidenceRows

structure Data (n : Nat) where
  cells : Nat → Cell
  candidates : Nat → Nat
  candidateSupports : Nat → List Nat
  edges : Nat → Nat
  edgeSupports : Nat → List Nat
  vertices : Nat → Nat
  kinds : Nat → Nat
  kindSupports : Nat → List Nat
  keys : List Nat
  fastKind : Nat → Nat
  missing : Nat → List Nat
  bad : Nat → Nat

def finiteCells {n : Nat} (D : Data n) (c : Fin n) : Cell := D.cells c.val

structure Facts {n : Nat} (D : Data n) : Prop where
  wellFormed : ∀ c : Fin n, RawFacetEmbedding.wellFormedCheck (D.cells c.val) = true
  edgeWithin : ∀ c : Fin n, ∀ e, e ∈ (D.cells c.val).edges →
    Nat.land e (D.cells c.val).vertices = e
  vertexExact : ∀ v : Fin 10, ∀ c : Fin n,
    (D.vertices v.val).testBit c.val = (D.cells c.val).vertices.testBit v.val
  candidateMasks : ∀ q : Fin 1024,
    D.candidates q.val = RawNatGrowthCheck.mask (D.candidateSupports q.val)
  candidateCoverage : ∀ c : Fin n,
    (D.cells c.val).ridgeMasks.all (fun q => (D.candidates q).testBit c.val) = true
  candidateSound : ∀ q : Fin 1024,
    (D.candidateSupports q.val).all (fun c => hasNat (D.cells c).ridgeMasks q.val) = true
  edgeMasks : ∀ e : Fin 1024,
    D.edges e.val = RawNatGrowthCheck.mask (D.edgeSupports e.val)
  edgeCoverage : ∀ c : Fin n,
    (D.cells c.val).edges.all (fun e => (D.edges e).testBit c.val) = true
  edgeSound : ∀ e : Fin 1024,
    (D.edgeSupports e.val).all (fun c => hasNat (D.cells c).edges e.val) = true
  kindMasks : ∀ k, k ∈ D.keys →
    D.kinds k = RawNatGrowthCheck.mask (D.kindSupports k)
  kindSound : ∀ k, k ∈ D.keys →
    (D.kindSupports k).all (fun c => decide ((D.cells c).kind = k)) = true
  kindExact : ∀ c : Fin n, D.fastKind c.val = (D.cells c.val).kind
  missingSound : ∀ c : Fin n, ∀ e, e ∈ D.missing c.val →
    Nat.land e (D.cells c.val).vertices = e ∧ e ∉ (D.cells c.val).edges

variable {n : Nat} {D : Data n}

theorem Facts.vertices_lt (F : Facts D) (c : Fin n) : (D.cells c.val).vertices < 1024 :=
  (RawFacetEmbedding.wellFormedCheck_sound _ (F.wellFormed c)).1

theorem Facts.edge_bounds (F : Facts D) (c : Fin n) :
    listBounds 1024 (D.cells c.val).edges = true :=
  List.all_eq_true.mpr fun e he => decide_eq_true
    ((RawFacetEmbedding.wellFormedCheck_sound _ (F.wellFormed c)).2.1 e he)

theorem Facts.ridge_bounds (F : Facts D) (c : Fin n) :
    listBounds 1024 (D.cells c.val).ridgeMasks = true :=
  List.all_eq_true.mpr fun q hq => decide_eq_true
    ((RawFacetEmbedding.wellFormedCheck_sound _ (F.wellFormed c)).2.2.1 q hq)

theorem Facts.ridge_support_coverage (F : Facts D) (c : Fin n) :
    (D.cells c.val).ridgeMasks.all (fun q => hasNat (D.candidateSupports q) c.val) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have hlt : q < 1024 := of_decide_eq_true (List.all_eq_true.mp (F.ridge_bounds c) q hq)
  rw [← mask_bit, ← F.candidateMasks ⟨q,hlt⟩]
  exact List.all_eq_true.mp (F.candidateCoverage c) q hq

theorem Facts.edge_support_coverage (F : Facts D) (c : Fin n) :
    (D.cells c.val).edges.all (fun e => hasNat (D.edgeSupports e) c.val) = true := by
  apply List.all_eq_true.mpr
  intro e he
  have hlt : e < 1024 := of_decide_eq_true (List.all_eq_true.mp (F.edge_bounds c) e he)
  rw [← mask_bit, ← F.edgeMasks ⟨e,hlt⟩]
  exact List.all_eq_true.mp (F.edgeCoverage c) e he

def ridgeRows (D : Data n) : Nat → Nat := boundedRow D.candidates 1024
def edgeRows (D : Data n) : Nat → Nat := boundedRow D.edges 1024

theorem Facts.ridge_exact (F : Facts D) (q : Nat) (c : Fin n) :
    (ridgeRows D q).testBit c.val = hasNat (D.cells c.val).ridgeMasks q :=
  boundedRow_exact (fun c => (D.cells c).ridgeMasks) D.candidates D.candidateSupports
    F.ridge_bounds F.candidateMasks F.ridge_support_coverage F.candidateSound q c

theorem Facts.edge_exact (F : Facts D) (q : Nat) (c : Fin n) :
    (edgeRows D q).testBit c.val = decide (q ∈ (D.cells c.val).edges) := by
  rw [edgeRows, boundedRow_exact (fun c => (D.cells c).edges) D.edges D.edgeSupports
    F.edge_bounds F.edgeMasks F.edge_support_coverage F.edgeSound q c]
  apply Bool.eq_iff_iff.mpr
  rw [hasNat_true, decide_eq_true_eq]

noncomputable def intersectionRows (D : Data n) (F : Facts D) :
    IntersectionIncompatibilityRows.Rows (finiteCells D) 10 where
  vertices v := D.vertices v.val
  vertex_exact := F.vertexExact
  faces q := Nat.lor (edgeRows D q) (ridgeRows D q)
  edge_complete := by
    intro c q hq
    change q ∈ (D.cells c.val).edges at hq
    rw [testBit_lor, F.edge_exact, decide_eq_true hq]
    rfl
  ridge_complete := by
    intro c q hq
    change q ∈ (D.cells c.val).ridgeMasks at hq
    rw [testBit_lor, F.ridge_exact, (hasNat_true _ _).mpr hq]
    exact Bool.or_true _

noncomputable def edgeDisagreementRows (D : Data n) (F : Facts D) :
    EdgeDisagreementRows.Rows (finiteCells D) where
  edges := edgeRows D
  pairs := containsRow (fun v : Fin 10 => D.vertices v.val)
  edge_exact := F.edge_exact
  pair_exact := containsRow_exact (fun c => (D.cells c.val).vertices)
    (fun v : Fin 10 => D.vertices v.val) F.vertices_lt F.vertexExact
  edge_within := F.edgeWithin

noncomputable def justifiedBad (D : Data n) (F : Facts D) (c : Fin n) : Nat :=
  Nat.lor (ProperFaceComplementRows.badFaceRow (intersectionRows D F) c)
    (EdgeDisagreementRows.incompatibleRow (edgeDisagreementRows D F)
      (D.cells c.val).edges (D.missing c.val))

theorem justifiedBad_sound (D : Data n) (F : Facts D) (a b : Fin n)
    (h : bitAt (justifiedBad D F a) b.val = true) :
    compatible (D.cells a.val) (D.cells b.val) = false := by
  rw [justifiedBad, bitAt_or, Bool.or_eq_true_iff] at h
  cases h with
  | inl h =>
      exact ProperFaceComplementRows.badFaceRow_sound
        (intersectionRows D F) a b (F.vertices_lt a) h
  | inr h =>
      exact EdgeDisagreementRows.incompatibleRow_sound
        (edgeDisagreementRows D F) a b _ _ (fun _ he => he) (F.missingSound a) h

/-- Every cache law is a theorem about the literal universe. The only final
finite comparison identifies each emitted rejection mask with its justified
proper-face/edge formula. -/
noncomputable def cache (D : Data n) (F : Facts D)
    (hbad : ∀ c : Fin n, D.bad c.val = justifiedBad D F c) :
    Cache (ConcreteGrowth.ridgeList (finiteCells D))
      (fun a b => compatible (D.cells a.val) (D.cells b.val))
      (fun c => (D.cells c.val).kind) where
  candidates q := D.candidates q.val
  incompatible c := D.bad c.val
  kinds := D.kinds
  keys := D.keys
  candidates_exact := by
    intro q c
    rw [bitAt_eq_testBit]
    have h := F.ridge_exact q.val c
    rw [ridgeRows, boundedRow, ite_eq_left q.isLt] at h
    rw [h]
    exact (has_decoded _ (F.ridge_bounds c) q).symm
  incompatible_sound := by
    intro a b h
    rw [hbad a] at h
    exact justifiedBad_sound D F a b h
  kind_sound := by
    intro k hk c h
    rw [bitAt_eq_testBit, F.kindMasks k hk, mask_bit, hasNat_true] at h
    exact of_decide_eq_true (List.all_eq_true.mp (F.kindSound k hk) c.val h)

#print axioms cache

end Papers.RationalityTen.RawSharedCache
