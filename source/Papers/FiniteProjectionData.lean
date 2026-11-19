module
public import Papers.ProjectedRelationTemplate
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# Finite data for projection reconstruction certificates

This module has no geometry, real numbers, topology, or linear algebra.
Every premise is a finite statement about labels and vertex masks. The
separate soundness modules transport these certificates to actual polytopes.

-/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

/-- The intrinsic finite set of ordinary and extra projection planes. -/
def computedPlanes {n : ℕ}
    (facets polygons : Finset (Finset (Fin (n + 1)))) :
    Finset (Bool × Finset (Fin (n + 1))) :=
  ((facets.filter fun F => 0 ∈ F).image fun F => (false, F)) ∪
    ((polygons.filter fun R => 0 ∉ R ∧ ∀ F ∈ facets, 0 ∈ F → ¬ R ⊆ F).image
      fun R => (true, R))

structure Boundary (n : ℕ) where
  facets : Finset (Finset (Fin (n + 1)))
  polygons : Finset (Finset (Fin (n + 1)))
  /-- A literal cache prevents repeated reconstruction during kernel replay. -/
  planeCache : Finset (Bool × Finset (Fin (n + 1))) := computedPlanes facets polygons
  planeCache_correct : planeCache = computedPlanes facets polygons := by rfl
  deriving DecidableEq

/-- The cache carries no additional mathematical data. -/
theorem Boundary.ext_faces {n : ℕ} (B C : Boundary n)
    (hF : B.facets = C.facets) (hR : B.polygons = C.polygons) : B = C := by
  cases B with
  | mk f r c hc =>
    cases C with
    | mk f' r' c' hc' =>
      dsimp at hF hR
      subst f'
      subst r'
      have he : c = c' := hc.trans hc'.symm
      cases he
      rfl

/-- Relabel both complete face families by the same vertex permutation. -/
def Boundary.relabel {n : ℕ} (B : Boundary n) (σ : Fin (n + 1) ≃ Fin (n + 1)) :
    Boundary n where
  facets := B.facets.image (fun S => S.image σ)
  polygons := B.polygons.image (fun S => S.image σ)

@[simp] theorem Boundary.relabel_refl {n : ℕ} (B : Boundary n) :
    B.relabel (Equiv.refl _) = B := by
  apply Boundary.ext_faces <;> simp [Boundary.relabel]

theorem Boundary.relabel_relabel {n : ℕ} (B : Boundary n)
    (σ τ : Fin (n + 1) ≃ Fin (n + 1)) :
    (B.relabel σ).relabel τ = B.relabel (σ.trans τ) := by
  apply Boundary.ext_faces <;>
    simp [Boundary.relabel, Finset.image_image, Function.comp_def, Equiv.trans_apply]

@[simp] theorem Boundary.relabel_symm {n : ℕ} (B : Boundary n)
    (σ : Fin (n + 1) ≃ Fin (n + 1)) : (B.relabel σ).relabel σ.symm = B := by
  apply Boundary.ext_faces <;> simp [Boundary.relabel, Finset.image_image, Function.comp_def]

/-- `false` denotes an ordinary facet plane; `true` an extra polygon. -/
abbrev Plane (n : ℕ) := Bool × Finset (Fin (n + 1))

def IsExtraMask {n : ℕ} (B : Boundary n) (R : Finset (Fin (n + 1))) : Prop :=
  R ∈ B.polygons ∧ 0 ∉ R ∧ ∀ F ∈ B.facets, 0 ∈ F → ¬ R ⊆ F

def planes {n : ℕ} (B : Boundary n) : Finset (Plane n) := B.planeCache

theorem planes_eq_computed {n : ℕ} (B : Boundary n) :
    planes B = computedPlanes B.facets B.polygons := B.planeCache_correct

@[simp] theorem ordinary_mem_planes {n : ℕ} (B : Boundary n) (S : Finset (Fin (n + 1))) :
    (false, S) ∈ planes B ↔ S ∈ B.facets ∧ 0 ∈ S := by
  rw [planes_eq_computed]
  simp [computedPlanes]

@[simp] theorem extra_mem_planes {n : ℕ} (B : Boundary n) (S : Finset (Fin (n + 1))) :
    (true, S) ∈ planes B ↔ IsExtraMask B S := by
  rw [planes_eq_computed]
  simp [computedPlanes, IsExtraMask]

abbrev PlaneNode {n : ℕ} (B : Boundary n) := ↥(planes B)

def carrier {n : ℕ} {B : Boundary n} (p : PlaneNode B) : Finset (Fin (n + 1)) := p.val.2

def incidence {n : ℕ} {B : Boundary n} (i : Fin n) (p : PlaneNode B) : Prop :=
  i.succ ∈ carrier p

instance {n : ℕ} {B : Boundary n} (i : Fin n) (p : PlaneNode B) :
    Decidable (incidence i p) := by
  unfold incidence
  infer_instance

variable {n c : ℕ}

inductive PointRule (B : Boundary n) (S : Finset (Fin n)) : Prop
  | atMostTwo (h : S.card ≤ 2)
  | avoidingPolygon (h : S.card ≤ 3) (R : B.polygons) (ha : 0 ∉ R.val)
      (hmem : ∀ i ∈ S, i.succ ∈ R.val)
  | facialWitness (h : S.card ≤ 3) (R : B.polygons) (ha : 0 ∈ R.val)
      (v : Fin n) (hv : v ∈ S) (hout : v.succ ∉ R.val)
      (hin : ∀ i ∈ S, i ≠ v → i.succ ∈ R.val)

inductive PlanePairRule {B : Boundary n} : PlaneNode B → PlaneNode B → Prop
  | ordinary (p q : PlaneNode B) (hp : p.val.1 = false) (hq : q.val.1 = false) (hne : p ≠ q) :
      PlanePairRule p q
  | extraOrdinary (p q : PlaneNode B) (hp : p.val.1 = true) (hq : q.val.1 = false) :
      PlanePairRule p q
  | ordinaryExtra (p q : PlaneNode B) (hp : p.val.1 = false) (hq : q.val.1 = true) :
      PlanePairRule p q
  | commonFacet (p q : PlaneNode B) (F : B.facets) (ha : 0 ∉ F.val)
      (R S : B.polygons) (hR : R.val = F.val ∩ carrier p)
      (hS : S.val = F.val ∩ carrier q) (hne : R ≠ S) : PlanePairRule p q

inductive PlaneRule (B : Boundary n) (S : Finset (PlaneNode B)) : Prop
  | atMostOne (h : S.card ≤ 1)
  | atMostTwo (h : S.card ≤ 2)
      (hpairs : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → PlanePairRule p q)
  | ordinary (h : S.card ≤ 3) (hord : ∀ p ∈ S, p.val.1 = false)
  | commonFacet (h : S.card ≤ 3) (F : B.facets) (ha : 0 ∉ F.val)
      (R : S → B.polygons) (hinj : Function.Injective R)
      (htrace : ∀ p : S, (R p).val = F.val ∩ carrier p.val)
  | commonPoint (p q r : PlaneNode B) (hr : r.val.1 = false)
      (w : Fin n) (hpair : PlanePairRule p q)
      (hwp : incidence w p) (hwq : incidence w q) (hwr : ¬ incidence w r)
      (hS : S ⊆ {p, q, r})

abbrev Node (B : Boundary n) := Fin n ⊕ PlaneNode B

def retainedPoints {B : Boundary n} (priority : Node B → ℕ) (p : PlaneNode B) :
    Finset (Fin n) := Finset.univ.filter fun i =>
  priority (Sum.inr p) < priority (Sum.inl i) ∧ incidence i p

def retainedPlanes {B : Boundary n} (priority : Node B → ℕ) (i : Fin n) :
    Finset (PlaneNode B) := Finset.univ.filter fun p =>
  priority (Sum.inl i) < priority (Sum.inr p) ∧ incidence i p

structure IncidenceCertificate (B : Boundary n) where
  priority : Node B → ℕ
  injective : Function.Injective priority
  plane_rule : ∀ p, PointRule B (retainedPoints priority p)
  point_rule : ∀ i, PlaneRule B (retainedPlanes priority i)

inductive FrameCertificate (B : Boundary n) {k : ℕ} (b : Fin k → Fin n) : Prop
  | polygon (hk : k ≤ 3) (hinj : Function.Injective b) (R : B.polygons)
      (ha : 0 ∉ R.val) (hmem : ∀ j, (b j).succ ∈ R.val)
  | facial (hk : k ≤ 4) (hinj : Function.Injective b) (R : B.polygons) (F : B.facets)
      (ha : 0 ∉ F.val) (hmem : ∀ j, (b j).succ ∈ F.val) (t : Fin k)
      (hout : (b t).succ ∉ R.val) (hin : ∀ j, j ≠ t → (b j).succ ∈ R.val)

abbrev FaceReference (B : Boundary n) := B.facets ⊕ B.polygons

def faceMask {B : Boundary n} : FaceReference B → Finset (Fin (n + 1))
  | Sum.inl F => F.val
  | Sum.inr R => R.val

def pointLabels (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.succ ∈ S

@[simp] theorem mem_pointLabels (S : Finset (Fin (n + 1))) (i : Fin n) :
    i ∈ pointLabels S ↔ i.succ ∈ S := by simp [pointLabels]

structure HeightRow (B : Boundary n) extends ProjectedRelationTemplate n where
  face : FaceReference B
  avoids : 0 ∉ faceMask face
  frame_mem : ∀ j, (frame j).succ ∈ faceMask face
  vertex_mem : vertex.succ ∈ faceMask face
  vertex_outside_frame : vertex ∉ Set.range frame
  frame_certificate : FrameCertificate B frame
  spanning_certificate : frameSize = 4 ∨
    (frameSize = 3 ∧ ∃ p : PlaneNode B, faceMask face ⊆ carrier p)

structure HeightCertificate (B : Boundary n) (c : ℕ) where
  rows : Fin c → HeightRow B
  pivot : Fin c → Fin n
  pivot_certificate : ∀ i, pivot i = (rows i).vertex ∨
    ∃ j : Fin (rows i).frameSize, pivot i = (rows i).frame j ∧
      FrameCertificate B (Function.update (rows i).frame j (rows i).vertex)
  later_absent : ∀ i j, i < j →
    pivot i ≠ (rows j).vertex ∧ pivot i ∉ Set.range (rows j).frame

def HeightCertificate.templates {B : Boundary n} (H : HeightCertificate B c) :
    Fin c → ProjectedRelationTemplate n := fun i => (H.rows i).toProjectedRelationTemplate

inductive FacetCoverage {B : Boundary n} (H : HeightCertificate B c) (F : B.facets) : Type
  | fundamental (b : Fin 4 → Fin n) (hframe : FrameCertificate B b)
      (hmem : ∀ j, (b j).succ ∈ F.val)
      (hcovered : ∀ v ∈ pointLabels F.val, v ∉ Set.range b →
        ∃ i : Fin c, H.templates i = {frameSize := 4, frame := b, vertex := v})
  | oneRow (b : Fin 4 → Fin n) (hframe : FrameCertificate B b)
      (hmem : ∀ j, (b j).succ ∈ F.val) (hcard : (pointLabels F.val).card ≤ 5)
      (i : Fin c) (hsupport : faceMask (H.rows i).face ⊆ F.val)
  | fromLargerFacet (b : Fin 4 → Fin n) (hframe : FrameCertificate B b)
      (hmem : ∀ j, (b j).succ ∈ F.val) (hcard : (pointLabels F.val).card ≤ 5)
      (R : B.polygons) (haR : 0 ∉ R.val) (hRcard : 4 ≤ (pointLabels R.val).card)
      (hRF : R.val ⊆ F.val) (G : B.facets) (g : Fin 4 → Fin n)
      (hgframe : FrameCertificate B g) (hgmem : ∀ j, (g j).succ ∈ G.val)
      (hRG : R.val ⊆ G.val)
      (hcovered : ∀ v ∈ pointLabels G.val, v ∉ Set.range g →
        ∃ i : Fin c, H.templates i = {frameSize := 4, frame := g, vertex := v})

structure ReconstructionCertificate (B : Boundary n) (c : ℕ) where
  incidence : IncidenceCertificate B
  heights : HeightCertificate B c
  facet : ∀ F : {F : B.facets // 0 ∉ F.val}, FacetCoverage heights F.val

/-- A finite boundary may use arbitrary vertex names.  Its complete
projection certificate is supplied after one explicit permutation. -/
structure CertifiedRelabelling (B : Boundary n) where
  target : Boundary n
  heightRows : ℕ
  certificate : ReconstructionCertificate target heightRows
  permutation : Fin (n + 1) ≃ Fin (n + 1)
  boundary_eq : B.relabel permutation = target

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection
