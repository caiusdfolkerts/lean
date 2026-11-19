module
prelude
public import FastRawCacheCertificate

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Compatibility coverage by face signatures

A literal cell is compatible with another only when their common vertex set
is a proper face of each and the induced edge lists agree.  We group cells
by those face signatures.  The groups need only cover every matching cell;
they may contain extras.  Disjointness from the resulting compatible
superset therefore proves that a sparse rejection mask contains no compatible
cell, without replaying every rejected pair separately.
-/
namespace Papers.RationalityTen.SignatureCompatibility
open ConcreteGrowth RawNatGrowthCheck RawGrowthCacheCertificate
open GrowthBitsets BatchedGrowthPruning RawNatGrowthSoundness

theorem land_bit (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i
theorem lor_bit (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i
theorem xor_bit (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) :=
  Nat.testBit_xor a b i

def smallFaces : List Nat := [0,1,2,4,8,16,32,64,128,256,512]
def simpleFace (q : Nat) : Bool := decide (Nat.land q (q-1) = 0)
def faces (a : Cell) : List Nat := smallFaces ++ a.edges ++ a.ridgeMasks

theorem simpleFace_mem (q : Nat) (hq : q < 1024) (h : simpleFace q = true) :
    q ∈ smallFaces := by
  have checked : ∀ q : Fin 1024, simpleFace q.val = true → q.val ∈ smallFaces := by
    decide +kernel
  exact checked ⟨q,hq⟩ h

theorem proper_mem_faces (a : Cell) (q : Nat) (hq : q < 1024)
    (h : proper a q = true) : q ∈ faces a := by
  simp only [proper, Bool.or_eq_true_iff] at h
  rcases h with (h | h) | h
  · exact List.mem_append_left _ (List.mem_append_left _ (simpleFace_mem q hq h))
  · exact List.mem_append_left _ (List.mem_append_right _ ((hasNat_true _ _).mp h))
  · exact List.mem_append_right _ ((hasNat_true _ _).mp h)

def allMask (n : Nat) : Nat := Nat.shiftLeft 1 n - 1

theorem allMask_bit {n : Nat} (b : Fin n) : (allMask n).testBit b.val = true := by
  have hs : Nat.shiftLeft 1 n = 2^n := PrimitiveBitsetGrowth.singleton_eq n
  rw [allMask, hs, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true b.isLt

/-- A mask covering cells whose vertex intersection with `m` is `q`.
Only the vertices selected by `m` impose a test. -/
def intersectionMask (all : Nat) (vertexMasks : Nat → Nat) (m q : Nat) : List Nat → Nat
  | [] => all
  | v :: rest =>
      Nat.land
        (if m.testBit v then
          if q.testBit v then vertexMasks v else Nat.xor all (vertexMasks v)
         else all)
        (intersectionMask all vertexMasks m q rest)

theorem intersectionMask_bit (all : Nat) (vertexMasks : Nat → Nat)
    (m bvertices b : Nat) (vs : List Nat)
    (hall : all.testBit b = true)
    (hvertices : ∀ v ∈ vs, (vertexMasks v).testBit b = bvertices.testBit v) :
    (intersectionMask all vertexMasks m (Nat.land m bvertices) vs).testBit b = true := by
  induction vs with
  | nil => exact hall
  | cons v rest ih =>
    have hv := hvertices v List.mem_cons_self
    have hr := ih (fun u hu => hvertices u (List.mem_cons_of_mem _ hu))
    simp only [intersectionMask, land_bit, hr, Bool.and_true]
    cases hm : m.testBit v <;> cases hb : bvertices.testBit v <;>
      simp only [hm, hb, land_bit, xor_bit, hv, hall, hr, Bool.false_and, Bool.true_and, Bool.false_eq_true, Bool.true_eq_false, Bool.false_xor, Bool.true_xor, Bool.not_false, Bool.not_true, if_true, if_false]

def edgeSignature (a : Cell) (q : Nat) : Nat :=
  mask (a.edges.filter (fun e => decide (Nat.land e q = e)))

def profileMask (all : Nat) (signatureIndex : Nat → Nat → Nat)
    (signatureMasks : Nat → Nat) (a : Cell) (q : Nat) : Nat :=
  if simpleFace q then all else signatureMasks (signatureIndex q (edgeSignature a q))

def cover (all : Nat) (vertexMasks : Nat → Nat)
    (signatureIndex : Nat → Nat → Nat) (signatureMasks : Nat → Nat) (a : Cell) : Nat :=
  union (fun q => Nat.land (intersectionMask all vertexMasks a.vertices q (List.range 10))
    (profileMask all signatureIndex signatureMasks a q)) (faces a)

theorem union_bit_of_mem (f : α → Nat) (xs : List α) (q : α) (hq : q ∈ xs)
    (b : Nat) (hb : (f q).testBit b = true) : (union f xs).testBit b = true := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil hq)
  | cons a xs ih =>
    simp only [union, lor_bit, Bool.or_eq_true_iff]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inl hb
    · exact Or.inr (ih hq)

theorem cover_complete {n : Nat} (cells : Fin n → Cell)
    (vertexMasks : Nat → Nat) (signatureIndex : Nat → Nat → Nat)
    (signatureMasks : Nat → Nat)
    (hbound : ∀ a, (cells a).vertices < 1024)
    (hvertices : ∀ (b : Fin n) v, v < 10 →
      (vertexMasks v).testBit b.val = (cells b).vertices.testBit v)
    (hprofiles : ∀ b : Fin n, (faces (cells b)).all (fun q =>
      (profileMask (allMask n) signatureIndex signatureMasks (cells b) q).testBit b.val) = true)
    (a b : Fin n) (hcompatible : compatible (cells a) (cells b) = true) :
    (cover (allMask n) vertexMasks signatureIndex signatureMasks (cells a)).testBit b.val = true := by
  let common := Nat.land (cells a).vertices (cells b).vertices
  have hcommon : common < 1024 := Nat.lt_of_le_of_lt Nat.and_le_left (hbound a)
  obtain ⟨hproper, hedges⟩ := Bool.and_eq_true_iff.mp hcompatible
  obtain ⟨hpa,hpb⟩ := Bool.and_eq_true_iff.mp hproper
  have hma : common ∈ faces (cells a) := proper_mem_faces _ _ hcommon hpa
  have hmb : common ∈ faces (cells b) := proper_mem_faces _ _ hcommon hpb
  have hsignature : edgeSignature (cells a) common = edgeSignature (cells b) common :=
    congrArg mask (of_decide_eq_true hedges)
  have hprofile : (profileMask (allMask n) signatureIndex signatureMasks (cells a) common).testBit b.val = true := by
    have h := List.all_eq_true.mp (hprofiles b) common hmb
    simpa only [profileMask, hsignature] using h
  apply union_bit_of_mem _ (faces (cells a)) common hma b.val
  rw [land_bit]
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, hprofile⟩
  exact intersectionMask_bit _ _ _ _ _ _ (allMask_bit b)
    (fun v hv => hvertices b v (List.mem_range.mp hv))

theorem rejection_sound {n : Nat} (cells : Fin n → Cell)
    (vertexMasks : Nat → Nat) (signatureIndex : Nat → Nat → Nat)
    (signatureMasks bad : Nat → Nat)
    (hbound : ∀ a, (cells a).vertices < 1024)
    (hvertices : ∀ (b : Fin n) v, v < 10 →
      (vertexMasks v).testBit b.val = (cells b).vertices.testBit v)
    (hprofiles : ∀ b : Fin n, (faces (cells b)).all (fun q =>
      (profileMask (allMask n) signatureIndex signatureMasks (cells b) q).testBit b.val) = true)
    (hdisjoint : ∀ a : Fin n,
      Nat.land (bad a.val) (cover (allMask n) vertexMasks signatureIndex signatureMasks (cells a)) = 0)
    (a b : Fin n) (hbad : (bad a.val).testBit b.val = true) :
    compatible (cells a) (cells b) = false := by
  cases hcompatible : compatible (cells a) (cells b) with
  | false => rfl
  | true =>
    have good := cover_complete cells vertexMasks signatureIndex signatureMasks
      hbound hvertices hprofiles a b hcompatible
    have impossible := congrArg (fun x : Nat => x.testBit b.val) (hdisjoint a)
    rw [land_bit, hbad, good, Nat.zero_testBit] at impossible
    exact Bool.noConfusion impossible

/-- The candidate and kind rows use their existing checked interfaces. Only
compatibility rejection changes: it now follows from signature coverage. -/
noncomputable def ofChecks {n : Nat} (cells : Nat → Cell)
    (candidates bad kinds : Nat → Nat) (candidateRows kindRows : Nat → List Nat)
    (keys : List Nat) (vertexMasks : Nat → Nat)
    (signatureIndex : Nat → Nat → Nat) (signatureMasks : Nat → Nat)
    (hridgeBounds : ∀ c : Fin n, listBounds 1024 (cells c.val).ridgeMasks = true)
    (hcandidateMasks : ∀ q : Fin 1024,
      candidates q.val = mask (candidateRows q.val))
    (hcandidateCoverage : ∀ c : Fin n,
      (cells c.val).ridgeMasks.all (fun q => (candidates q).testBit c.val) = true)
    (hcandidateSound : ∀ q : Fin 1024,
      (candidateRows q.val).all (fun c => hasNat (cells c).ridgeMasks q.val) = true)
    (hkindMasks : ∀ j, j ∈ keys → kinds j = mask (kindRows j))
    (hkindSound : ∀ j, j ∈ keys →
      (kindRows j).all (fun c => decide ((cells c).kind = j)) = true)
    (hbound : ∀ a : Fin n, (cells a.val).vertices < 1024)
    (hvertices : ∀ (b : Fin n) v, v < 10 →
      (vertexMasks v).testBit b.val = (cells b.val).vertices.testBit v)
    (hprofiles : ∀ b : Fin n, (faces (cells b.val)).all (fun q =>
      (profileMask (allMask n) signatureIndex signatureMasks (cells b.val) q).testBit b.val) = true)
    (hdisjoint : ∀ a : Fin n, Nat.land (bad a.val)
      (cover (allMask n) vertexMasks signatureIndex signatureMasks (cells a.val)) = 0) :
    Cache (ConcreteGrowth.ridgeList (fun c : Fin n => cells c.val))
      (fun a b : Fin n => compatible (cells a.val) (cells b.val))
      (fun c : Fin n => (cells c.val).kind) := by
  let base : Cache (ConcreteGrowth.ridgeList (fun c : Fin n => cells c.val))
      (fun a b : Fin n => compatible (cells a.val) (cells b.val))
      (fun c : Fin n => (cells c.val).kind) :=
    FastRawCacheCertificate.ofChecks cells candidates (fun _ => 0) kinds candidateRows
      (fun _ => []) kindRows keys hridgeBounds hcandidateMasks hcandidateCoverage
      hcandidateSound (fun _ => rfl) (fun _ => rfl) hkindMasks hkindSound
  exact {base with
    incompatible := fun a => bad a.val
    incompatible_sound := by
      intro a b h
      rw [bitAt_eq_testBit] at h
      exact rejection_sound _ vertexMasks signatureIndex signatureMasks bad
        hbound hvertices hprofiles hdisjoint a b h}

#print axioms ofChecks
end Papers.RationalityTen.SignatureCompatibility
