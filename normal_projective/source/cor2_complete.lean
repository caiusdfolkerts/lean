module

public import cap_extraction_geometry
public import cap_polarity_geometry
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Printer
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
public import maxwell_development

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


/-!
# Complete three-dimensional normal-projective verification

Authoritative component inputs and exact retained-line provenance are recorded
in `audit/current/cor2_complete_source_map.json`.  This aggregate is generated
by `tools/assemble_cor2.py`; edit its component inputs, then reassemble.
All proof bodies are preserved. The ordinary compiler and axiom-audit
records identify the checked source bytes.
-/

@[expose] public section
noncomputable section
set_option maxErrors 500

/- Source component: Cor2Candidate/FiniteHullModel.lean -/
section


/-!
# Finite vertex hulls admit actual complete facet presentations

The frontend is valid in every dimension.  In positive dimension, polarize
about an interior point, then use the actual extreme points of the compact
polar as the facet labels.  Strict facet witnesses are averages of independent
active normals.  Thus no finite halfspace representation theorem is assumed.
-/

open Set Finset
open scoped BigOperators Topology

namespace NormalProjective.FiniteHullModel

open CanonicalModel UnitNormalization NormalHull

variable {d : ℕ} {V : Type*} [Fintype V]

abbrev E := CanonicalModel.Space d

abbrev PolarVertices (v : V → E (d := d)) :=
  (primal v).extremePoints ℝ

instance polarVerticesFinite (v : V → E (d := d)) : Finite (PolarVertices v) :=
  (halfspace_extremePoints_finite (fun i => (rowForm (v i)).toLinearMap)
    (fun _ => 1)).to_subtype

instance polarVerticesFintype (v : V → E (d := d)) : Fintype (PolarVertices v) :=
  Fintype.ofFinite _

def facetData (v : V → E (d := d)) : HalfspaceData (PolarVertices v) (E (d := d)) :=
  (fun x => rowForm x.val,fun _ => 1)

theorem facetData_region (v : V → E (d := d))
    (h₀ : (0 : E) ∈ interior (hull v)) :
    dataRegion (facetData v) = hull v := by
  ext y
  rw [PolarFinite.hull_iff_extreme_pairings v h₀]
  change (∀ x : PolarVertices v, rowForm x.val y ≤ 1) ↔
    ∀ x ∈ (primal v).extremePoints ℝ, dot y x ≤ 1
  constructor
  · intro h x hx
    simpa only [rowForm_apply,NormalHull.dot_comm] using h ⟨x,hx⟩
  · intro h x
    simpa only [rowForm_apply,NormalHull.dot_comm] using h x.val x.property

theorem polar_vertex_ne_zero (hd : 0 < d) (v : V → E (d := d))
    (x : PolarVertices v) : x.val ≠ 0 := by
  obtain ⟨I,hI,hind⟩ := extremePoint_has_active_basis
    (fun i => (rowForm (v i)).toLinearMap) (fun _ => 1) x.property
  intro hx
  have hh := hI ⟨0,hd⟩
  simp only [hx,map_zero] at hh
  exact zero_ne_one hh

theorem strict_facet_witness (hd : 0 < d) (v : V → E (d := d))
    (x : PolarVertices v) :
    ∃ y ∈ dataRegion (facetData v), rowForm x.val y = 1 ∧
      ∀ z : PolarVertices v, z ≠ x → rowForm z.val y < 1 := by
  classical
  let f := fun i => (rowForm (v i)).toLinearMap
  obtain ⟨I,hI,hind⟩ := extremePoint_has_active_basis f (fun _ => 1) x.property
  have hdet := facetCoefficientMatrix_det_ne_zero (fun j => f (I j)) hind
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let y : E := (d : ℝ)⁻¹ • ∑ j : Fin d, v (I j)
  have heval (z : PolarVertices v) : rowForm z.val y =
      (d : ℝ)⁻¹ * ∑ j : Fin d, rowForm (v (I j)) z.val := by
    simp only [y,map_smul,map_sum,smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [rowForm_apply,NormalHull.dot_comm]
  have hle (z : PolarVertices v) (j : Fin d) : rowForm (v (I j)) z.val ≤ 1 :=
    z.property.1 (I j)
  have he : rowForm x.val y = 1 := by
    rw [heval]
    have hh (j : Fin d) : rowForm (v (I j)) x.val = 1 := hI j
    simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    exact inv_mul_cancel₀ hdR.ne'
  have hstrict (z : PolarVertices v) (hz : z ≠ x) : rowForm z.val y < 1 := by
    have hex : ∃ j : Fin d, rowForm (v (I j)) z.val < 1 := by
      by_contra! hall
      apply hz
      apply Subtype.ext
      apply tight_minor_unique f (fun _ => 1) I hdet
      · intro j
        exact le_antisymm (hle z j) (hall j)
      · exact hI
    obtain ⟨j,hj⟩ := hex
    have hsum : (∑ k : Fin d, rowForm (v (I k)) z.val) < ∑ _ : Fin d, (1 : ℝ) :=
      Finset.sum_lt_sum (fun k _ => hle z k) ⟨j,Finset.mem_univ j,hj⟩
    rw [heval]
    apply (inv_mul_lt_iff₀ hdR).mpr
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hsum
  refine ⟨y,?_,he,hstrict⟩
  intro z
  by_cases hz : z = x
  · subst z
    exact he.le
  · exact (hstrict z hz).le

def regularOfCenteredHull (hd : 0 < d) (v : V → E (d := d))
    (h₀ : (0 : E) ∈ interior (hull v)) : RegularData d (PolarVertices v) where
  data := facetData v
  normal_ne_zero := by
    intro x hx
    change rowForm x.val = 0 at hx
    have he := congrArg coefficients hx
    apply polar_vertex_ne_zero hd v x
    simpa only [coefficients_rowForm,coefficients_zero] using he
  compact := by
    rw [facetData_region v h₀]
    exact (Set.finite_range v).isCompact_convexHull ℝ
  full_dimensional := by
    rw [facetData_region v h₀]
    exact ⟨0,h₀⟩
  strict_facet_point := strict_facet_witness hd v

theorem regularOfCenteredHull_carrier (hd : 0 < d) (v : V → E (d := d))
    (h₀ : (0 : E) ∈ interior (hull v)) :
    (presentation (regularOfCenteredHull hd v h₀)).carrier = convexHull ℝ (Set.range v) := by
  rw [presentation_carrier]
  exact facetData_region v h₀

def centeredVertices (v : V → E (d := d)) (c : E (d := d)) : V → E (d := d) :=
  fun i => v i-c

theorem centered_hull_image (v : V → E (d := d)) (c : E) :
    hull (centeredVertices v c) =
      AffineEquiv.constVAdd ℝ E (-c) '' convexHull ℝ (Set.range v) := by
  let a := AffineEquiv.constVAdd ℝ E (-c)
  have hh := a.toAffineMap.image_convexHull (Set.range v)
  have he : a.toAffineMap '' Set.range v = Set.range (centeredVertices v c) := by
    rw [← Set.range_comp']
    congr 1
    funext i
    simp [a,centeredVertices,sub_eq_add_neg,add_comm]
  rw [he] at hh
  exact hh.symm

theorem centered_zero_interior (v : V → E (d := d)) (c : E)
    (hc : c ∈ interior (convexHull ℝ (Set.range v))) :
    (0 : E) ∈ interior (hull (centeredVertices v c)) := by
  rw [centered_hull_image]
  let a := AffineEquiv.constVAdd ℝ E (-c)
  have hh : a.toHomeomorphOfFiniteDimensional c ∈
      a.toHomeomorphOfFiniteDimensional '' interior (convexHull ℝ (Set.range v)) :=
    ⟨c,hc,rfl⟩
  rw [a.toHomeomorphOfFiniteDimensional.image_interior] at hh
  simpa [a] using hh

/-- A canonical facet presentation together with its literal underlying set.
The label type is supplied by the construction rather than imposed on the
finite vertex list. -/
structure FacetModel (K : Set (E (d := d))) where
  Label : Type
  labels : Fintype Label
  presentation : @CanonicalModel.Presentation d Label labels
  carrier_eq : presentation.carrier = K

def facetModelOfCenteredHull (hd : 0 < d) (v : V → E (d := d))
    (h₀ : (0 : E) ∈ interior (hull v)) : FacetModel (convexHull ℝ (Set.range v)) where
  Label := PolarVertices v
  labels := inferInstance
  presentation := presentation (regularOfCenteredHull hd v h₀)
  carrier_eq := regularOfCenteredHull_carrier hd v h₀

/-- Every full-dimensional finite vertex hull in positive dimension has an
irredundant complete facet presentation with exactly the same carrier. -/
theorem finite_hull_has_facet_model (hd : 0 < d) (v : V → E (d := d))
    (hfull : (interior (convexHull ℝ (Set.range v))).Nonempty) :
    Nonempty (FacetModel (convexHull ℝ (Set.range v))) := by
  obtain ⟨c,hc⟩ := hfull
  let w := centeredVertices v c
  have hw : (0 : E) ∈ interior (hull w) := centered_zero_interior v c hc
  let p := regularOfCenteredHull hd w hw
  let a := AffineEquiv.constVAdd ℝ E c
  refine ⟨{
    Label := PolarVertices w
    labels := inferInstance
    presentation := presentation (affineRegular a p)
    carrier_eq := ?_ }⟩
  rw [affineRegular_carrier,regularOfCenteredHull_carrier]
  change a '' hull (centeredVertices v c) = convexHull ℝ (Set.range v)
  rw [centered_hull_image,Set.image_image]
  have he : (fun x : E => a (AffineEquiv.constVAdd ℝ E (-c) x)) = id := by
    funext x
    simp [a,add_assoc]
  rw [he,Set.image_id]

def zeroPresentation : CanonicalModel.Presentation 0 Empty where
  normal := Empty.elim
  support := Empty.elim
  unit_normal := fun i => nomatch i
  compact := by
    have hsub : (region (Empty.elim : Empty → CanonicalModel.Space 0)
        (Empty.elim : Empty → ℝ)).Subsingleton :=
      fun _ _ _ _ => Subsingleton.elim _ _
    exact hsub.finite.isCompact
  full_dimensional := by
    have he : region (Empty.elim : Empty → CanonicalModel.Space 0)
        (Empty.elim : Empty → ℝ) = Set.univ := by
      ext x
      simp [region]
    rw [he,interior_univ]
    exact ⟨0,Set.mem_univ 0⟩
  strict_facet_point := fun i => nomatch i

/-- The full vertex-hull frontend, including dimension zero. -/
theorem finite_hull_has_facet_model_all_dimensions (v : V → E (d := d))
    (hfull : (interior (convexHull ℝ (Set.range v))).Nonempty) :
    Nonempty (FacetModel (convexHull ℝ (Set.range v))) := by
  cases d with
  | zero =>
      refine ⟨{
        Label := Empty
        labels := inferInstance
        presentation := zeroPresentation
        carrier_eq := ?_ }⟩
      ext x
      constructor
      · intro hx
        obtain ⟨y,hy⟩ := hfull.mono interior_subset
        exact (Subsingleton.elim y x) ▸ hy
      · intro hx i
        exact Empty.elim i
  | succ n => exact finite_hull_has_facet_model (Nat.succ_pos n) v hfull

end NormalProjective.FiniteHullModel

end

/- Source component: Cor2Candidate/SimpleThreeCorollary.lean -/
section


/-!
# Corollary 2: every simple convex three-polytope is PN-unique

The statement below quantifies over arbitrary canonical labelled realizations.
Normalization, extraction of corresponding genuine caps, the path of caps,
and the return from polarity are all supplied by proved constructions.
-/

open Set
open scoped Topology

namespace NormalProjective.CanonicalModel.Realization

variable {d : ℕ} {V : Type*} [Fintype V] {R : Presentation d V}

theorem PNRelated.rebase {S : Presentation d V} (hSR : S.SameLabelledType R)
    {P Q : Realization R} (h : PNRelated P Q) :
    PNRelated (rebase hSR P) (rebase hSR Q) := by
  obtain ⟨p,n,hw⟩ := h
  exact ⟨p,n,hw.rebase hSR⟩

end NormalProjective.CanonicalModel.Realization

namespace NormalProjective

open CanonicalModel CanonicalModel.Realization UnitNormalization CapSource
open Planar

variable {V : Type*} [Fintype V]

theorem normalized_three_chart (P : Presentation 3 V) :
    ∃ (p : RegularData 3 V) (a : CanonicalModel.Space 3 ≃ᵃ[ℝ] CanonicalModel.Space 3),
      (∀ v, p.data.2 v = 1) ∧ presentation p = affinePresentation a P := by
  obtain ⟨a,hpos,hgeneric⟩ :=
    GenericCoordinates.exists_generic_centered_chart (n := 2) (ofCanonical P)
  let r := affineRegular a (ofCanonical P)
  let p := normalizedRegular r hpos
  refine ⟨p,a,?_,?_⟩
  · intro v
    have hh := normalizedRegular_data r hpos
    have hh' := congrArg (fun D => D.2 v) hh
    exact hh'
  · rw [presentation_normalizedRegular]
    rfl

/-- Corollary 2 of the manuscript, for the full labelled realization space
of every simple convex three-polytope. -/
theorem simple_three_pn_unique {R : Presentation 3 V} (hR : R.Simple)
    (P Q : Realization R) : PNRelated P Q := by
  classical
  obtain ⟨p,a,hp,heP⟩ := normalized_three_chart P.val
  obtain ⟨q,b,hq,heQ⟩ := normalized_three_chart Q.val
  have hRp : R.SameLabelledType (presentation p) := by
    rw [heP]
    exact P.property.trans (affinePresentation_sameLabelledType a P.val)
  have hRq : R.SameLabelledType (presentation q) := by
    rw [heQ]
    exact Q.property.trans (affinePresentation_sameLabelledType b Q.val)
  have hpS : IsSimpleHalfspace (fun v => (p.data.1 v).toLinearMap) p.data.2 :=
    (simple_iff_raw p).mp (hR.of_sameLabelledType hRp)
  have hqS : IsSimpleHalfspace (fun v => (q.data.1 v).toLinearMap) q.data.2 :=
    (simple_iff_raw q).mp (hR.of_sameLabelledType hRq)
  obtain ⟨p',q',hp',hq',hp'S,hq'S,A,B,a',b',hAp,hBq,hCD⟩ :=
    compatible_positions p q hp hq hpS hqS (hRp.symm.trans hRq)
  have heP' : presentation p' = affinePresentation (a.trans a') P.val := by
    rw [hAp,heP,affinePresentation_trans]
  have heQ' : presentation q' = affinePresentation (b.trans b') Q.val := by
    rw [hBq,heQ,affinePresentation_trans]
  have hRp' : R.SameLabelledType (presentation p') := by
    rw [heP']
    exact P.property.trans (affinePresentation_sameLabelledType _ _)
  have hRq' : R.SameLabelledType (presentation q') := by
    rw [heQ']
    exact Q.property.trans (affinePresentation_sameLabelledType _ _)
  let P' : Realization R := ⟨presentation p',hRp'⟩
  let Q' : Realization R := ⟨presentation q',hRq'⟩
  have hPP' : PNRelated P P' := by
    have hh := (affineAction_related (a.trans a') P).pnRelated
    have he : affineAction (a.trans a') P = P' := Subtype.ext heP'.symm
    rwa [he] at hh
  have hQQ' : PNRelated Q Q' := by
    have hh := (affineAction_related (b.trans b') Q).pnRelated
    have he : affineAction (b.trans b') Q = Q' := Subtype.ext heQ'.symm
    rwa [he] at hh
  let C := A.strictConvexCap p' hp' hp'S
  let D := B.strictConvexCap q' hq' hq'S
  have hCD' : C.SameCombinatorics D := hCD
  obtain ⟨v₀,hv₀⟩ := C.interior_nonempty
  have hvD : v₀ ∉ D.disk.boundary := by
    rw [← hCD'.boundary_eq]
    exact hv₀
  have hPC : (presentation p').SameLabelledType (presentation (C.polarRegular v₀ hv₀)) :=
    A.cap_polar_sameLabelledType p' hp' hp'S v₀ hv₀
  have hQD : (presentation q').SameLabelledType (presentation (D.polarRegular v₀ hvD)) :=
    B.cap_polar_sameLabelledType q' hq' hq'S v₀ hvD
  let PC : Realization R := ⟨presentation (C.polarRegular v₀ hv₀),hRp'.trans hPC⟩
  let PD : Realization R := ⟨presentation (D.polarRegular v₀ hvD),hRq'.trans hQD⟩
  have hP'C : PNRelated P' PC :=
    (A.pnRelated_cap_polar p' hp' hp'S v₀ hv₀).rebase hRp'
  have hQ'D : PNRelated Q' PD :=
    (B.pnRelated_cap_polar q' hq' hq'S v₀ hvD).rebase hRq'
  obtain ⟨γ,hγ⟩ := StrictConvexCap.exists_path_sameCombinatorics C D hCD'
  have hcap : PNRelated PC PD :=
    (StrictConvexCap.pnRelated_of_cap_path C D v₀ hv₀ hCD' γ hγ).rebase (hRp'.trans hPC)
  exact hPP'.trans (hP'C.trans (hcap.trans (hQ'D.symm.trans hQQ'.symm)))

/-- Equivalent statement with two actual facet presentations and an explicit
label-preserving face-lattice isomorphism. -/
theorem simple_three_presentations_pn (P Q : Presentation 3 V)
    (hP : P.Simple) (hPQ : P.SameLabelledType Q) :
    PNRelated (⟨P,Presentation.sameLabelledType_refl P⟩ : Realization P) ⟨Q,hPQ⟩ :=
  simple_three_pn_unique hP _ _

end NormalProjective

end

/- Source component: Cor2Candidate/Relabelling.lean -/
section


/-!
# Changing facet-label types and the unlabelled three-dimensional consequence

This scope frontend derives the facet-label correspondence from actual faces.
An arbitrary order isomorphism of actual face orders preserves the empty face,
the full carrier, and the nonempty maximal proper faces. The already developed
facet-faithfulness theorem identifies those latter faces with the displayed
labels. Consequently the label equivalence below is derived from the given face
isomorphism; it is not supplied as an additional hypothesis.

Reindexing changes neither the carrier nor any geometric facet. Its canonical
normal and support at label `i` are exactly the original data at label `e i`.
Thus the final PN word ends at the original target carrier, with only its labels
transported to the source label type.
-/


namespace NormalProjective.LabelTransport

open Set CanonicalModel UnitNormalization

variable {d : ℕ} {V W : Type*} [Fintype V] [Fintype W]

abbrev RawFaces (p : RegularData d V) :=
  HalfspaceFaces (fun i => (p.data.1 i).toLinearMap) p.data.2

def emptyFace (p : RegularData d V) : RawFaces p := ⟨∅, isExposed_empty⟩

def fullFace (p : RegularData d V) : RawFaces p :=
  ⟨dataRegion p.data, by
    change IsExposed ℝ (dataRegion p.data) (dataRegion p.data)
    exact IsExposed.refl _⟩

theorem map_empty (p : RegularData d V) (q : RegularData d W)
    (e : RawFaces p ≃o RawFaces q) : e (emptyFace p) = emptyFace q := by
  apply le_antisymm
  · have h := e.monotone
      (show emptyFace p ≤ e.symm (emptyFace q) from Set.empty_subset _)
    simpa only [e.apply_symm_apply] using h
  · exact Set.empty_subset _

theorem map_full (p : RegularData d V) (q : RegularData d W)
    (e : RawFaces p ≃o RawFaces q) : e (fullFace p) = fullFace q := by
  apply le_antisymm
  · exact (e (fullFace p)).property.subset
  · have h := e.monotone
      (show e.symm (fullFace q) ≤ fullFace p from (e.symm (fullFace q)).property.subset)
    simpa only [e.apply_symm_apply] using h

theorem map_actualFacet (p : RegularData d V) (q : RegularData d W)
    (e : RawFaces p ≃o RawFaces q) (F : RawFaces p) (hF : IsActualFacet p F) :
    IsActualFacet q (e F) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hne
    have he : e F = emptyFace q :=
      Subtype.ext (Set.not_nonempty_iff_eq_empty.mp hne)
    have hzero : F = emptyFace p :=
      e.injective (he.trans (map_empty p q e).symm)
    exact hF.1.ne_empty (congrArg Subtype.val hzero)
  · intro hfull
    have he : e F = fullFace q := Subtype.ext hfull
    have htop : F = fullFace p :=
      e.injective (he.trans (map_full p q e).symm)
    exact hF.2.1 (congrArg Subtype.val htop)
  · intro G hFG hG
    have hFG' : F ≤ e.symm G := by
      simpa only [e.symm_apply_apply] using e.symm.monotone hFG
    have hproper : (e.symm G).val ≠ dataRegion p.data := by
      intro hfull
      have he : e.symm G = fullFace p := Subtype.ext hfull
      have he' : G = fullFace q := by
        simpa only [e.apply_symm_apply, map_full p q e] using congrArg e he
      exact hG (congrArg Subtype.val he')
    have he := hF.2.2 (e.symm G) hFG' hproper
    simpa only [e.apply_symm_apply] using congrArg e he

def actualFacetEquiv (p : RegularData d V) (q : RegularData d W)
    (e : RawFaces p ≃o RawFaces q) :
    {F : RawFaces p // IsActualFacet p F} ≃ {F : RawFaces q // IsActualFacet q F} where
  toFun F := ⟨e F.val, map_actualFacet p q e F.val F.property⟩
  invFun F := ⟨e.symm F.val, map_actualFacet q p e.symm F.val F.property⟩
  left_inv F := Subtype.ext (e.symm_apply_apply F.val)
  right_inv F := Subtype.ext (e.apply_symm_apply F.val)

/-- The facet-label equivalence induced by an arbitrary actual face-order
isomorphism, using the checked complete-facet enumeration. -/
def labelEquiv (p : RegularData d V) (q : RegularData d W)
    (e : RawFaces p ≃o RawFaces q) : V ≃ W :=
  (displayedFacetEquiv p).trans ((actualFacetEquiv p q e).trans (displayedFacetEquiv q).symm)

theorem labelEquiv_facet (p : RegularData d V) (q : RegularData d W)
    (e : RawFaces p ≃o RawFaces q) (i : V) :
    e (displayedFacet p i) = displayedFacet q (labelEquiv p q e i) := by
  have h := congrArg Subtype.val
    ((displayedFacetEquiv q).apply_symm_apply
      ((actualFacetEquiv p q e) ((displayedFacetEquiv p) i)))
  exact h.symm

def relabelData (p : HalfspaceData W (CanonicalModel.Space d)) (e : V ≃ W) :
    HalfspaceData V (CanonicalModel.Space d) := (fun i => p.1 (e i), fun i => p.2 (e i))

theorem dataRegion_relabelData (p : HalfspaceData W (CanonicalModel.Space d)) (e : V ≃ W) :
    dataRegion (relabelData p e) = dataRegion p := by
  ext x
  constructor
  · intro hx j
    change p.1 j x ≤ p.2 j
    have h := hx (e.symm j)
    change p.1 (e (e.symm j)) x ≤ p.2 (e (e.symm j)) at h
    simpa only [e.apply_symm_apply] using h
  · intro hx i
    exact hx (e i)

def relabelRegular (q : RegularData d W) (e : V ≃ W) : RegularData d V where
  data := relabelData q.data e
  normal_ne_zero i := q.normal_ne_zero (e i)
  compact := by
    rw [dataRegion_relabelData]
    exact q.compact
  full_dimensional := by
    rw [dataRegion_relabelData]
    exact q.full_dimensional
  strict_facet_point := by
    intro i
    obtain ⟨x, hx, hxi, hxs⟩ := q.strict_facet_point (e i)
    refine ⟨x, ?_, hxi, ?_⟩
    · rw [dataRegion_relabelData]
      exact hx
    · intro j hji
      exact hxs (e j) (e.injective.ne hji)

@[simp] theorem relabelRegular_region (q : RegularData d W) (e : V ≃ W) :
    dataRegion (relabelRegular q e).data = dataRegion q.data :=
  dataRegion_relabelData q.data e

def relabelFaceOrderIso (q : RegularData d W) (e : V ≃ W) :
    RawFaces q ≃o RawFaces (relabelRegular q e) where
  toFun F := ⟨F.val, by
    change IsExposed ℝ (dataRegion (relabelRegular q e).data) F.val
    rw [relabelRegular_region]
    exact F.property⟩
  invFun F := ⟨F.val, by
    have h := F.property
    change IsExposed ℝ (dataRegion (relabelRegular q e).data) F.val at h
    exact (congrArg (fun K : Set (CanonicalModel.Space d) => IsExposed ℝ K F.val)
      (relabelRegular_region q e)).mp h⟩
  left_inv F := Subtype.ext rfl
  right_inv F := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

theorem relabelFaceOrderIso_facet (q : RegularData d W) (e : V ≃ W) (i : V) :
    relabelFaceOrderIso q e (displayedFacet q (e i)) =
      displayedFacet (relabelRegular q e) i := by
  apply Subtype.ext
  change tightFace (fun j => (q.data.1 j).toLinearMap) q.data.2 {e i} =
    tightFace (fun j => ((relabelRegular q e).data.1 j).toLinearMap)
      (relabelRegular q e).data.2 {i}
  ext x
  simp only [tightFace, Set.mem_setOf_eq, Set.forall_mem_singleton]
  change (x ∈ dataRegion q.data ∧ q.data.1 (e i) x = q.data.2 (e i)) ↔
    (x ∈ dataRegion (relabelRegular q e).data ∧ q.data.1 (e i) x = q.data.2 (e i))
  rw [relabelRegular_region]

theorem relabelRegular_presentation_facet (q : RegularData d W) (e : V ≃ W) (i : V) :
    (presentation (relabelRegular q e)).facet i = (presentation q).facet (e i) := by
  simp only [presentation_facet, relabelRegular_region] <;> rfl

end NormalProjective.LabelTransport

namespace NormalProjective.CanonicalModel.Presentation

open UnitNormalization LabelTransport

variable {d : ℕ} {V W : Type*} [Fintype V] [Fintype W]

/-- The identical geometric presentation indexed by an equivalent label type. -/
def relabel (Q : Presentation d W) (e : V ≃ W) : Presentation d V :=
  presentation (relabelRegular (ofCanonical Q) e)

@[simp] theorem relabel_normal (Q : Presentation d W) (e : V ≃ W) (i : V) :
    (Q.relabel e).normal i = Q.normal (e i) := by
  change (presentation (ofCanonical Q)).normal (e i) = Q.normal (e i)
  rw [presentation_ofCanonical]

@[simp] theorem relabel_support (Q : Presentation d W) (e : V ≃ W) (i : V) :
    (Q.relabel e).support i = Q.support (e i) := by
  change (presentation (ofCanonical Q)).support (e i) = Q.support (e i)
  rw [presentation_ofCanonical]

@[simp] theorem relabel_carrier (Q : Presentation d W) (e : V ≃ W) :
    (Q.relabel e).carrier = Q.carrier := by
  change (presentation (relabelRegular (ofCanonical Q) e)).carrier = Q.carrier
  rw [presentation_carrier, relabelRegular_region,
    ← presentation_carrier (ofCanonical Q), presentation_ofCanonical]

@[simp] theorem relabel_facet (Q : Presentation d W) (e : V ≃ W) (i : V) :
    (Q.relabel e).facet i = Q.facet (e i) := by
  change (presentation (relabelRegular (ofCanonical Q) e)).facet i = Q.facet (e i)
  rw [relabelRegular_presentation_facet, presentation_ofCanonical]

@[simp] theorem relabel_symm (Q : Presentation d W) (e : V ≃ W) :
    (Q.relabel e).relabel e.symm = Q := by
  apply presentation_ext
  · funext i
    simp only [relabel_normal, e.apply_symm_apply]
  · funext i
    simp only [relabel_support, e.apply_symm_apply]

/-- Reindexing fixes the underlying point set of every actual face. -/
def relabelFaceEquiv (Q : Presentation d W) (e : V ≃ W) :
    Q.Faces ≃o (Q.relabel e).Faces where
  toFun F := ⟨F.val, by
    change IsExposed ℝ (Q.relabel e).carrier F.val
    rw [relabel_carrier]
    exact F.property⟩
  invFun F := ⟨F.val, by
    have h := F.property
    change IsExposed ℝ (Q.relabel e).carrier F.val at h
    exact (congrArg (fun K : Set (CanonicalModel.Space d) => IsExposed ℝ K F.val)
      (relabel_carrier Q e)).mp h⟩
  left_inv F := Subtype.ext rfl
  right_inv F := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

theorem SameLabelledType.relabel {P Q : Presentation d W}
    (e : V ≃ W) (h : P.SameLabelledType Q) :
    (P.relabel e).SameLabelledType (Q.relabel e) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨(relabelFaceEquiv P e).symm.trans
    (u.trans (relabelFaceEquiv Q e)), ?_⟩
  intro i
  obtain ⟨s, hsP, hsQ⟩ := hu (e i)
  refine ⟨relabelFaceEquiv P e s, ?_, ?_⟩
  · change s.val = (P.relabel e).facet i
    rw [relabel_facet]
    exact hsP
  · change (u s).val = (Q.relabel e).facet i
    rw [relabel_facet]
    exact hsQ

theorem Simple.relabel {Q : Presentation d W} (e : V ≃ W) (hQ : Q.Simple) :
    (Q.relabel e).Simple := by
  intro x hx
  have hxQ : x ∈ Q.carrier.extremePoints ℝ := by
    simpa only [relabel_carrier] using hx
  let f : {i : V // x ∈ (Q.relabel e).facet i} ≃ {j : W // x ∈ Q.facet j} :=
    { toFun := fun i => ⟨e i.val, by
        simpa only [relabel_facet] using i.property⟩
      invFun := fun j => ⟨e.symm j.val, by
        simpa only [relabel_facet, e.apply_symm_apply] using j.property⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_apply i.val)
      right_inv := fun j => Subtype.ext (e.apply_symm_apply j.val) }
  exact (Nat.card_congr f).trans (hQ x hxQ)

/-- An arbitrary actual face-order isomorphism induces a facet-label
equivalence making the two presentations have the same labelled type. -/
theorem exists_relabel_sameLabelledType (P : Presentation d V) (Q : Presentation d W)
    (e : P.Faces ≃o Q.Faces) : ∃ l : V ≃ W, P.SameLabelledType (Q.relabel l) := by
  let p := ofCanonical P
  let q := ofCanonical Q
  let e' : (presentation p).Faces ≃o (presentation q).Faces := by
    have hP : presentation p = P := presentation_ofCanonical P
    have hQ : presentation q = Q := presentation_ofCanonical Q
    exact (congrArg₂
      (fun (A : Presentation d V) (B : Presentation d W) => A.Faces ≃o B.Faces)
      hP hQ).mpr e
  let E : RawFaces p ≃o RawFaces q :=
    (faceOrderEquiv p).symm.trans (e'.trans (faceOrderEquiv q))
  let l := labelEquiv p q E
  refine ⟨l, ?_⟩
  have h : (presentation p).SameLabelledType (presentation (relabelRegular q l)) := by
    apply sameLabelledType_of_faceOrderIso p (relabelRegular q l)
      (E.trans (relabelFaceOrderIso q l))
    intro i
    change relabelFaceOrderIso q l (E (displayedFacet p i)) =
      displayedFacet (relabelRegular q l) i
    rw [labelEquiv_facet p q E i]
    exact relabelFaceOrderIso_facet q l i
  simpa only [p, q, relabel, presentation_ofCanonical] using h

end NormalProjective.CanonicalModel.Presentation

namespace NormalProjective.CanonicalModel.Realization

variable {d : ℕ} {V W : Type*} [Fintype V] [Fintype W]
  {R : Presentation d W}

/-- Apply one label equivalence to every realization in a labelled space. -/
def relabel (e : V ≃ W) (P : Realization R) : Realization (R.relabel e) :=
  ⟨P.val.relabel e, Presentation.SameLabelledType.relabel e P.property⟩

@[simp] theorem relabel_carrier (e : V ≃ W) (P : Realization R) :
    (relabel e P).carrier = P.carrier := P.val.relabel_carrier e

@[simp] theorem relabel_facet (e : V ≃ W) (P : Realization R) (i : V) :
    (relabel e P).facet i = P.facet (e i) := P.val.relabel_facet e i

theorem NormalStep.relabel (e : V ≃ W) {P Q : Realization R}
    (h : NormalStep P Q) : NormalStep (relabel e P) (relabel e Q) := by
  change (P.val.relabel e).normal = (Q.val.relabel e).normal
  funext i
  simpa only [Presentation.relabel_normal] using congrFun h (e i)

theorem normalStep_relabel_iff (e : V ≃ W) {P Q : Realization R} :
    NormalStep (relabel e P) (relabel e Q) ↔ NormalStep P Q := by
  constructor
  · intro h
    change (P.val.relabel e).normal = (Q.val.relabel e).normal at h
    change P.val.normal = Q.val.normal
    funext j
    simpa only [Presentation.relabel_normal, e.apply_symm_apply]
      using congrFun h (e.symm j)
  · exact NormalStep.relabel e

theorem ProjectiveStep.relabel (e : V ≃ W) {P Q : Realization R}
    (h : ProjectiveStep P Q) : ProjectiveStep (relabel e P) (relabel e Q) := by
  obtain ⟨M, hM, hd, hK, hF⟩ := h
  refine ⟨M, hM, ?_, ?_, ?_⟩
  · simpa only [relabel_carrier] using hd
  · simpa only [relabel_carrier] using hK
  · intro i
    simpa only [relabel_facet] using hF (e i)

theorem projectiveStep_relabel_iff (e : V ≃ W) {P Q : Realization R} :
    ProjectiveStep (relabel e P) (relabel e Q) ↔ ProjectiveStep P Q := by
  constructor
  · rintro ⟨M, hM, hd, hK, hF⟩
    refine ⟨M, hM, ?_, ?_, ?_⟩
    · simpa only [relabel_carrier] using hd
    · simpa only [relabel_carrier] using hK
    · intro i
      simpa only [relabel_facet, e.apply_symm_apply] using hF (e.symm i)
  · exact ProjectiveStep.relabel e

theorem affineRelated_relabel_iff (e : V ≃ W) {P Q : Realization R} :
    AffineRelated (relabel e P) (relabel e Q) ↔ AffineRelated P Q := by
  constructor
  · rintro ⟨a, hK, hF⟩
    refine ⟨a, ?_, ?_⟩
    · simpa only [relabel_carrier] using hK
    · intro i
      simpa only [relabel_facet, e.apply_symm_apply] using hF (e.symm i)
  · rintro ⟨a, hK, hF⟩
    refine ⟨a, ?_, ?_⟩
    · simpa only [relabel_carrier] using hK
    · intro i
      simpa only [relabel_facet] using hF (e i)

/-- Reindex every intermediate presentation, preserving both move counts. -/
theorem PNWord.relabel (e : V ≃ W) {P Q : Realization R} {p n : ℕ}
    (h : PNWord P Q p n) : PNWord (relabel e P) (relabel e Q) p n := by
  induction h with
  | nil P => exact PNWord.nil _
  | projective hs ht ih => exact PNWord.projective (ProjectiveStep.relabel e hs) ih
  | normal hs ht ih => exact PNWord.normal (NormalStep.relabel e hs) ih

theorem PNWord.of_relabel (e : V ≃ W) {P Q : Realization R} {p n : ℕ}
    (h : PNWord (Realization.relabel e P) (Realization.relabel e Q) p n) :
    PNWord P Q p n := by
  have hRR : R.SameLabelledType ((R.relabel e).relabel e.symm) := by
    rw [Presentation.relabel_symm]
    exact Presentation.sameLabelledType_refl R
  have hP : Realization.rebase hRR
      (Realization.relabel e.symm (Realization.relabel e P)) = P := by
    apply Subtype.ext
    exact Presentation.relabel_symm P.val e
  have hQ : Realization.rebase hRR
      (Realization.relabel e.symm (Realization.relabel e Q)) = Q := by
    apply Subtype.ext
    exact Presentation.relabel_symm Q.val e
  have hh := (h.relabel e.symm).rebase hRR
  simpa only [hP, hQ] using hh

theorem pnWord_relabel_iff (e : V ≃ W) {P Q : Realization R} {p n : ℕ} :
    PNWord (relabel e P) (relabel e Q) p n ↔ PNWord P Q p n :=
  ⟨PNWord.of_relabel e, PNWord.relabel e⟩

theorem pnRelated_relabel_iff (e : V ≃ W) {P Q : Realization R} :
    PNRelated (relabel e P) (relabel e Q) ↔ PNRelated P Q := by
  constructor
  · rintro ⟨p, n, h⟩
    exact ⟨p, n, h.of_relabel e⟩
  · rintro ⟨p, n, h⟩
    exact ⟨p, n, h.relabel e⟩

end NormalProjective.CanonicalModel.Realization

namespace NormalProjective

open CanonicalModel CanonicalModel.Realization

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Corollary 2 for arbitrary facet-label types and an unlabelled actual
face-order isomorphism. The terminal carrier is literally the carrier of `Q`. -/
theorem simple_three_faceOrderIso_pn (P : Presentation 3 V) (Q : Presentation 3 W)
    (hP : P.Simple) (e : P.Faces ≃o Q.Faces) :
    ∃ (l : V ≃ W) (h : P.SameLabelledType (Q.relabel l)),
      (Q.relabel l).carrier = Q.carrier ∧
      PNRelated (⟨P, Presentation.sameLabelledType_refl P⟩ : Realization P)
        ⟨Q.relabel l, h⟩ := by
  obtain ⟨l, h⟩ := Presentation.exists_relabel_sameLabelledType P Q e
  exact ⟨l, h, Q.relabel_carrier l, simple_three_presentations_pn P (Q.relabel l) hP h⟩

end NormalProjective

namespace NormalProjective.CubeUpper

open CanonicalModel CanonicalModel.Realization CyclicCube

/-- The paper's ambient dimension `d ≥ 2` is exactly the cube parameter
`n ≥ 1` used by the verified constructions, with `d = n + 1`. -/
theorem cube_dimension_parameter_iff (d : ℕ) :
    2 ≤ d ↔ ∃ n : ℕ, 1 ≤ n ∧ d = n + 1 := by
  constructor
  · intro hd
    refine ⟨d - 1, ?_, ?_⟩ <;> omega
  · rintro ⟨n, hn, rfl⟩
    omega

/-- The projective, normal, and total move counts agree exactly after the
same dimension substitution; natural-number subtraction is accounted for. -/
theorem cube_move_counts_reindex {n : ℕ} (hn : 1 ≤ n) :
    n = (n + 1) - 1 ∧ n - 1 = (n + 1) - 2 ∧
      n + (n - 1) = 2 * (n + 1) - 3 := by
  omega

/-- The exact-count upper bound for an arbitrary geometric cube presentation.
The facet alignment is derived from the actual face-order isomorphism; the word
starts at `P` itself and ends at the paper's literal centred cube carrier. -/
theorem every_cube_exact_word_of_faceOrderIso
    {V : Type*} [Fintype V] {n : ℕ} (hn : 1 ≤ n)
    (P : Presentation (n + 1) V)
    (e : P.Faces ≃o (referenceCube n).Faces) :
    ∃ (Q : Presentation (n + 1) V) (hPQ : P.SameLabelledType Q),
      Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
      PNWord (⟨P, Presentation.sameLabelledType_refl P⟩ : Realization P)
        ⟨Q, hPQ⟩ n (n - 1) := by
  obtain ⟨l, h⟩ := Presentation.exists_relabel_sameLabelledType
    (referenceCube n) P e.symm
  let P₀ : Realization (referenceCube n) := ⟨P.relabel l, h⟩
  have hRP : ((referenceCube n).relabel l.symm).SameLabelledType P := by
    simpa only [Presentation.relabel_symm] using
      (Presentation.SameLabelledType.relabel l.symm h)
  let Q : Presentation (n + 1) V := (centeredRealization n).val.relabel l.symm
  have hPQ : P.SameLabelledType Q := hRP.symm.trans
    (Presentation.SameLabelledType.relabel l.symm (centeredRealization n).property)
  have hword := ((every_cube_exact_word hn P₀).relabel l.symm).rebase hRP.symm
  have hstart : rebase hRP.symm (Realization.relabel l.symm P₀) =
      (⟨P, Presentation.sameLabelledType_refl P⟩ : Realization P) := by
    apply Subtype.ext
    exact Presentation.relabel_symm P l
  have hend : rebase hRP.symm (Realization.relabel l.symm (centeredRealization n)) =
      (⟨Q, hPQ⟩ : Realization P) := Subtype.ext rfl
  refine ⟨Q, hPQ, ?_, ?_⟩
  · calc
      Q.carrier = (centeredRealization n).val.carrier :=
        Presentation.relabel_carrier _ l.symm
      _ = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) :=
        centeredRealization_carrier n
  · simpa only [hstart, hend] using hword

end NormalProjective.CubeUpper

end

#print axioms NormalProjective.simple_three_pn_unique
#print axioms NormalProjective.simple_three_presentations_pn
#print axioms NormalProjective.simple_three_faceOrderIso_pn
#print axioms NormalProjective.CubeUpper.every_cube_exact_word_of_faceOrderIso
#print axioms NormalProjective.FiniteHullModel.finite_hull_has_facet_model_all_dimensions

/-! Read-only actual-body audit; generated from the canonical project root. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`cor2_complete]
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let isLocal (n : Name) : Bool := localModules.contains (moduleOf n)
  let names := env.checked.get.constants.foldStage2
    (fun ns n _ => ns.push n) (#[] : Array Name)
  let names := names.qsort Name.lt
  let mut records : Array Json := #[]
  let mut boundaries : NameSet := {}
  for n in names do
    let some ci := env.find? n | throwError "Missing imported declaration {n}"
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (ci.value? true).isSome do
          throwError "Local proof or definition body unavailable: {n}"
    | .axiomInfo _ => throwError "Local axiom declaration is forbidden: {n}"
    | _ => pure ()
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom {ax} in {n}"
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    let ctorDeps := match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    let deps := (typeDeps ++ valueDeps ++ ctorDeps).foldl (fun s x => s.insert x) ({} : NameSet)
    for d in deps.toArray do
      unless isLocal d do boundaries := boundaries.insert d
    let typeString ← liftTermElabM <| return (← Meta.ppExpr ci.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("type", toJson typeString),
      ("proof_or_definition_body_available", toJson (ci.value? true).isSome),
      ("direct_dependencies", toJson (deps.toArray.qsort Name.lt |>.map Name.toString)),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let mut boundaryRecords : Array Json := #[]
  for n in boundaries.toArray.qsort Name.lt do
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved library-boundary axiom {ax} in {n}"
    boundaryRecords := boundaryRecords.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [
    ("lean_version", toJson "4.35.0"),
    ("mathlib_commit", toJson "56a005855ea17e0b0958f73ec801ae140b0a1679"),
    ("local_modules", toJson (localModules.map Name.toString)),
    ("local_declarations", Json.arr records),
    ("pinned_library_boundary", Json.arr boundaryRecords),
    ("unapproved_axioms", Json.arr #[])]
  IO.FS.createDirAll ".lake/reports/audit/final"
  IO.FS.writeFile ".lake/reports/audit/final/Cor2Complete_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
