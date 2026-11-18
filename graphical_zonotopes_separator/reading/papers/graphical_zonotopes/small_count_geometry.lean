module

public import Papers.GraphicalZonotopes.SmallCountModules
public import Papers.GraphicalZonotopes.UnitBookGeometry
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Pointwise

/-- The complete geometric construction associated with a proper nonempty
complete-multipartite pair pattern. The finite-type transport labels exactly
one outer vertex per Boolean column; it does not change the ambient graph. -/
theorem lattice_book_of_complement_family {s k : ℕ} (hs : 3≤s)
    (blocks : Finset (Finset (Fin s)))
    (hb : ComplementFamily (univ : Finset (Fin s)) blocks)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph (Fin s)),e∉crossingPairs blocks)
    (hcard : (crossingPairs blocks).card+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  have hsf : 3≤Fintype.card (Fin s):=by simpa using hs
  have hk : 0<k:=by omega
  letI : Nonempty (Fin s):=⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  have hJ : Fintype.card (Branch blocks)=k := by
    simpa only [Branch,Fintype.card_option,Fintype.card_coe] using hcard
  let e : Fin k≃Branch blocks:=
    (finCongr hJ.symm).trans (Fintype.equivFin (Branch blocks)).symm
  let F : Fin k → SetFunction (Fin s):=fun i => modules blocks (e i)
  have hF : ∀ i,IsMonotoneBoolean (F i):=fun i => modules_boolean hb hsf (e i)
  have hess : ∀ i a,Essential (F i) a:=fun i a => modules_essential hb hsf (e i) a
  obtain ⟨z,hzn,hzc⟩:=unit_integrable hb hsf hproper
  have hc : Compatible z F (fun _ => 1) := by
    apply (compatible_reindex e z (modules blocks) (fun _ => 1)).mpr
    exact hzc
  have huniq : UniqueIntegrableRelation F (fun _ => 1) := by
    intro t ht
    obtain ⟨u,hun,huc⟩:=ht
    have hold : Compatible u (modules blocks) (fun j => t (e.symm j)) :=
      (compatible_reindex e u (modules blocks) t).mp huc
    obtain ⟨c,hc⟩:=unit_unique hb hsf hproper (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,smul_eq_mul,mul_one] using congrFun hc (e i)
  exact lattice_book_of_unit_modules (by omega) hk F hF hess ⟨z,hzn,hc⟩ huniq

end SmallCount
end BooleanModule
end GraphicalZonotopes
