module
public import sunlet
import all sunlet
public meta import Lean
open Lean Meta Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for n in #[`Sunlet.paper_theorem_1_1, `Sunlet.GroupCoordinates.paper_theorem_1_1_original_coordinates, `Sunlet.paper_theorem_2_3_literal, `Sunlet.ComplexPaper.generic_unique_unordered_decomposition, `Sunlet.ComplexPaper.normalized_generic_degree, `Sunlet.ComplexPaper.normalized_isGalois, `Sunlet.ComplexPaper.paper_theorem_4_2_algebraic_fibers, `Sunlet.NormalizedLatinSystem.model_rational, `Sunlet.ComplexPaper.paper_corollary_5_1_point_ambiguity, `Sunlet.ComplexPaper.paper_corollary_5_1_degree, `Sunlet.CyclicSelectedField.paper_theorem_6_1_all_orders, `Sunlet.OrbitClasses.paper_theorem_7_1, `Sunlet.OrbitHeight.inverse_stable_original_coordinates_order_free, `Sunlet.OrbitClasses.paper_corollary_7_4, `Sunlet.NetworkTheorem.paper_corollary_8_1_leaf_cut, `Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted_leaf_cut, `Sunlet.addTranslationPerm_apply, `Sunlet.ToricPairAlgebra.genericVariable_ne_zero, `Sunlet.ToricPairAlgebra.embeddedTorus_base, `Sunlet.CyclicSparseWitness.shift_ne_zero, `Sunlet.NormalizedLatinSystem.generic_normalized_equation_iff, `PolynomialImage.rational_form_of_mem, `Sunlet.CyclicSelectedField.observedNormalizedField_eq_modelImageField, `Sunlet.ComplexPaper.normalizedGaloisEquiv] do
    let some info := env.checked.get.find? n | throwError "No checked constant {n}"
    let typeText ← liftTermElabM do
      withOptions (fun o => o.setBool `pp.all true) do
        return (← ppExpr info.type).pretty
    let origin := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.toString
      | none => env.mainModule.toString
    let kind := match info with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | _ => "other"
    let mut fields := [("name", toJson n.toString), ("origin", toJson origin),
      ("kind", toJson kind), ("type", toJson typeText),
      ("type_raw", toJson info.type.dbgToString),
      ("type_constants", toJson (info.type.getUsedConstants.map Name.toString)),
      ("type_hash", toJson (hash info.type).toNat),
      ("levels", toJson (info.levelParams.map Name.toString))]
    match info with
    | .defnInfo d =>
      let hints := match d.hints with
        | .opaque => "opaque"
        | .abbrev => "abbrev"
        | .regular h => "regular " ++ toString h.toNat
      fields := fields ++ [("hints", toJson hints), ("safety", toJson (reprStr d.safety)),
        ("value_raw", toJson d.value.dbgToString),
        ("value_constants", toJson (d.value.getUsedConstants.map Name.toString))]
    | _ => pure ()
    logInfo m!"PALOMAR_CONSTINFO {(Json.mkObj fields).compress}"
