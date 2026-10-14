import Gluck.Smooth.Assembly
import Gluck.Regularity.SphereUnrestricted
import Lean

/-!
# The shared mixed-curvature construction: kernel dependency audit

Run `lake env lean scripts/audits/spaceform-mixed-anchor.lean` after building.
Every endpoint must use the common profile-window producer, exact control closing,
and the paused-anchor simplicity argument. The audit follows both declaration types
and proof terms, including private declarations; an import alone cannot satisfy it.
It also rejects the retired geometry-specific closing capstones and any axiom outside
`propext`, `Classical.choice`, and `Quot.sound`.

Only project declarations need dependency traversal: declarations from Lean and Mathlib
cannot refer to declarations in their downstream importing project. The axiom audit is
fully transitive, without this project filter. Direct dependencies are cached across roots so large shared
proof terms are scanned once. Historical blueprint snapshots are untouched.
-/

open Lean Elab Command

namespace SpaceformMixedAnchorAudit

private def isProjectDeclaration (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some index =>
    let moduleName := env.header.moduleNames[index]!.toString
    moduleName.startsWith "Gluck" || moduleName.startsWith "ForMathlib"
  | none => false

/-- Match the terminal component so private-name numbering cannot hide a retired producer. -/
private def isRetiredClosing (name : Name) : Bool :=
  #["exists_closingParam", "exists_closingParamWith", "exists_layout_closing",
    "exists_layout_closingWith", "mixed_spherical_endpoint_winding",
    "mixed_spherical_endpoint_winding_with_property"].any
    fun suffix => name.toString.endsWith ("." ++ suffix)

private def requiredConstruction : Array Name := #[
  `Gluck.ArcChain.exists_realization_of_profile_window,
  `Gluck.ArcChain.exists_realization_of_regularAnchor,
  `Gluck.ArcChain.exists_profile_regularAnchor,
  `Gluck.ArcChain.exists_closed_concentration,
  `Gluck.ArcChain.eventually_simple_concentration,
  `Gluck.ArcChain.exists_chainControlStabilityRadius,
  `Gluck.ArcChain.controlFlow_isFrame]

private def endpoints : Array Name := #[
  `Gluck.ArcChain.exists_realization_of_profile_window,
  `Gluck.dahlberg_converse,
  `Gluck.spherical_dahlberg_converse,
  `Gluck.spherical_dahlberg_converse_unrestricted,
  `Gluck.Hyperbolic.dahlberg_converse,
  `Gluck.hyperbolic_dahlberg_converse,
  `Gluck.dahlberg_converse_smooth,
  `Gluck.spherical_dahlberg_converse_smooth,
  `Gluck.spherical_dahlberg_converse_unrestricted_smooth,
  `Gluck.hyperbolic_dahlberg_converse_smooth,
  `Gluck.dahlberg_converse_rgc2,
  `Gluck.spherical_dahlberg_converse_rgc2,
  `Gluck.spherical_dahlberg_converse_unrestricted_rgc2,
  `Gluck.hyperbolic_dahlberg_converse_rgc2]

elab "audit_spaceform_mixed_anchor" : command => do
  let env ← getEnv
  let mut dependencyCache : NameMap (Array Name) := {}
  for root in endpoints do
    unless isProjectDeclaration env root do
      throwError "Missing project endpoint {root}"
    let axioms ← Lean.collectAxioms root
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {root}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    let mut count : Nat := 0
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if isRetiredClosing name then
        throwError "Retired closing producer {name} remains a kernel dependency of {root}"
      unless isProjectDeclaration env name do continue
      count := count + 1
      let mut dependencies : Array Name := #[]
      if let some cached := dependencyCache.find? name then
        dependencies := cached
      else
        let some info := env.find? name | throwError "Missing declaration {name}"
        dependencies := (info.type.getUsedConstants ++
          ((info.value? true).map Expr.getUsedConstants).getD #[]).filter
          (isProjectDeclaration env)
        dependencyCache := dependencyCache.insert name dependencies
      pending := pending ++ dependencies
    for required in requiredConstruction do
      unless visited.contains required do
        throwError "{root} does not use the shared construction declaration {required}"
    logInfo m!"PASS {root}: {count} project dependencies; shared construction present; \
      retired closing absent; axioms: {axioms}"

end SpaceformMixedAnchorAudit

audit_spaceform_mixed_anchor
