import Lean
import Lean.DeclarationRange
import ImportGraph.Imports.RequiredModules
import Mathlib.Lean.Expr.Basic

open Lean Lean.Elab Lean.Elab.Command

namespace DeclarationReachability

/--
The declaration-granularity form of importGraph's
`NameSet.transitivelyUsedConstants`: traverse the same
`ConstantInfo.getUsedConstantsAsSet` edges with an explicit work set, but retain
constant names rather than aggregating them to their defining modules.
-/
def transitivelyUsedConstants (root : Name) : CoreM NameSet := do
  let mut visited : NameSet := {}
  let mut pending : NameSet := {root}
  while !pending.isEmpty do
    let current := pending.min!
    pending := pending.erase current
    if !visited.contains current then
      visited := visited.insert current
      for used in (← getConstInfo current).getUsedConstantsAsSet do
        if !visited.contains used then
          pending := pending.insert used
  return visited

/-- Public, non-internal constants recorded as defined by `moduleName`. -/
def declarationsInModule (env : Environment) (moduleName : Name) : CoreM NameSet := do
  let some moduleIdx := env.header.moduleNames.idxOf? moduleName
    | return {}
  let mut result : NameSet := {}
  for declaration in env.header.moduleData[moduleIdx]!.constNames do
    if !(← declaration.isBlackListed) && (← findDeclarationRanges? declaration).isSome then
      result := result.insert declaration
  return result

private def printNames (heading : String) (names : NameSet) : CommandElabM Unit := do
  logInfo m!"{heading} ({names.size})"
  for name in names do
    logInfo m!"  {name}"

syntax (name := declarationReachabilityStx)
  "#declaration_reachability " ident " in " "[" ident,* "]" : command

syntax (name := declarationReachabilityUnionStx)
  "#declaration_reachability_union " "[" ident,* "]" " in " "[" ident,* "]" : command

/--
Print the transitive constant closure of a declaration, restricted to each
listed module, followed by the complementary module declarations (orphans).
-/
elab_rules : command
  | `(#declaration_reachability $target:ident in [$modules:ident,*]) => do
      let targetName := target.getId
      let env ← getEnv
      let closure ← liftCoreM <| transitivelyUsedConstants targetName
      logInfo m!"TARGET {targetName}"
      logInfo m!"TRANSITIVE_CLOSURE_ALL_MODULES ({closure.size})"
      for moduleStx in modules.getElems do
        let moduleName := moduleStx.getId
        let declarations ← liftCoreM <| declarationsInModule env moduleName
        let reachable := declarations.foldl (init := {}) fun acc name =>
          if closure.contains name then acc.insert name else acc
        let orphans := declarations.foldl (init := {}) fun acc name =>
          if closure.contains name then acc else acc.insert name
        logInfo m!"MODULE {moduleName} TOTAL ({declarations.size})"
        printNames "REACHABLE" reachable
        printNames "ORPHANS" orphans

  | `(#declaration_reachability_union [$targets:ident,*] in [$modules:ident,*]) => do
      let env ← getEnv
      let mut closure : NameSet := {}
      logInfo m!"TARGET_UNION"
      for targetStx in targets.getElems do
        let targetName := targetStx.getId
        logInfo m!"  {targetName}"
        closure := closure.union (← liftCoreM <| transitivelyUsedConstants targetName)
      logInfo m!"TRANSITIVE_CLOSURE_ALL_MODULES ({closure.size})"
      for moduleStx in modules.getElems do
        let moduleName := moduleStx.getId
        let declarations ← liftCoreM <| declarationsInModule env moduleName
        let reachable := declarations.foldl (init := {}) fun acc name =>
          if closure.contains name then acc.insert name else acc
        let orphans := declarations.foldl (init := {}) fun acc name =>
          if closure.contains name then acc else acc.insert name
        logInfo m!"MODULE {moduleName} TOTAL ({declarations.size})"
        printNames "REACHABLE" reachable
        printNames "ORPHANS" orphans

end DeclarationReachability
