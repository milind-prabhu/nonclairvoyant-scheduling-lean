import Scheduling
import Lean.Util.FoldConsts

open Lean Elab Command

elab "#export_scheduling_dependencies" : command => do
  let env ← getEnv
  let namesText ← IO.FS.readFile "blueprint/source_names.txt"
  let targets := namesText.splitOn "\n"
  let rows ← liftTermElabM do
    let mut rows : Array Json := #[]
    for (n, c) in env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
      let name := n.toString
      if name.startsWith "Scheduling." || name.startsWith "_private.Scheduling." then
        let used := (c.getUsedConstantsAsSet.toArray.map (fun n => n.toString)).qsort (· < ·)
        let kind := match c with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque"
          | _ => "other"
        let statement ← if targets.contains name || targets.any (fun t => !t.isEmpty && name.endsWith ("." ++ t)) then
          pure (← Meta.ppExpr c.type).pretty
          else pure ""
        rows := rows.push <| Json.mkObj [
          ("name", .str name), ("kind", .str kind),
          ("used", .arr (used.map Json.str)), ("statement", .str statement)]
    pure rows
  IO.FS.writeFile "blueprint/compiled_dependencies.json" (Json.arr rows).pretty
  logInfo m!"Exported {rows.size} project declarations from the compiled Lean environment."

#export_scheduling_dependencies
