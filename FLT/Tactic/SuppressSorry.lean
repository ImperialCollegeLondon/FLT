import Lean.Elab.Command
open Lean
open Elab Command

register_option suppressSorry : Bool := {
  defValue := false
  descr := "suppress sorry warnings"
}

initialize
  have wrap m stx := do
    m stx
    if suppressSorry.get (← getOptions) then
      let msgs := (← get).messages ++
        (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) {}
      modify ({ · with messages := msgs, snapshotTasks := #[] })
      if msgs.hasUnreported then
        modify fun s => { s with
          messages.unreported := s.messages.unreported.filter fun m =>
            !(m.severity matches .warning && m.data.hasTag (· == `hasSorry)) }
  have wrapEntry wrap := .map fun e => { e with value := wrap e.value }
  have { defn, ext, .. } := commandElabAttribute
  have wrapAttrsMap m := m.modify defn.name fun v =>
    let add declName stx attrKind := do
      let key ← defn.evalKey false stx
      let .none := IR.getSorryDep (← getEnv) declName | return
      let val ← unsafe evalConstCheck CommandElab defn.valueTypeName declName
      ext.add { key := key, declName := declName, value := wrap val } attrKind
      defn.onAdded false declName
    { v with add }
  let hooked ← IO.mkRef false
  have hook m stx := do
    if !(← hooked.get) then
      hooked.set true
      modifyEnv fun env => attributeExtension.modifyState env fun s =>
        { s with map := wrapAttrsMap s.map }
    m stx
  have wrapTable₁ wrap ks r :=
    { r with map₁ := ks.foldl (fun map k => map.modify k (wrapEntry wrap)) r.map₁ }
  commandElabAttribute.tableRef.modify fun r =>
    let r := wrapTable₁ wrap [``Parser.Command.declaration] r
    wrapTable₁ hook [``Parser.Command.attribute] r
