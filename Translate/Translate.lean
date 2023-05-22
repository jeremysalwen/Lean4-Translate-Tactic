import Lean
import Std.Data.Array.Init.Lemmas
import Std.Data.Array.Lemmas
import Mathlib.Tactic.Find
import Mathlib.Tactic.Simps.Basic
import Lean.Elab.Term
import Translate.SimpAttrs

open Lean Meta Elab Term Lean.Meta Tactic


def transformEtaReduce (e : Expr) : MetaM Expr := do
  transform e fun node => pure <| TransformStep.continue node.etaExpanded?

def betaReduceHead (e:Expr): Expr :=
  if e.isHeadBetaTarget then e.headBeta else e

def onlySimp (lemmas: List Name) (e: Expr) : MetaM Simp.Result :=
  simpOnlyNames lemmas e
    (config := { decide := false })

-- The same as in mathlib addRelatedDef, except we don't look up the defintion,
-- but pass a const to the construct function.  Also we don't apply attrs to source definition :D
def addRelatedThm (src : Name) (suffix : String) (ref : Syntax)
    (attrs? : Option (Syntax.TSepArray `Lean.Parser.Term.attrInstance ","))
    (construct : Expr → Expr → List Name → MetaM (Expr × List Name)) :
    MetaM Unit := do
  let tgt := match src with
    | Name.str n s => Name.mkStr n $ s ++ suffix
    | x => .str x suffix
  addDeclarationRanges tgt {
    range := ← getDeclarationRange (← getRef)
    selectionRange := ← getDeclarationRange ref }
  let info ← getConstInfo src
  let (newValue, newLevels) ← construct info.type (← mkConstWithLevelParams @src) info.levelParams
  let newValue ← instantiateMVars newValue
  let newType ← instantiateMVars (← inferType newValue)
  match info with
  | ConstantInfo.thmInfo info =>
    addAndCompile <| .thmDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
  | ConstantInfo.defnInfo info =>
    -- Structure fields are created using `def`, even when they are propositional,
    -- so we don't rely on this to decided whether we should be constructing a `theorem` or a `def`.
    addAndCompile <| if ← isProp newType then .thmDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
      else .defnDecl
      { info with levelParams := newLevels, type := newType, name := tgt, value := newValue }
  | _ => throwError "Constant {src} is not a theorem or definition."
  if isProtected (← getEnv) src then
    setEnv $ addProtected (← getEnv) tgt
  let attrs := match attrs? with | some attrs => attrs | none => #[]
  _ ← Term.TermElabM.run' <| do
    let attrs ← elabAttrs attrs
    Term.applyAttributes tgt attrs


def upLemmaAttrs : MetaM (Syntax.TSepArray `Lean.Parser.Term.attrInstance ",") := do
  let arr : Syntax.TSepArray `Lean.Parser.Term.attrInstance "," := ∅
  let arr := arr.push (← `(Lean.Parser.Term.attrInstance|array_to_list))
  return arr


def countFnsFromTypeAux (e : Expr) (ty: Expr) (exclude: List Name) : StateT ℕ MetaM Unit := do
  e.forEach fun subExpr => do
    match subExpr.getAppFnArgs with
    | (f, args ) =>
      if f ∉ exclude then
        args.forM (λ arg => do
          let (mvars, _, _) ← forallMetaTelescope (← inferType ty)
          if ← withoutModifyingEnv (isDefEq (mkAppN ty mvars) (← inferType arg)) then
            modify Nat.succ
        )

def countFnCallsAux (e : Expr) (fns: List Name) : StateT ℕ MetaM Unit := do
  e.forEach fun subExpr => do
    match subExpr.getAppFnArgs with
    | (f, _) =>
      if f ∈  fns then
        modify Nat.succ

def countFnsFromType(e: Expr) (ty: Expr) (exclude: List Name) : MetaM ℕ  := do
  let initialState := 0
  let (_, finalState) ← (countFnsFromTypeAux e ty exclude).run initialState
  return finalState

def countFnCalls (e : Expr) (fns: List Name) : MetaM ℕ := do
  let initialState := 0
  let (_, finalState) ← (countFnCallsAux e fns).run initialState
  return finalState

def fillImplicitArgsWithMVars (e: Expr): MetaM Expr := do
  forallTelescope (← inferType e) (fun xs _ => do
    let mut result := e
    for x in xs do
      if ¬ (← x.fvarId!.getBinderInfo).isExplicit then
        result := mkApp result (← mkFreshExprMVar (← x.fvarId!.getType))
    pure result
  )

def translateLemma (srcType: Name) (f r: Name) (roundtrip1 roundtrip2: Name) (lem: Name) : MetaM Unit := do
  addRelatedThm lem "_up" (← getRef) (← upLemmaAttrs)
    fun t value levels => do
      let transformed ←  forallTelescope t (fun xs ty => do
        match ty.getAppFnArgs with
          | (``Eq, #[α, lhs, rhs]) => do
            if (← countFnsFromType lhs (← mkConst' srcType) [f]) > (← countFnsFromType rhs (← mkConst' srcType) [f]) && (← countFnCalls ty [f]) > 0 then
              let mut e := (mkAppN value xs)
              if lhs.isAppOf f then
                let r ← fillImplicitArgsWithMVars (← mkConst' r)
                if (← isDefEq (← inferType r) (← mkArrow α (← mkFreshTypeMVar))) then
                  e ← mkCongrArg r e
                  e ← simpType (onlySimp [roundtrip1, roundtrip2]) e

              for x in xs.reverse do
                e ← mkLambdaFVars #[x] e
                if (← x.fvarId!.getBinderInfo).isExplicit then
                  e ← mkFunExt e
              
              e ← transformEtaReduce e 
              e ← simpType (onlySimp []) e
              pure e
            else
              throwError "Does not reduce operations on the source type"
          | _ => throwError "Can only handle hypotheses of the form `a = b`"
      )
      pure (transformed, levels)

elab "#translateLemma" srcType:ident " x " f:ident " x " r:ident " x " roundtrip1:ident " x " roundtrip2:ident " x " e:ident: command => Elab.Command.liftTermElabM do
  translateLemma srcType.getId f.getId r.getId roundtrip1.getId roundtrip2.getId e.getId

elab "#translateSimpLemmas" srcType:ident f:ident r:ident roundtrip1:ident roundtrip2:ident : command => Elab.Command.liftTermElabM do
  Term.applyAttributes roundtrip1.getId (← elabAttrs (← upLemmaAttrs))
  Term.applyAttributes roundtrip2.getId (← elabAttrs (← upLemmaAttrs))
  let allSimpDecls ← getAllSimpDecls `simp

  for lem in allSimpDecls do
    try
      commitIfNoEx do
        translateLemma srcType.getId f.getId r.getId roundtrip1.getId roundtrip2.getId lem
    catch _ =>
      continue
