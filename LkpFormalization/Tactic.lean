import Lean
import LkpFormalization.Basic

open Lean Meta Elab Term

inductive PTree (α : Type) where
  | empty : PTree α
  | goal (value : α) : PTree α
  | node (left : PTree α) (value : α) (right : PTree α)
  deriving Inhabited, Repr

inductive Ctx (α : Type) where
  | top : Ctx α
  | inLeft : Ctx α → α → PTree α → Ctx α
  | inRight : PTree α → α → Ctx α → Ctx α
  deriving Inhabited

structure Zipper (α : Type) where
  focus : PTree α
  ctx   : Ctx α

section

variable {α : Type}

def PTree.goals : PTree α → List α
  | empty       => []
  | goal a      => [a]
  | node l _ r  => l.goals ++ r.goals

def Ctx.plug : Ctx α → PTree α → PTree α
  | top, t            => t
  | inLeft c a r, t   => c.plug (.node t a r)
  | inRight l a c, t  => c.plug (.node l a t)

namespace Zipper

def ofTree (t : PTree α) : Zipper α := ⟨t, .top⟩
def toTree (z : Zipper α) : PTree α := z.ctx.plug z.focus
def goals (z : Zipper α) : List α := z.toTree.goals

def up? (z : Zipper α) : Option (Zipper α) :=
  match z.ctx with
  | .top => none
  | .inLeft c a r => some ⟨.node z.focus a r, c⟩
  | .inRight l a c => some ⟨.node l a z.focus, c⟩

def firstGoalIn : PTree α → Ctx α → Option (Zipper α)
  | .empty, _ => none
  | .goal a, c => some ⟨.goal a, c⟩
  | .node l a r, c =>
    match firstGoalIn l (.inLeft c a r) with
    | some z => some z
    | none => firstGoalIn r (.inRight l a c)

def goLeft? (z : Zipper α) : Option (Zipper α) :=
  match z.focus with
  | .node l a r => firstGoalIn l (.inLeft z.ctx a r)
  | _ => none

def goRight? (z : Zipper α) : Option (Zipper α) :=
  match z.focus with
  | .node l a r => firstGoalIn r (.inRight l a z.ctx)
  | _ => none

def nextIn : PTree α → Ctx α → Option (Zipper α)
  | _, .top => none
  | t, .inLeft c a r =>
    match firstGoalIn r (.inRight t a c) with
    | some z => some z
    | none => nextIn (.node t a r) c
  | t, .inRight l a c => nextIn (.node l a t) c

def nextGoal? (z : Zipper α) : Option (Zipper α) := nextIn z.focus z.ctx

end Zipper
end

abbrev DerivM := StateT (Zipper Expr) TermElabM

/-! ## Partial tree visualization in the Infoview

After each `lk_derive` tactic, the tree is drawn with `curryst` (via
`TypstInfoview`) and attached to that tactic's syntax: the Infoview displays it
when the cursor is on its line. Thus, placing the cursor on a tactic shows the
tree as it looks *after* that tactic is applied.

Color convention: open goal = dashed blue box; focus = orange box;
closed nodes = no box. -/

register_option lk.showTree : Bool := {
  defValue := true
  descr := "Mostrar en el Infoview el árbol parcial después de cada táctica de `lk_derive`."
}

register_option lk.curryst : String := {
  defValue := "@preview/curryst:0.6.0"
  descr := "Paquete de Typst con el que se dibujan los árboles (se importan `rule` y `prooftree`)."
}

/-- How a node's sequent is rendered. -/
inductive Mark where
  | closed  -- already-derived node
  | goal    -- open goal
  | focus   -- current focus

/-- Typst (math mode) for a sequent, using the `ToTypst Sequent` instance.
The instance is specified explicitly with `α := Sequent`: the `Expr` received here is
usually in normal form (`Prod.mk ..`), and type inference would otherwise select the
instance for `α × β` instead of the one for `Sequent`. -/
unsafe def seqToTypstUnsafe (s : Expr) : MetaM String := do
  let s ← instantiateMVars s
  let e ← mkAppOptM ``ToTypst.toTypst #[some (Lean.mkConst ``Sequent), none, some s]
  evalExpr String (Lean.mkConst ``String) e

@[implemented_by seqToTypstUnsafe]
opaque seqToTypst (s : Expr) : MetaM String

/-- If the sequent cannot be evaluated (free variables, metavariables, ...), render
Lean's pretty-printer output as text. -/
def renderSeq (s : Expr) : MetaM String := do
  try seqToTypst s
  catch _ => return "\"" ++ Typst.escapeString s!"{← ppExpr s}" ++ "\""

def PTree.style (f : Expr → MetaM String) : PTree Expr → MetaM (PTree (Mark × String))
  | .empty => return .empty
  | .goal a => return .goal (.goal, ← f a)
  | .node l a r => return .node (← l.style f) (.closed, ← f a) (← r.style f)

def Ctx.style (f : Expr → MetaM String) : Ctx Expr → MetaM (Ctx (Mark × String))
  | .top => return .top
  | .inLeft c a r => return .inLeft (← c.style f) (.closed, ← f a) (← r.style f)
  | .inRight l a c => return .inRight (← l.style f) (.closed, ← f a) (← c.style f)

def PTree.markRoot (m : Mark) : PTree (Mark × String) → PTree (Mark × String)
  | .goal (_, s) => .goal (m, s)
  | .node l (_, s) r => .node l (m, s) r
  | .empty => .empty

/-- Typst code (code expression) for a sequent according to its mark. -/
def Mark.wrap : Mark → String → String
  | .closed, s => s!"${s}$"
  | .goal, s =>
    "box(stroke: (paint: rgb(\"#4dabf7\"), thickness: 0.8pt, dash: \"dashed\"), " ++
    s!"inset: (x: 4pt, y: 3pt), radius: 2pt, ${s}$)"
  | .focus, s =>
    "box(stroke: 1.2pt + rgb(\"#ff922b\"), fill: rgb(\"#ff922b33\"), " ++
    s!"inset: (x: 4pt, y: 3pt), radius: 2pt, ${s}$)"

/-- `rule(premises..., conclusion)` (in `curryst` ≥ 0.6, the conclusion goes last).
A node without premises (an axiom) is rendered as a standalone sequent, as in `BNTree.toTypst`. -/
def PTree.typst : PTree (Mark × String) → Option String
  | .empty => none
  | .goal (m, s) => some (m.wrap s)
  | .node l (m, s) r =>
    match l.typst, r.typst with
    | none, none => some (m.wrap s)
    | pl, pr =>
      some ("rule(\n  " ++ ",\n  ".intercalate (pl.toList ++ pr.toList ++ [m.wrap s]) ++ "\n)")

/-- Typst document (markup mode) for the current state. -/
def renderZipper (curryst : String) (z : Zipper Expr) : MetaM String := do
  let focus := (← z.focus.style renderSeq).markRoot .focus
  let tree := (← z.ctx.style renderSeq).plug focus
  let imp := s!"#import \"{curryst}\": rule, prooftree\n#set text(size: 12pt)\n"
  match tree.typst with
  | none => return imp
  | some body =>
    if body.startsWith "rule(" then return imp ++ "#prooftree(" ++ body ++ ")\n"
    else return imp ++ "#{ " ++ body ++ " }\n"

/-- Attach state `z` to syntax `stx`. A rendering failure never interrupts the derivation. -/
def showTree (stx : Syntax) (z : Zipper Expr) : TermElabM Unit := do
  let opts ← getOptions
  unless opts.get lk.showTree.name lk.showTree.defValue do return
  let curryst := opts.get lk.curryst.name lk.curryst.defValue
  try
    let doc ← renderZipper curryst z
    Typst.display stx doc (fun c => { c with mode := "markup" }) (warn := false)
  catch ex =>
    withRef stx <| logWarning m!"lk_derive: no se pudo dibujar el árbol: {ex.toMessageData}"

declare_syntax_cat lk_tac (behavior := both)
syntax "apply_rule " term:max (ppSpace colGt term:max)* : lk_tac
syntax "left"       : lk_tac
syntax "right"      : lk_tac
syntax "up"         : lk_tac
syntax "next"       : lk_tac
syntax "show_state" : lk_tac

syntax (name := lkDerive) "lk_derive " term:max " by " many1Indent(lk_tac) : term

def elabRuleApp (r : Term) (ss : Array Term) : TermElabM Expr := do
  let args ← ss.mapM fun s => `(BNTree.node BNTree.leaf $s BNTree.leaf)
  let app ← args.foldlM (fun f a => `($f $a)) r
  let e ← Term.elabTerm app none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def evalRule (e : Expr) : MetaM (Expr × Expr × Expr) := do
  let mut v ← whnf e
  if let (``Option.some, #[_, t]) := v.getAppFnArgs then
    v ← whnf t
  else if v.isAppOf ``Option.none then
    throwError "la regla no es aplicable a esas premisas (devolvió `none`)"
  match v.getAppFnArgs with
  | (``BNTree.node, #[_, l, c, r]) => return (l, c, r)
  | _ => throwError "la regla no se evaluó a un `BNTree.node`:{indentExpr v}"

def isEmptyLeaf (e : Expr) : MetaM Bool :=
  return (← whnf e).isAppOf ``BNTree.leaf

partial def toPTree (e : Expr) : MetaM (PTree Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``BNTree.leaf, _) => return .empty
  | (``BNTree.node, #[_, l, s, r]) =>
    if (← isEmptyLeaf l) && (← isEmptyLeaf r) then
      return .goal s
    else
      return .node (← toPTree l) s (← toPTree r)
  | _ => throwError "no pude interpretar como `BNTree`:{indentExpr e}"

def PTree.toBNExpr (seqTy : Expr) : PTree Expr → MetaM Expr
  | .empty => mkAppOptM ``BNTree.leaf #[some seqTy]
  | .goal s => throwError "hoja abierta: {s}"
  | .node l s r => do
    let l' ← PTree.toBNExpr seqTy l
    let r' ← PTree.toBNExpr seqTy r
    mkAppM ``BNTree.node #[l', s, r']

def applyRule (r : Term) (ss : Array Term) : DerivM Unit := do
  let z ← get
  let .goal s := z.focus
    | throwError "apply_rule: el foco no es una hoja abierta (use `left`, `right` o `next`)"
  let (t₁, concl, t₂) ← evalRule (← elabRuleApp r ss)
  unless (← isDefEq concl s) do
    throwError "apply_rule: la conclusión de la regla no coincide con el foco\n  regla: {concl}\n  foco:  {s}"
  let n := PTree.node (← toPTree t₁) s (← toPTree t₂)
  set { z with focus := n }

def goto (name : String) (f : Zipper Expr → Option (Zipper Expr)) : DerivM Unit := do
  match f (← get) with
  | some z => set z
  | none => throwError "{name}: no hay ninguna hoja abierta en esa dirección"

def showState : DerivM Unit := do
  let z ← get
  let foco : MessageData := match z.focus with
    | .goal s => m!"hoja abierta {s}"
    | .node _ s _ => m!"nodo {s}"
    | .empty => m!"(vacío)"
  let gs := z.goals.map fun s => m!"  • {s}"
  logInfo m!"foco: {foco}\nhojas abiertas ({gs.length}):\n{MessageData.joinSep gs "\n"}"

def evalLkTac (stx : Syntax) : DerivM Unit := withRef stx do
  match stx with
  | `(lk_tac| apply_rule $r $ss*) => applyRule r ss
  | `(lk_tac| left)       => goto "left"  Zipper.goLeft?
  | `(lk_tac| right)      => goto "right" Zipper.goRight?
  | `(lk_tac| up)         => goto "up"    Zipper.up?
  | `(lk_tac| next)       => goto "next"  Zipper.nextGoal?
  | `(lk_tac| show_state) => showState
  | _ => throwUnsupportedSyntax

@[term_elab lkDerive] def elabLkDerive : TermElab := fun stx _ => do
  match stx with
  | `(lk_derive $s by $tacs*) =>
    let seqTy := Lean.mkConst ``Sequent
    let s₀ ← elabTermEnsuringType s (some seqTy)
    synthesizeSyntheticMVarsNoPostponing
    let s₀ ← instantiateMVars s₀
    let resTy ← mkAppM ``BNTree #[seqTy]
    let mut z := Zipper.ofTree (.goal s₀)
    -- Initial state: displayed when the cursor is on the `by` line.
    showTree stx[2] z
    let mut failed := false
    for t in tacs do
      try
        let ((), z') ← (evalLkTac t).run z
        z := z'
      catch ex =>
        -- As with Lean tactics, report the error at that tactic, stop executing the
        -- remaining tactics, and preserve the previous state in the Infoview.
        logException ex
        failed := true
      showTree t z
      if failed then break
    if failed then
      mkSorry resTy (synthetic := true)
    else
      match z.goals with
      | [] => PTree.toBNExpr seqTy z.toTree
      | gs =>
        let ms := gs.map fun g => m!"⊢? {g}"
        logErrorAt stx[2] m!"lk_derive: quedan hojas abiertas:{indentD (MessageData.joinSep ms "\n")}"
        mkSorry resTy (synthetic := true)
  | _ => throwUnsupportedSyntax

instance : Repr Sequent := inferInstanceAs (Repr (List PropForm × List PropForm))
