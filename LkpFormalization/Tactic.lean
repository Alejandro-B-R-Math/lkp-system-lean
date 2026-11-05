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
    let ((), z) ← (tacs.forM fun t => evalLkTac t).run (Zipper.ofTree (.goal s₀))
    match z.goals with
    | [] => PTree.toBNExpr seqTy z.toTree
    | gs =>
      let ms := gs.map fun g => m!"⊢? {g}"
      throwError "lk_derive: quedan hojas abiertas:{indentD (MessageData.joinSep ms "\n")}"
  | _ => throwUnsupportedSyntax

instance : Repr Sequent := inferInstanceAs (Repr (List PropForm × List PropForm))
