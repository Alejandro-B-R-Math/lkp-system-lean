import Lean
import LkpFormalization.Basic

/-!
# Notation for formulas and sequents

Write
```
A ∨ B, ¬A ⊢ B          -- or:  A ∨ B, ¬A → B   /   A ∨ B, ¬A -> B
```
instead of `([A ∨ₚ B, ¬ₚ A], [B])`.

## How to use it

* `[form| A ∧ ¬B]`   → a `PropForm`
* `[seq| A, B ⊢ C]`  → a `Sequent`
* In `lk_derive` and `apply_rule`, the sequent can be written without delimiters
  (see `Tactic.lean`).
* Variables are identifiers (`A`, `p`, `q₁`); strings also work (`"A"`).
* `‹t›` inserts a Lean term of type `PropForm`: `[form| ‹φ› ⊃ A]`.
-/

open Lean

namespace LkpFormalization

/-- Builds a sequent. This is what `[seq| Γ ⊢ Δ]` produces.
A dedicated function is used (instead of `(Γ, Δ)`) so that the term has type `Sequent`
and therefore the `ToTypst Sequent` instance is selected rather than the one for `α × β`. -/
def Sequent.mk (Γ Δ : List PropForm) : Sequent := (Γ, Δ)

def PropForm.pp : PropForm → Nat → String
  | .var s, _ => s
  | .tr, _ => "⊤"
  | .fls, _ => "⊥"
  | .neg p, k => (if k > 90 then "(" else "") ++ "¬" ++ p.pp 90 ++ (if k > 90 then ")" else "")
  | .conj p q, k => (if k > 70 then "(" else "") ++ p.pp 71 ++ " ∧ " ++ q.pp 70 ++ (if k > 70 then ")" else "")
  | .disj p q, k => (if k > 65 then "(" else "") ++ p.pp 66 ++ " ∨ " ++ q.pp 65 ++ (if k > 65 then ")" else "")
  | .impl p q, k => (if k > 55 then "(" else "") ++ p.pp 56 ++ " ⊃ " ++ q.pp 55 ++ (if k > 55 then ")" else "")
  | .equiv p q, k => (if k > 50 then "(" else "") ++ p.pp 51 ++ " ≡ " ++ q.pp 50 ++ (if k > 50 then ")" else "")

/-- Formula in `[form| ...]` notation, without unnecessary parentheses. -/
def PropForm.toNotation (p : PropForm) : String := p.pp 0

/-- `A, B ⊢ C` for messages and `#eval`. -/
def Sequent.toString (s : Sequent) : String :=
  ", ".intercalate (s.1.map PropForm.toNotation) ++ " ⊢ " ++ ", ".intercalate (s.2.map PropForm.toNotation)

instance : ToString Sequent := ⟨Sequent.toString⟩

declare_syntax_cat lk_form

syntax:max ident                : lk_form
syntax:max str                  : lk_form
syntax:max "⊤"                  : lk_form
syntax:max "⊥"                  : lk_form
syntax:max "(" lk_form ")"      : lk_form
syntax:max "‹" term "›"         : lk_form
syntax:90  "¬" lk_form:90       : lk_form
syntax:70  lk_form:71 " ∧ " lk_form:70 : lk_form
syntax:65  lk_form:66 " ∨ " lk_form:65 : lk_form
syntax:55  lk_form:56 " ⊃ " lk_form:55 : lk_form
syntax:50  lk_form:51 " ≡ " lk_form:50 : lk_form

declare_syntax_cat lk_seq

syntax lk_form,* " ⊢ "  lk_form,* : lk_seq
--syntax lk_form,* " → "  lk_form,* : lk_seq
--syntax lk_form,* " -> " lk_form,* : lk_seq

partial def expandForm (s : TSyntax `lk_form) : MacroM Term :=
  match s with
  | `(lk_form| $x:ident) =>
    `(PropForm.var $(Syntax.mkStrLit x.getId.eraseMacroScopes.toString))
  | `(lk_form| $s:str)   => `(PropForm.var $s)
  | `(lk_form| ⊤)        => `(PropForm.tr)
  | `(lk_form| ⊥)        => `(PropForm.fls)
  | `(lk_form| ($a))     => expandForm a
  | `(lk_form| ‹$t›)     => pure t
  | `(lk_form| ¬ $a)     => do `(PropForm.neg $(← expandForm a))
  | `(lk_form| $a ∧ $b)  => do `(PropForm.conj $(← expandForm a) $(← expandForm b))
  | `(lk_form| $a ∨ $b)  => do `(PropForm.disj $(← expandForm a) $(← expandForm b))
  | `(lk_form| $a ⊃ $b)  => do `(PropForm.impl $(← expandForm a) $(← expandForm b))
  | `(lk_form| $a ≡ $b)  => do `(PropForm.equiv $(← expandForm a) $(← expandForm b))
  | _ => Macro.throwUnsupported

def expandSeq (s : TSyntax `lk_seq) : MacroM Term := do
  unless s.raw.getNumArgs == 3 do Macro.throwUnsupported
  let as ← s.raw[0].getSepArgs.mapM fun a => expandForm ⟨a⟩
  let bs ← s.raw[2].getSepArgs.mapM fun a => expandForm ⟨a⟩
  `(Sequent.mk [$as,*] [$bs,*])

/-- `[form| A ∧ ¬B]` -/
macro:max "[form|" f:lk_form "]" : term => expandForm f

/-- `[seq| A, B ⊢ C]` -/
macro:max "[seq|" s:lk_seq "]" : term => expandSeq s

declare_syntax_cat lk_arg
syntax "(" lk_seq ")" : lk_arg
syntax term:max       : lk_arg

def expandArg (a : TSyntax `lk_arg) : MacroM Term :=
  match a with
  | `(lk_arg| ($s:lk_seq)) => expandSeq s
  | `(lk_arg| $t:term)     => pure t
  | _ => Macro.throwUnsupported

end LkpFormalization
