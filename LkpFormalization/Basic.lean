import TypstInfoview.Basic

namespace LkpFormalization

inductive PropForm
  | var   : String → PropForm
  | tr    : PropForm
  | fls   : PropForm
  | neg   : PropForm → PropForm
  | conj  : PropForm → PropForm → PropForm
  | disj  : PropForm → PropForm → PropForm
  | impl  : PropForm → PropForm → PropForm
  | equiv  : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq, Inhabited

namespace PropForm

notation:max "⊤ₚ" => PropForm.tr
notation:max "⊥ₚ" => PropForm.fls
prefix:90 "¬ₚ "   => PropForm.neg
infixr:70 " ∧ₚ "  => PropForm.conj
infixr:65 " ∨ₚ "  => PropForm.disj
infixr:55 " ⊃ₚ "  => PropForm.impl
infixr:50 " ≡ₚ "  => PropForm.equiv

private def toString : PropForm → String
  | var s     => s
  | tr        => "⊤"
  | fls       => "⊥"
  | neg p     => "(¬ " ++ toString p ++ ")"
  | conj p q  => "(" ++ toString p ++ " ∧ " ++ toString q ++ ")"
  | disj p q  => "(" ++ toString p ++ " ∨ " ++ toString q ++ ")"
  | impl p q  => "(" ++ toString p ++ " ⊃ " ++ toString q ++ ")"
  | equiv p q => "(" ++ toString p ++ " ≡ " ++ toString q ++ ")"

instance : ToString PropForm := ⟨PropForm.toString⟩

instance : Coe String PropForm := ⟨fun s => var s⟩

instance : Repr PropForm where
  reprPrec A _ := A.toString.toFormat

def toTypstAux : PropForm → String
  | var x => x
  | tr => "top"
  | fls => "bot"
  | neg f => s!"not {f.toTypstAux}"
  | conj f₁ f₂ => s!"({f₁.toTypstAux} and {f₂.toTypstAux})"
  | disj f₁ f₂ => s!"({f₁.toTypstAux} or {f₂.toTypstAux})"
  | impl f₁ f₂ => s!"({f₁.toTypstAux} supset {f₂.toTypstAux})"
  | equiv f₁ f₂ => s!"({f₁.toTypstAux} equiv {f₂.toTypstAux})"

instance : ToTypst PropForm where
  toTypst := PropForm.toTypstAux

end PropForm

def Sequent := (List PropForm) × (List PropForm)

instance : ToTypst Sequent where
  toTypst s := (toTypst s.1) ++ " -> " ++ (toTypst s.2)

def Sequent.antecedent (s : Sequent) : List PropForm := s.1
def Sequent.succedent (s : Sequent) : List PropForm := s.2

end LkpFormalization
