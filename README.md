# LK' System in Lean 4

This project aims to formalize and standardize core aspects of the **LK' system** (a variant of Gentzen's sequent calculus \(LK\)) using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

This repository serves as supplementary material and an open-source library for the **Computational Logic** course at the **University of Antioquia (2026)**.

## Interactive Proof Tree

The `lk_derive` tactic displays the proof tree in the Lean Infoview after each tactic. Place the cursor on a tactic line to inspect the tree at that point in the derivation. The current focus is highlighted in orange, open goals are shown in dashed blue boxes, and closed nodes have no box.

The following example, also available in [`LkpFormalization/example.lean`](LkpFormalization/example.lean), derives the sequent `A ⊢ A` using the cut rule:

```lean
import LkpFormalization.Tactic
import TypstInfoview

def t₃ : BNTree Sequent :=
  lk_derive A ⊢ A by
    apply_rule cut (A ⊢ A) (A ⊢ A)
    left
    apply_rule (ax "A")
    next
    apply_rule (ax "A")
```

In the Infoview, placing the cursor on each tactic shows the proof tree after that step. `left` moves the focus to the left open premise, and `next` moves to the next open goal. To render the completed proof tree with Typst, use the `typst` preamble and `#typst t₃` command shown in `example.lean`.

> ***Note:*** Rendering the proof tree requires [Typst](https://github.com/typst/typst) to be installed locally.

## TODO

Implement the rules of $\text{LK}^\prime$

- [ ] Structural rules
  - [x] Weakening
  - [ ] Contraction
  - [x] Exchange
  - [x] Cut rule
- [ ] Logical rules
  - [ ] Antecedent conjunction rules
  - [ ] Succedent conjunction rule
  - [x] Antecedent disjunction rule
  - [x] Succedent disjunction rules
  - [ ] Implication rules
  - [x] Negation rules
