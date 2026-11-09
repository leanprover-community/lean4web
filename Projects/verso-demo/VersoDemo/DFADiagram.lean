import VersoManual
open Verso Genre Manual InlineLean

#doc (Manual) "DFA Language Equivalence" =>

Coinductive predicates naturally capture bisimulation-like notions, like showing that these two DFAs have equivalent languages:

:::row (align := "top")
```diagram (cssScale := "0.1") +inline
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "ok") |>.atop
(cfg.state 1 "fail") |>.atop
(cfg.loop 0 "a") |>.atop
(cfg.loop 1 "a, b") |>.atop
(cfg.edge 0 1 "b")
```

```diagram (cssScale := "0.1") +inline
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "start") |>.atop
(cfg.accept 1 "ok") |>.atop
(cfg.state 2 "fail") |>.atop
(cfg.arc 0 1 "a" 30) |>.atop
(cfg.arc 1 0 "a" (-30)) |>.atop
(cfg.edge 1 2 "b") |>.atop
(cfg.arc 0 2 "b" (-140)) |>.atop
(cfg.loop 2 "a, b")
```
:::

# Defining DFAs

:::leanSection
```lean -show
variable {Q : Type} {A : Type} {q₀ : Q}
```
A deterministic finite automaton is given by a set of states {lean}`Q`, an alphabet {lean}`A`, a start state {lean}`q₀` in {lean}`Q`, a subset of {lean}`Q` that indicates which states are accepting states, and a transition function that takes a state and an element of the alphabet to a new state:
:::

```lean
structure DFA (Q : Type) (A : Type) : Type where
  q₀ : Q
  δ : Q → A → Q
  accepting : Q → Bool
```

Two automata over the same alphabet have equivalent languages from a given pair of states when they agree as to whether these states are accepting and they furthermore have equivalent languages from all successor states according to their transition functions:
```lean
def languageEquivalent (M : DFA Q A) (M' : DFA Q' A)
    (q : Q) (q' : Q') : Prop :=
  M.accepting q = M'.accepting q' ∧
    ∀ (a : A), languageEquivalent M M' (M.δ q a) (M'.δ q' a)
coinductive_fixpoint
```

The coinduction principle captures the standard notion of bisimulation of deterministic automata:
```signature
languageEquivalent.coinduct {Q A Q' : Type}
  (M : DFA Q A) (M' : DFA Q' A) (pred : Q → Q' → Prop) :
  (∀ (q : Q) (q' : Q'), pred q q' →
    M.accepting q = M'.accepting q' ∧
    ∀ (a : A), pred (M.δ q a) (M'.δ q' a)) →
  ∀ (q : Q) (q' : Q'), pred q q' →
    languageEquivalent M M' q q'
```

# Encoding the Example

The DFAs above can be represented using the following definitions:
```lean
inductive Alphabet where | a | b

inductive Q1 where | ok | fail

def loop : DFA Q1 Alphabet where
  q₀ := .ok
  δ
    | .ok, .a => .ok
    | _, _ => .fail
  accepting
    | .ok => True
    | _ => False

inductive Q2 where | start | ok | fail

def cycle : DFA Q2 Alphabet where
  q₀ := .start
  δ
    | .start, .a => .ok
    | .ok, .a => .start
    | _, _ => .fail
  accepting
    | .start | .ok => True
    | .fail => False
```

# Proving Equivalence

To prove that our two examples are equivalent, the first step is to define a relation that captures their equivalent states.
Then, coinduction lifts the demonstration that they actually are equivalent in this relation to language equivalence:
```lean
theorem loop_equiv_cycle :
    languageEquivalent loop cycle loop.q₀ cycle.q₀ := by
  let r : Q1 → Q2 → Prop
  | .ok, .start
  | .ok, .ok
  | .fail, .fail => True
  | _, _ => False
  apply languageEquivalent.coinduct (pred := r)
  . simp only [loop, cycle] <;>
    grind
  . simp [r, loop, cycle]
```
