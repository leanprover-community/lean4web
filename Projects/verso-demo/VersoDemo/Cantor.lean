import VersoManual
open Verso Genre Manual InlineLean

#doc (Manual) "Cantor's Diagonal Argument" =>

The type of all predicates over a type is that type's _powerset_. Elements of one of these subsets satisfy the predicate:
```lean
def Set (α : Type u) : Type u :=
  α → Prop

instance : Membership α (Set α) where
  mem xs x := xs x
```

A function $`f` is surjective if each element of the range is covered by an element of the domain:
```lean
def Surjective (f : α → β) :=
  ∀ y, ∃ x, f x = y
```

Given a function $`f ∈ S → \mathcal{P}(S)`, Cantor's diagonal argument involves the diagonal set $`\{x ∈ S \mid x \not\in f(x)\}`. The {tactic}`grind` tactic takes care of many reasoning steps:
```lean
theorem cantor (f : S → Set S) : ¬ Surjective f := by
  intro h
  have ⟨x, p⟩ := h (fun x : S => x ∉ f x)
  have : x ∈ f x ↔ x ∉ f x := by
    constructor <;>
    simp [Membership.mem] at * <;>
    grind
  grind
```
