import Mathlib.Logic.Equiv.Basic -- import the theory
-- of bijections as functions with two-sided inverses

-- Let X, Y and Z be sets
variable (X Y Z : Type)

-- Then there's a bijection between functions `X × Y → Z`
-- and functions from `X` to (the space of functions from `Y` to `Z`).

example : (X × Y → Z) ≃ (X → (Y → Z)) :=
{ -- to go from f : X × Y → Z to a function X → (Y → Z),
  -- send x and y to f(x,y)
  toFun := fun f ↦ (fun x y ↦ f (x,y))
  -- to go from g : X → (Y → Z) to a function X × Y → Z,
  -- send a pair p=(x,y) to (g p.1) (p.2) where p.i is the i'th element of p
  invFun := fun g ↦ (fun p ↦ g p.1 p.2)
  -- Here we prove that if f ↦ g ↦ f' then f' = f
  left_inv := by
    intro f -- let f : X × Y → Z be arbitrary.
    rfl -- turns out f' = f by definition
  -- here we prove that if g ↦ f ↦ g' then g' = g
  right_inv := by
    intro g -- let f : X → (Y → Z) by arbitrary
    rfl -- turns out that g' = g by definition
}
