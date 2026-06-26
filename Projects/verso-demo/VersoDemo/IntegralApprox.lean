import VersoManual
open Verso Genre Manual InlineLean

#doc (Manual) "Approximating an Integral" =>

The area under $`\sin x` from $`0` to $`k` can be calculated exactly:

$$`\int_0^k \sin x \,dx = 1 - \cos k`

This means that we can exactly compute the area under $`\sin x` from $`0` to $`1.5` like this:

```lean (name := eval1)
#eval 1 - Float.cos 1.5
```
```leanOutput eval1
0.929263
```

But we can approximate this integral with a (left) [Riemann sum](https://en.wikipedia.org/wiki/Riemann_sum).
If we say we want to break the interval from $`0` to $`k` into $`n` different rectangles, then we can define the left riemann sum as

$$`\sum_{i=0}^{n - 1} \sin x \times dx`

Where $`dx = {k \over n}` and $`x = i \times dx`, which we can then express in Lean like this:

```lean
def leftSum k n (f : (x dx : Float) → Float) :=
  List.range n |>.foldl (init := 0) (fun (sum : Float) i =>
    let dx := k / n.toFloat
    let x := i.toFloat * dx
    sum + f x dx)

def integralApprox (k : Float) (n : Nat) : Float :=
  leftSum k n (fun x dx => Float.sin x * dx)
```

The error in calculating the area under $`\sin x` from $`0` to $`1.5` with 6 rectangles is about $`0.13`.

```lean (name := eval2)
#eval (1 - Float.cos 1.5) - integralApprox 1.5 6
```
```leanOutput eval2
0.129532
```

The error dramatically decreases as we increase the number of rectangles from $`2^0 = 1` to $`2^8 = 256`:

```lean (name := eval3)
#eval List.range 9 |>.map (fun m => Float.abs
  ((1 - Float.cos 1.5)
    - (integralApprox 1.5 (Nat.pow 2 m))))
```
```leanOutput eval3
[0.929263, 0.418034, 0.197946, 0.096239, 0.047438, 0.023549, 0.011732, 0.005855, 0.002925]
```
