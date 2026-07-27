<!-- Converted to markdown from doc/goal.ipynb in PyPantograph. -->

# Goals and Tactics

Executing tactics in Pantograph is simple. To start a proof, call the
`Server.goal_start` function and supply an expression.

```python
from pantograph import Server
from pantograph.expr import Site, TacticHave, TacticExpr, TacticMode
```

```python
server = await Server.create()
state0 = await server.goal_start_async("forall (p q: Prop), Or p q -> Or q p")
```

This creates a *goal state*, which consists of some goals. In this
case since it is the beginning of a state, it has only one goal.

```python
print(state0)
```

Output:
```

⊢ forall (p q: Prop), Or p q -> Or q p
```

To execute a tactic on a goal state, use `Server.goal_tactic`. This function
takes a state, a tactic, and an optional site (see below). Most Lean tactics are strings.

```python
state1 = await server.goal_tactic_async(state0, "intro a")
print(state1)
```

Output:
```
a : Prop
⊢ ∀ (q : Prop), a ∨ q → q ∨ a
```

Executing a tactic produces a new goal state. If this goal state has no goals,
the proof is complete. You can recover the usual form of a goal with `str()`

```python
print(state1.goals[0])
```

Output:
```
a : Prop
⊢ ∀ (q : Prop), a ∨ q → q ∨ a
```

Starting in v0.3.5, you can run multiple tactics in one shot. Use `?_` to mark goals to be solved later.

```python
state2 = await server.goal_tactic_async(state0, "intro p q\nintro h\ncases h")
print(state2)
```

Output:
```
inl
p : Prop
q : Prop
h✝ : p
⊢ q ∨ p
inr
p : Prop
q : Prop
h✝ : q
⊢ q ∨ p
```

```python
state2 = await server.goal_tactic_async(state0, "intro p q h\nhave random : 1 + 1 = 2 := ?_\ncases h")
print(state2)
```

Output:
```
refine_2.inl
p : Prop
q : Prop
random : 1 + 1 = 2
h✝ : p
⊢ q ∨ p
refine_2.inr
p : Prop
q : Prop
random : 1 + 1 = 2
h✝ : q
⊢ q ∨ p
refine_1
p : Prop
q : Prop
h : p ∨ q
⊢ 1 + 1 = 2
```

## Error Handling and GC

When a tactic fails, it throws an exception (`TacticFailure`) which contains a list of either `str`s or `Message` objects in `e.args[0]`.

```python
from pantograph.message import TacticFailure
try:
    state2 = await server.goal_tactic_async(state1, "assumption")
    print("Should not reach this")
except TacticFailure as e:
    print(e)
    for msg in e.args[0]:
        print(msg)
```

Output:
```
[Message(data="tactic 'assumption' failed\na : Prop\n⊢ ∀ (q : Prop), a ∨ q → q ∨ a", pos=Position(line=0, column=0), pos_end=None, severity=<Severity.ERROR: 3>, kind=None)]
0:0: error: tactic 'assumption' failed
a : Prop
⊢ ∀ (q : Prop), a ∨ q → q ∨ a
```

A state with no goals is considered solved

```python
state0 = await server.goal_start_async("forall (p : Prop), p -> p")
state1 = await server.goal_tactic_async(state0, "intro")
state2 = await server.goal_tactic_async(state1, "intro h")
state3 = await server.goal_tactic_async(state2, "exact h")
state3
```

Output:
```
GoalState(#7, goals=[], _sentinel=#4
```

Execute `server.gc()` once in a while to delete unused goals.

```python
await server.gc_async()
```

## Special Tactics

Lean has special provisions for some tactics. This includes `have`, `let`,
`calc`. To execute one of these tactics, create a `TacticHave`, `TacticLet`,
instance and feed it into `server.goal_tactic`.

Technically speaking `have` and `let` are not tactics in Lean, so their execution requires special attention. In v0.3.5, they can be run under the normal tactic function as well (see above).

```python
state0 = await server.goal_start_async("1 + 1 = 2")
state1 = await server.goal_tactic_async(state0, TacticHave(branch="2 = 1 + 1", binder_name="h"))
print(state1)
```

Output:
```

⊢ 2 = 1 + 1
h : 2 = 1 + 1
⊢ 1 + 1 = 2
```

The `TacticExpr` "tactic" parses an expression and assigns it to the current
goal.  This leverages Lean's type unification system and is as expressive as
Lean expressions. Many proofs in Mathlib4 are written in a mixture of expression
and tactic forms.

```python
state0 = await server.goal_start_async("forall (p : Prop), p -> p")
state1 = await server.goal_tactic_async(state0, "intro p")
state2 = await server.goal_tactic_async(state1, TacticExpr("fun h => h"))
print(state2)
```

Output:
```

```

### Drafting

Pantograph supports drafting (technically the sketch step) from
[Draft-Sketch-Prove](https://github.com/wellecks/ntptutorial/tree/main/partII_dsp).
Pantograph's drafting feature is more powerful. At any place in the proof, you
can replace an expression with `sorry`, and the `sorry` will become a goal. Any type errors will also become goals. In order to detect whether type errors have occurred, the user can look at the messages from each compilation unit.

At this point we must introduce the idea of compilation units. Each Lean
definition, theorem, constant, etc., is a *compilation unit*. When Pantograph
extracts data from Lean source code, it sections the data into these compilation
units.

For example, consider this sketch produced by a language model prover:
```lean
by
   intros n m
   induction n with
   | zero =>
     have h_base: 0 + m = m := sorry
     have h_symm: m + 0 = m := sorry
     sorry
   | succ n ih =>
     have h_inductive: n + m = m + n := sorry
     have h_pull_succ_out_from_right: m + Nat.succ n = Nat.succ (m + n) := sorry
     have h_flip_n_plus_m: Nat.succ (n + m) = Nat.succ (m + n) := sorry
     have h_pull_succ_out_from_left: Nat.succ n + m = Nat.succ (n + m) := sorry
     sorry
```
There are some `sorry`s that we want to solve automatically with hammer tactics. We can do this by drafting.

Pantograph can also load `sorry`s from a code snippet, which provides an alternative way for proof initiation. Warning: `load_sorry` does not work with `example` declarations.

```python
sketch = """
theorem add_comm_proved_formal_sketch : ∀ n m : Nat, n + m = m + n := sorry
"""
unit, = await server.load_sorry_async(sketch)
print(unit.goal_state)
```

Output:
```

⊢ ∀ (n m : Nat), n + m = m + n
```

```python
step = """
by
   -- Consider some n and m in Nats.
   intros n m
   -- Perform induction on n.
   induction n with
   | zero =>
     -- Base case: When n = 0, we need to show 0 + m = m + 0.
     -- We have the fact 0 + m = m by the definition of addition.
     have h_base: 0 + m = m := sorry
     -- We also have the fact m + 0 = m by the definition of addition.
     have h_symm: m + 0 = m := sorry
     -- Combine facts to close goal
     sorry
   | succ n ih =>
     sorry
"""
from pantograph.expr import TacticDraft
tactic = TacticDraft(step)
state1 = await server.goal_tactic_async(unit.goal_state, tactic)
print(state1)
```

Output:
```
n : Nat
m : Nat
⊢ 0 + m = m
n : Nat
m : Nat
h_base : 0 + m = m
⊢ m + 0 = m
n : Nat
m : Nat
h_base : 0 + m = m
h_symm : m + 0 = m
⊢ 0 + m = m + 0
n✝ : Nat
m : Nat
n : Nat
ih : n + m = m + n
⊢ n + 1 + m = m + (n + 1)
```

### Search Target Distillation

Sometimes, we want to search for an object (witness) along with proofs (companions) of properties about the object. This problem is known as **companion generation**. In Pantograph, `load_sorry` will automatically pair companions to create coupled search targets. Note that this is only available for flat dependency structures, where one object has a list of properties.

```python
sketch = """
def f : Nat -> Nat := sorry
theorem property (n : Nat) : f n = n + 1 := sorry
"""
target, = await server.load_sorry_async(sketch, ignore_values=True)
print(target.goal_state)
```

Output:
```

⊢ { f // ∀ (n : Nat), f n = n + 1 }
```

## Sites

The optional `site` argument to `goal_tactic` controls the area of effect of a tactic. Site controls what the tactic sees when it asks Lean for the current goal. Most tactics only act on a single goal, but tactics acting on multiple goals are plausible as well.

The `auto_resume` field defaults to the server option's `automaticMode` (which defaults to `True`). When this field is true, Pantograph will not deliberately hide other goals away from the tactic. This is the usual modus operandi of tactic proofs in Lean. When `auto_resume` is set to `False`, Pantograph will set other goals to dormant. This can be useful in limiting the area of effect of a tactic. However, dormanting a goal comes with the extra burden that it has to be activated ("resume") later, via `goal_resume`.

```python
state = await server.goal_start_async("forall (p : Prop), p -> And p (Or p p)")
state = await server.goal_tactic_async(state, "intro p h")
state = await server.goal_tactic_async(state, "apply And.intro")
print(state)
```

Output:
```
left
p : Prop
h : p
⊢ p
right
p : Prop
h : p
⊢ p ∨ p
```

In the example below, we set `auto_resume` to `False`, and the sibling goal is dormanted.

```python
state1 = await server.goal_tactic_async(state, "exact h", site=Site(goal_id=0, auto_resume=False))
print(state1)
```

Output:
```

```

In the example below, we preferentially operate on the second goal. Note that the first goal is still here.

```python
state2 = await server.goal_tactic_async(state, "apply Or.inl", site=Site(goal_id=1))
print(state2)
```

Output:
```
right.h
p : Prop
h : p
⊢ p
left
p : Prop
h : p
⊢ p
```

## Tactic Modes

Pantograph has special provisions for handling `conv` and `calc` tactics. The commonality of these tactics is incremental feedback: The tactic can run half way and produce some goal. Pantograph supports this via tactic modes. Every goal carries around with it a `TacticMode`, and the user is free to switch between modes. By default, the mode is `TacticMode.TACTIC`.

```python
state = await server.goal_start_async("∀ (a b: Nat), (b = 2) -> 1 + a + 1 = a + b")

state = await server.goal_tactic_async(state, "intro a b h")
state = await server.goal_tactic_async(state, TacticMode.CALC)
state = await server.goal_tactic_async(state, "1 + a + 1 = a + 1 + 1")
state
```

Output:
```
GoalState(#24, goals=[Goal(id='_uniq.381', variables=[Variable(t='Nat', v=None, name='a'), Variable(t='Nat', v=None, name='b'), Variable(t='b = 2', v=None, name='h')], target='1 + a + 1 = a + 1 + 1', sibling_dep=None, name='calc', mode=<TacticMode.TACTIC: 1>), Goal(id='_uniq.400', variables=[Variable(t='Nat', v=None, name='a'), Variable(t='Nat', v=None, name='b'), Variable(t='b = 2', v=None, name='h')], target='a + 1 + 1 = a + b', sibling_dep=None, name=None, mode=<TacticMode.CALC: 3>)], _sentinel=#14
```
