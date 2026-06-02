<!-- Converted to markdown from doc/frontend.ipynb in PyPantograph. -->

# Data Extraction

```python
import os
from pathlib import Path
from pantograph.server import Server
```

## Tactic Invocation

Pantograph can extract tactic invocation data from a Lean file. A **tactic
invocation** is a tuple containing the before and after goal states, and the
tactic which converts the "before" state to the "after" state.

To extract tactic invocation data, use `server.tactic_invocations(file_name)`
and supply the file name of the input Lean file.

```python
project_path = Path(os.getcwd()).parent.resolve() / 'examples/Example'
print(f"$PWD: {project_path}")
server = await Server.create(imports=['Example'], project_path=project_path)
units = await server.tactic_invocations_async(project_path / "Example.lean")
```

Output:
```
$PWD: /Users/aniva/Projects/matp/PyPantograph/examples/Example
```

The function returns a list of `CompilationUnit` objects, corresponding to each compilation unit in the input Lean file. For performance reasons only the text boundaries are loaded into `CompilationUnit`s.

```python
with open(project_path / "Example.lean", 'rb') as f:
    content = f.read()
    for i, unit in enumerate(units):
        print(f"#{i}: [{unit.i_begin},{unit.i_end}]")
        unit_text = content[unit.i_begin:unit.i_end].decode('utf-8')
        print(unit_text)
```

Output:
```
#0: [14,85]
/-- Ensure that Aesop is running -/
example : α → α :=
  by aesop


#1: [85,254]
example : ∀ (p q: Prop), p ∨ q → q ∨ p := by
  intro p q h
  -- Here are some comments
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption
```

Each `CompilationUnit` includes a list of `TacticInvocation`s, which contains the `.before` (corresponding to the state before the tactic), `.after` (corresponding to the state after the tactic), and `.tactic` (tactic executed) fields.

```python
for i in units[0].invocations:
    print(f"[Before]\n{i.before}")
    print(f"[Tactic]\n{i.tactic} (using {i.used_constants})")
    print(f"[After]\n{i.after}")
```

Output:
```
[Before]
α : Sort ?u.7
⊢ α → α
[Tactic]
aesop (using [])
[After]
```

```python
for i in units[1].invocations:
    print(f"[Before]\n{i.before}")
    print(f"[Tactic]\n{i.tactic} (using {i.used_constants})")
    print(f"[After]\n{i.after}")
```

Output:
```
[Before]
⊢ ∀ (p q : Prop), p ∨ q → q ∨ p
[Tactic]
intro p q h (using [])
[After]
p q : Prop
h : p ∨ q
⊢ q ∨ p
[Before]
p q : Prop
h : p ∨ q
⊢ q ∨ p
[Tactic]
cases h (using ['Eq.refl', 'Or'])
[After]
case inl
p q : Prop
h✝ : p
⊢ q ∨ p
case inr
p q : Prop
h✝ : q
⊢ q ∨ p
[Before]
case inl
p q : Prop
h✝ : p
⊢ q ∨ p
[Tactic]
apply Or.inr (using ['Or.inr'])
[After]
case inl.h
p q : Prop
h✝ : p
⊢ p
[Before]
case inl.h
p q : Prop
h✝ : p
⊢ p
[Tactic]
assumption (using [])
[After]

[Before]
case inr
p q : Prop
h✝ : q
⊢ q ∨ p
[Tactic]
apply Or.inl (using ['Or.inl'])
[After]
case inr.h
p q : Prop
h✝ : q
⊢ q
[Before]
case inr.h
p q : Prop
h✝ : q
⊢ q
[Tactic]
assumption (using [])
[After]
```

## Check Compilation

Use `check_compile` to check if some Lean code compiles.

Keep in mind that Lean compilation can execute arbitrary code.

```python
server = await Server.create()
code = """
example : 1 + 1 = 2 := by rfl
"""
await server.check_compile_async(code)
```

Output:
```
[CompilationUnit(i_begin=0, i_end=31, messages=[], invocations=None, goal_state=None, goal_src_boundaries=None, new_constants=None)]
```

If there are no error messages, it means the unit compiles.

## Loading Definitions

Pantograph keeps track of a global environment. `Server.load_definitions` adds new definitions to the environment.

```python
code = """
def mystery : Nat -> Nat := fun x => x + 1
"""
await server.load_definitions_async(code)
await server.env_inspect_async("mystery")
```

Output:
```
{'type': {'pp': 'Nat → Nat'},
 'sourceStart': {'line': 2, 'column': 0},
 'sourceEnd': {'line': 2, 'column': 42},
 'isUnsafe': False}
```

## Track Checking

We can check if one file conforms to the definition and theorems of another. If the result object has no `failure`s or error messages, the check has passed.

```python
src = """
def f : Nat -> Nat := sorry
theorem property (n : Nat) : f n = n + 1 := sorry
"""
dst = """
def f (x : Nat) := x + 1
theorem property (n : Nat) : f n = n + 1 := rfl
"""
await server.check_track_async(src, dst)
```

Output:
```
CheckTrackResult(src_messages=[], dst_messages=[], failure=None)
```

```python
src = """
def f : Nat -> Nat := sorry
theorem property (n : Nat) : f n = n + 1 := sorry
"""
# Tampering!
dst = """
def f (x : Nat) := x + 1
theorem property (n : Nat) : 0 = 0 := rfl
"""
await server.check_track_async(src, dst)
```

Output:
```
CheckTrackResult(src_messages=[], dst_messages=[], failure='Type clash of property')
```
