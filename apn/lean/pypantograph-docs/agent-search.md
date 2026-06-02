<!-- Converted from doc/agent-search.ipynb in https://github.com/lenianiva/PyPantograph
     at commit b8608f3 (the version installed in this image). -->

# Search

Pantograph supports basic proof search. In this case, Pantograph treats goals as nodes on an and-or tree. The user supplies an agent which should provide two functions:

1. *Tactic*: Which tactic should be used on a goal?
2. *Guidance*: What is the search priority on a goal?

The user agent should inherit from `pantograph.search.Agent`. Here is a brute force agent example:

```python
from typing import Optional
import collections
from pantograph import Server
from pantograph.search import Agent
from pantograph.expr import GoalState, Tactic
```

```python
class DumbAgent(Agent):

    def __init__(self):
        super().__init__()

        self.goal_tactic_id_map = collections.defaultdict(lambda : 0)
        self.intros = [
            "intro",
        ]
        self.tactics = [
            "intro h",
            "cases h",
            "apply Or.inl",
            "apply Or.inr",
        ]
        self.no_space_tactics = [
            "assumption",
        ]

    def next_tactic(
            self,
            state: GoalState,
            goal_id: int,
    ) -> Optional[Tactic]:
        key = (state.state_id, goal_id)
        i = self.goal_tactic_id_map[key]

        target = state.goals[goal_id].target
        if target.startswith('∀'):
            tactics = self.intros
        elif ' ' in target:
            tactics = self.tactics
        else:
            tactics = self.no_space_tactics

        if i >= len(tactics):
            return None

        self.goal_tactic_id_map[key] = i + 1
        return tactics[i]
```

Execute the search with `agent.search`.

```python
server = Server()
agent = DumbAgent()
goal_state = server.goal_start("∀ (p q: Prop), Or p q -> Or q p")
agent.search(server=server, goal_state=goal_state, verbose=False)
```

Output:
```
SearchResult(n_goals_root=1, duration=0.7717759609222412, success=True, steps=16)
```

## Automatic and Manual Modes

The agent chooses one goal and executes a tactic on this goal. What happens to the other goals that are not chosen? By default, the server runs in automatic mode. In automatic mode, all other goals are automatically inherited by a child state, so a user agent could declare a proof finished when there are no more goals remaining in the current goal state.

Some users may wish to handle sibling goals manually. For example, Aesop's treatment of metavariable coupling is not automatic. To do this, pass the flag `options={ "automaticMode" : False }` to the `Server` constructor.
