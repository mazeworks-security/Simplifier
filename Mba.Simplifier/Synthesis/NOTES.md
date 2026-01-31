# Ideas to explore:

### Synthesize trees instead of DAGs
- Solver needs to synthesize less operand numbers
- Think of the tree as an operand stack. `a+b` has the stack `a,b`, op2 is simply `line_index - 1`. More thought needed on finding the index of `a`.

### Variable permutation idea from "SAT-Based Exact Synthesis" paper

- If two variables are symmetric, assert that `a` must be used before `b`.
- Add a "truth table component". Instead of having and, or, xor, neg, instructions, add a truth table component that can specify any 2-variable truth table.

### Constraint optimization
- We're creating overlapping constraints with lots of redundancies.
- E.g. I had one constraint that asserted that `op1` of `opcode op0, op1` is zero if `opcode == NOT`. I also had a constraint that `op0 >= op1` for all associative operators. 
- Can we boost solver performance by combining these constraints? Equality saturation over the constraints?


# Constraint performance and ideas

Sort associative operand indices:
- `add(3, 1)` => `add(1, 3)`. 
- Result: 10x degredation in synthesis speed...
- I guess this is bad because it's a very local or syntactic constraint. 
    - I suspect these kinds of constraints are only justifiable if they can be thought of as a profitable rewrite rule.
    - "a|111" => "111|a" is not profitable. It does not reduce the number of instructions
    - "a|0" => "0" is profitable. It reduces the number of instructions.
    - The solver should be much better at handling global constraints. Structural and functional redundancy constraints.
Eliminate idempotent instructions:
- `a&a`, `a|a`, and `a^a` are not allowed at all
- 10x faster synthesis times on boolean `~(a&b|c|d|e|f|g)` with `14` instruction count. 500ms
