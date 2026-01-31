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

### Optimize encoding of opcode selectors
- Instructions are created as one big conditional select of `N` values, where `N` is the number of components (ignoring upper or lower bounds)
- Different encodings imply vastly different solving times for some `N`s.
- A `select3` encoding improved my synthesis runtime by 50%. Tldr when `N == 3`, the optimal encoding is `If(Extract(1,1,index) == 1, elements[2], If(Extract(0,0,index) == 1, elements[1], elements[0]))` where `index` is a 2-bit bitvector.
- 'select3' might actually not be optimal - there's another encoding called `one-hot` where you instead allocate 3 bits 
- On the boolean `~(a|b|c|d|e|f|g)`, my synthesizer is twice as fast as `synth` when using the `select3` encoding. I used the same set of components (AND, OR, NOT) with the maximum number of constants set to zero.
- These optimal encodings can also be used for selecting operands.

### Heuristic selection of components and some other stuff
- Recently synthesized `(((x|16)+y)^y) >> 4` as a part of some bit blasted circuit.
- Could we identify outermost right shifts by saying "0th bit depends on bits 4..63, meaning there's a right shift"
- You can check if an expression is nonlinear by asking a solver if any output bits depend on bits of input variables that are above it.

### CEGIS pruning
- We can analyze the knownbits of the input expression to immediately prune invalid candidates.
-   Though this might actually be a wasteful query. 
- I have some musings about improvements to CEGIS(T) that I haven't fleshed out. Something about overapproximating functions. The linear and semi-linear signature vector create good approximation functions. You can choose inputs are basically testing different approximations of the function, covering different spots of the search space. I'm using the overapproximation terminology loosely and probably wrong.

# Constraint performance and ideas

### Sort associative operand indices:
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

### Constant optimization
- When synthesizing expressions with constants, make sure the constants always come first. E.g. the first N nodes to choose from should be constants
- Find compact ways for the synthesizer to derive common large constants. E.g. N-bit bitmasks can be created by `(1 << N) - 1`, where `N` is some 7-bit integer. This allows you to synthesize all truncation masks for all possible bit widths. Also allows you to synthesize `-1`. Could be tweaked slightly to allow synthesizing `0` too. What other constants are common?

# Questions for matteo
- Do you have any problems where `opt_commutative`, `opt_insn_order`, `opt_dead_code_elimination`, `opt_common_subexpression_elimination` improved speed? In my experiments they've made performance performance worse.
    - I suspect these optimizations hurt when you have simple operators (and, add, xor). The payoff is probably stronger when you have MUL, DIV, or anything with a quadratic or higher. My intuition there is that you reduce the total number of places these huge multiplier circuits can appear.
- How does my implementation differ from `synth`? I'm doing the line stuff but I think there are some differences, specifically with how we encode operands?