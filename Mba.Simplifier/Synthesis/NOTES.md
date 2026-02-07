===================================
# Encoding

# A maximum number of constants is specified, each receiving a variable of
Constants:
const0 = BvConst("const0", WIDTH)
const1 = BvConst("const1", WIDTH)
const2 = BvConst("const2", WIDTH)

Enum Opcode
{
	Add = 0,
	Sub = 1,
	And = 2,
	...
}

Operand
{
	is_constant: Bool
	index: BitVec
}

# Line definitions
# First few lines dedicated to inputs ( [x, y] )
# All subsequent lines dedicated to operations
lines[0] = x
lines[1] = y
lines[N] = opcode operands[2] 
lines[N+1] = opcode operands[2] 
...

===================================
# Selection of semantics


line = lines[N]
opcode = line.opcode
op0 = line.operands[0]
op1 = line.operands[1]

# If the operand is a constant, represent it as an ITE chain selecting one of the possible constants
opnd0_const = ITE(op0.index == 0, constants[0], ITE(op0.index == 1, constants[1], constants[2]))
opnd1_const = ITE(op1.index == 0, constants[0], ITE(op1.index == 1, constants[1], constants[2]))
# Similarly if the operand is not a c onstant, represent it as an ITE chain selecting the semantic of a previous line
opnd0_value = ITE(op0.index == 0, semantics[0], semantics[1])
opnd1_value = ITE(op1.index == 0, semantics[0], semantics[1])

# We then select either a constant or line semantic using `is_constant`
op0 = ITE(op0.is_constant, opnd0_const, opnd0_value)
op1 = ITE(op1.is_constant, opnd1_const, opnd1_value)
# Finally the semantics for this line is represented as an ITE chain of all possible semantics.
semantics[0] = ITE(opcode == Add, op0 + op1, ITE(opcode == Sub, op0 - op1, op0 & op1 ... ))

===================================
Real world example: (a&b) + 255

Line definitions:
lines[0] = a
lines[1] = b
lines[2] = compCode2 (line2_op0Const line2_op0) (line2_op1Const line2_op1)
lines[3] = compCode3 (line3_op0Const line3_op0) (line3_op1Const line3_op1)
semantics0 = a

semantics1 = b

line2_op0_semantics = (let ((_let0 (= line2_op0 #b00))) (ite line2_op0Const (ite _let0 const0 const1) (ite _let0 a b)))

line2_op1_semantics = (let ((_let0 (= line2_op1 #b00))) (ite line2_op1Const (ite _let0 const0 const1) (ite _let0 a b)))

semantics2 = (ite (= compCode2 #b000) (bvnot line2_op0_semantics) (ite (= compCode2 #b001) (bvand line2_op0_semantics line2_op1_semantics) (ite (= compCode2 #b010) (bvor line2_op0_semantics line2_op1_semantics) (ite (= compCode2 #b011) (bvxor line2_op0_semantics line2_op1_semantics) (ite (= compCode2 #b100) (bvadd line2_op0_semantics line2_op1_semantics) (bvsub line2_op0_semantics line2_op1_semantics))))))

line3_op0_semantics = (let ((_let0 (= line3_op0 #b00))) (ite line3_op0Const (ite _let0 const0 const1) (ite _let0 a (ite (= line3_op0 #b01) b semantics2))))

line3_op1_semantics = (let ((_let0 (= line3_op1 #b00))) (ite line3_op1Const (ite _let0 const0 const1) (ite _let0 a (ite (= line3_op1 #b01) b semantics2))))

semantics3 = (ite (= compCode3 #b000) (bvnot line3_op0_semantics) (ite (= compCode3 #b001) (bvand line3_op0_semantics line3_op1_semantics) (ite (= compCode3 #b010) (bvor line3_op0_semantics line3_op1_semantics) (ite (= compCode3 #b011) (bvxor line3_op0_semantics line3_op1_semantics) (ite (= compCode3 #b100) (bvadd line3_op0_semantics line3_op1_semantics) (bvsub line3_op0_semantics line3_op1_semantics))))))


# TODO: How does thsi compare to the indirect encoding
===================================
Optimization constraints:

- Symmetric constants: The first constant must be used before the 2nd constant
- DCE, CSE
	- CSE actually hurts performance usually
- Idempotency pruning: Ban a&a, a|a, a^a; similarly a&0, a&-1, a|-1
- Constant folding: At least one operand must not be constant
- Commutative ops: Sort indices of commutative operators. 
	- Constants move to the right
- Unary operand pruning: If `opcode == NOT, NEG, ...`, constrain the 2nd operand index to be zero.
- Independent instruction reordering: If two instructions are next to each other and do not depend on each other, sort them:
	%0 = a+c
	%1 = a+b
	=>
	%0 = a+b
	%1 = a+c
	// can sort by both opcodes and indices of operands
- Smart encodings of indices. Use minimum bits necessary(even fewer than synth I think for indices)
- Optional: Only allow multiplication if one operand is constant




Additional ideas:
- Fence constraints
	- Tree encoding



























































=====================



# Ideas to explore:

### Synthesize trees instead of DAGs
- Solver needs to synthesize less operand numbers
- Think of the tree as an operand stack. `a+b` has the stack `a,b`, op2 is simply `line_index - 1`. More thought needed on finding the index of `a`.

### Variable permutation idea from "SAT-Based Exact Synthesis" paper

- If two variables are symmetric, assert that `a` must be used before `b`.
- Add a "truth table component". Instead of having and, or, xor, neg, instructions, add a truth table component that can specify any 2-variable truth table.


### Optimize encoding of opcode selectors
- Instructions are created as one big conditional select of `N` values, where `N` is the number of components (ignoring upper or lower bounds)
- Different encodings imply vastly different solving times for some `N`s.
- A `select3` encoding improved my synthesis runtime by 50%. Tldr when `N == 3`, the optimal encoding is `If(Extract(1,1,index) == 1, elements[2], If(Extract(0,0,index) == 1, elements[1], elements[0]))` where `index` is a 2-bit bitvector.
- 'select3' might actually not be optimal. There's another encoding called `one-hot` where you instead allocate 3 bits 
- On the boolean `~(a|b|c|d|e|f|g)`, my synthesizer is twice as fast as `synth` when using the `select3` encoding. I used the same set of components (AND, OR, NOT) with the maximum number of constants set to zero.

- For picking the opcode you can do a one-hot encoding(one boolean per possible opcode) or a bit-vector encoding(create a bitvector that can hold values 0..N). I'm doing the latter all the time and I think `synth` is too. But we could instead mix the encodings.
- One idea I have is to always use the bit-vector encoding, but for the `not` operator, use a 1-bit selector variable. The idea being that, choosing a unary means that the 2nd operator is set to zero, which enables a whole bunch of search space pruning. If we can make the "is this a not" extremely obvious, 

### Optimize encoding of operand index selectors
- Same ideas from above^ apply to selecting operands.
- Another idea: We're asking the solver to find two operand indices that are less than `i`. In most cases we don't want them to be equal, so we're looking for two indices such that `op0 < i-1` and `op1 < op0`. Does this have a more efficient encoding?

### Heuristic selection of components and some other stuff
- Recently synthesized `(((x|16)+y)^y) >> 4` as a part of some bit blasted circuit.
- Could we identify outermost right shifts by saying "0th bit depends on bits 4..63, meaning there's a right shift"
- You can check if an expression is nonlinear by asking a solver if any output bits depend on bits of input variables that are above it.

You can detect outermost shifts easily. Compute the maximum gap between the lower and upper bits. E.g. `(((x|16)+y)^y) >> 4` has a maximum gap of 4.
Then shift the expression left by the maximum gap.. `((((x|16)+y)^y) >> 4) << 4`. If there is no more dependencies between the upper and lower bits, very high chance you have an outermost shift.


### Used variable criteria
Ask the SMT whether any variables are dead. If they are not dead, add a constraint that a variable must have at least one use.

### CEGIS pruning
- We can analyze the knownbits of the input expression to immediately prune invalid candidates.
-   Though this might actually be a wasteful query. 
- I have some musings about improvements to CEGIS(T) that I haven't fleshed out. Something about overapproximating functions. The linear and semi-linear signature vector create good approximation functions. You can choose inputs are basically testing different approximations of the function, covering different spots of the search space. I'm using the overapproximation terminology loosely and probably wrong.

# Picking IO points for booleans
CEGIS on booleans often degenerates to an exhaustive search. Because there are many booleans that behave identically on all points but one...

### On the encoding of constants
From `synth` comments:
```
        Attributes:
        func: The function that this program implements.
        insns: List of instructions.
            This is a list of pairs where each pair consists
            of an Op and a list of pairs that denotes the arguments to
            the instruction. The first element of the pair is a boolean
            that indicates whether the argument is a constant or not.
            The second element is either the variable number of the
            operand or the constant value of the operand.
        outputs: List of outputs.
            For each output variable in `spec` there is a tuple
            `(is_const, v)` in this list. `is_const` indicates that
            the output is constant. In this case, `v` is a Z3 constant
            that gives the value of the constant output. If `is_const`
            is false, `v` is a Python int that indicates the number of
            the instruction in this program whose value is the output.
            Note that the first n numbers are taken by the n inputs
            of the program
        """.
```

Adding one bit to indicate whether an instruction is a constant seems to be a good idea.

# Constraint performance and ideas

# Const multiplication encoding


### Sort commutative operand indices:
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

# Sort associative operations
- `b + (a + c)` => `a + (b+c)`
- We could steal some ideas from SAT based graph canonicalization tools. Maybe SAT based canonical labeling or the SAT NPN canon papers

# Optimization of constant operands
- For shift instructions you can add a dedicated shift constant field. It's like 5 bits. I think this encoding is actually cheaper than allocating a full extra constant.
- For some booleans it would make sense to ban nonlinear multiplication

# SAT ideas
https://dl.acm.org/doi/10.1145/3670405

"We propose a novel SAT-based approach to graph generation. Our approach utilizes the interaction between a CDCL SAT solver and a special symmetry propagator where the SAT solver runs on an encoding of the desired graph property. The symmetry propagator checks partially generated graphs for minimality with respect to a lexicographic ordering during the solving process."

# Fence constraints
The sat exact synthesis paper talks about fence constraints. Instead of allowing any line to read from `0 .. i-1`, they can read from `window .. i-1`, where window is some constant.

We could experiment with this. It also makes code more efficient because it minimizes live ranges.

### Constant optimization
- When synthesizing expressions with constants, make sure the constants always come first. E.g. the first N nodes to choose from should be constants
- @MATTEO Is this a good idea^? Does `synth` already do this?
- Find compact ways for the synthesizer to derive common large constants. E.g. N-bit bitmasks can be created by `(1 << N) - 1`, where `N` is some 7-bit integer. This allows you to synthesize all truncation masks for all possible bit widths. Also allows you to synthesize `-1`. Could be tweaked slightly to allow synthesizing `0` too. What other constants are common?


### Percy
- Percy implements SSV, MSV, DITT encodings in the most efficient ways possible https://github.com/whaaswijk/percy/blob/master/include/percy/encoders/ssv_dag_encoder.hpp
- They directly invoke a sat solver rather than going through a QFBV solver
- We can probably get huge speedups by using optimal encodings for variable selection and such. Precomputed optimal circuits for cardinality,

- Percy does not use cadical or cryptominisat. Instead they use bsat or some other solver. 
```
Moreover, it is
not clear how the various encodings and constraints interact
with different SAT solvers. To date no comprehensive quantitative comparison of the various methods exists. This presents
difficulties in the design of new systems, as there is no data
to use as a basis for any design choices. Another hurdle is
that, like many EDA algorithms, it is difficult to parallelize.
Some efforts have been made in parallelizing SAT solvers
using techniques, such as cube-and-conquer, clause sharing,
and portfolio SAT solvers which apply different SAT solvers
in a parallel or distributed manner [24], [25]. This has proven
difficult, partially due to theoretical limitations of the resolution procedure [26]. Moreover, solvers based on these methods
are typically domain agnostic, and do not take advantage of
specific domain structure
```
- Could these topology ideas be extended to general bitvector problems?
- Generics solvers are "domain agnostic". Is there some sat solver that might have better performance on these problems?

# MISC
- Got a 2x performance boost on a hard problem by using a MUX selector when `N > 12`. Basically instead of doing 12 ITE nodes, you can do a binary search. Only pays off for large N(12 or more) though

Implies(a|b|c|d, statement) should be writen as 4 different imply statements. For some reason the solver is better at handling this


# Optimizing reasoning about symmetry and other pruning constraints
Most of our optimization constraints are like "If this operation has an commutative opcode, make the 1st operand be smaller than the 2nd one". The commutative check is implemented using `N` comparisons for however many opcodes you have.

Instead we can sort our component IDs based on their properties. commutative operators should be near each other, allowing for a simple integer comparison instead of a linear set of ITEs.

Similarly using the bitvector encoding for opcode selectors, there are padding bits leftover. You want to make the least expensive component(bitwise) be assigned to this padding bit by placing it at the end. Because the solver will probabilisticaly pick the last component more often than others

# Optimizing CEGIS
CEGIS is very expensive because you are cloning the candidate expression for each input combination. At least that's the only way I know of doing it. If you want to assert that two functions `f0(x, y)` and `f1(x, y)` are equivalent on `(111, 323)`, you clone the functions, substitute in the input combination, and assert that `a == b`. 

At one point I was using 1000 IO samples as my starting point for CEGIS. When I instead switched to 10, the problem I was working on solved 100x faster. So minimizing the number of points is very important. Or alternatively so is finding an alternative formulation.

One alternative formulation idea I have is to take e.g. a 5-bit BitVector, zero extend it to your expressions bit width, then run some ultra simple hash like function on it. You can then do a for-all query over this 5-bit variable, asserting that your expression is equivalent for these input combinations. 
    - Scratch that: DO not use a hash function, the solver won't be able to reason about it with the forall query.
    - If you instead just plugged in Zx(56, BitVec(x, 8))

Another idea is to heuristically pick the initial input combinations. We want as few input combinations as possible. What makes a good input combination?

Last idea is a revision of CEGIS inputs. Bad inputs cause the solver to get stuck. During CEGIS we can maintain a list of candidate expressions, and a list of inputs. After say 10 rounds of CEGIS, we can synthesize a new, smaller set of inputs that would cover all corner cases.

For one expression with complex bitwise constants `(((x|1111)+y)^y) >> 4`, I had extremely good results by picking two initial input combinations:
- One that maximizes the number of set bits in the output `f(40, 64)`
- One that minimizes the number of set bits in the output `f(160, 89)`

Similar ideas:
- Find inputs that alternate the output bits as strongly as possible
- Find inputs that maximize the distance from your current outputs

For booleans you might be able to classify it. Is it sparse or dense? That will inform your point selection. 

At one point CEGIS found the fitting expression `((((x:i8|87:i8)+y:i8)^y:i8)>>4:i8)` for our input.

Another idea: Pick inputs based on Sygus difficulty. Pick an two or three input combinations... can Sygus efficiently handle it? Yes => it's probably a bad input pair

# Case study:
Synthesizing the 8-bit expression `((x ^ 60) * ((82 - (x * (x ^ 60)))))` with 7 instructions, and the components:
- CONSTANT(up to 2), xor, add, sub, mul

CEGIS got through ~5 iterations and then got stuck and couldnt find a solution. If I instead pick the initial inputs: `188, 255, 2, 131, 128`, CEGIS instantly finds a solution in ~300ms after one iteraiton.

I derived these inputs by taking the input expression and asking an SMT solver to synthesize some inputs using the ideas from the "Optimizing CEGIS" section. Specifically the min/max popcount minimizing inputs, alternating bits maximization, a boundary case(MSB set), and one other heuristic I can't be bothered to explain (sensitivity).

After computing these inputs, I picked only the ones where the CEGIS solution and input expression behaved differently.

# Abusing arithmetic mod 2^n properties
`(RSI + RBP) & 0xFFFFFFFF `

Look at knownbits. If the upper 32 bits are known to be zero, synthesize a 32-bit expression and zero extend it later. This is always legal if you're restricted to bitwise, arithmetic, and constant operators.

# Debugging CEGIS
On the input `(((x|1111)+y)^y) >> 4`, using `1` initial input sample gives terrible CEGIS results. CEGIS gets stuck - the solver can't find any solution after the 5th iteration. If I use 5 random inputs instead, it instantly finds a solution.

I think these search space constraining heuristics from `synth` hurt for normal CEGIS, but may extremely help CEGIS(T). 

# "Grouped" encoding of opcodes
Currently I have a bitvec representing an enum of opcodes like:
```
Const = 0
Not = 1
And = 2
Or = 3
Xor = 4

Add = 5
Sub = 6

Mul = 7
```

But instead a different encoding may be easier for the solver:
```
enum Opcode
{
    Const()
    Bitwise(bitwise_opcode, line0, line1) # One of the bitwise operators: NOT,AND,OR,XOR
    LinearArithmetic(is_add, line0, line1) # ADD or SUB
    Mul() # Gets its own opcode because it's very expensive
}
``

The idea is that it might be easier for the solver to reason about this. Similar operatrs get grouped close together.

I guess this is called a hierarchical encodings. It's definitely easier for the solver to reason about.

Initial pass at a hierarchy:
```
Bitwise(NOT, AND, OR, XOR)
Arithmetic(ADD,SUB,MUL) # maybe move MUL out?
Shift(SHL, LSHR)
CMP(EQ, NEQ, ULT, UGE, SLT, SGE)
DIV/UREM(DIV, UDIV, SMOD, UREM, SREM)
ITE
``

# "Local CEGIS" from fastsynth
https://github.com/kroening/fastsynth/blob/master/src/fastsynth/local_cegis.h#L42

Seems to extend CEGIS(T) with additional heuristics? Neighborhoods of solutions, exploring neighboors. collecting constraints on neighborhoods?


# Encodings
We need to get a better picture of how different encodings of the symmetry breaking constraints perform.

### Constraint optimization
The constraints we're encoding have an extreme amount of redundancies and overlap. Some kind of optimizing compiler should be able to optimize these constraints. Redundancies and also general bitvector simplifications can be performed.

`SLOT: SMT-LLVM Optimizing Translation` yields a 1.5x or 2x speedup on some benchmarks.
    - Their conversion from SMT to LLVM IR is exponential time because they did not use a hashmap??????

Improvements:
- Annotate line / operand index variables with range annotations on the LLVM IR level
- Increase hardcoded llvm limit variables for enhanced precision. LLVM default value of `MaxAnalysisRecursionDepth` is 6, blocking a lot of opts
- Enhanced knownbits precision. Use a solver or adhoc algorithm. "Easy" to get a little bit of added precision over what LLVM offers
- Enhanced undemanded / demanded precision. Using solver or adhoc algorithms
    - Global undemanded bits analysis (maybe applied only to the selector variables). Delete all bits that are nil
- Upgrade LLVM IR version (SLOT on llvm15)
- Identify additional missed optimizations
    - Use our synthesizer tools to spot these automatically

# AIG and CNF minimization
- https://github.com/bitwuzla/bitwuzla/discussions/128
- Issues claim ABC does not help CVC4. Still maybe it could help. I have a strong feeling it would.

TODO for me today (2/7/2026): Try AIG minimization

# Incremental solving
It might make sense to completely disable incremental SAT solving. 

# TODO:
- Add back independent line reordering constraints





# Questions for matteo
- How does my implementation differ from `synth`? I'm doing the line stuff but I think there are some differences, specifically with how we encode operands?
- There are different encoding strategies for the lines. 
    - "SSV" (Single Selection Variable) = the intuitive way
    - "MSV" (Multiple Selection Variables) = less intuitive way. Operands encoded "separately". 
        - Smaller CNF encoding
        - Scales better when you have many components with 3 or more variables.
        - Strictly worse than SSV when you only have 1 and 2 variable components
    - "DITT" (Distinct Input Truth Tables) = I have no idea. May be similar to the truth table component idea I proposed
    - Which encoding is Synth using?
- What is the lower and upper bound on the number of unique components(add, or, xor) that you've been using? What does the distribution look like?
- Does `synth` have the ability to specify upper bounds for each component? 

Interested in seeing how our compionnts compare. I feel like I'm beating synth quite often.

Others:
- BRAHMA. Intractable examples. Take forever even with exact number of components specified(but not layout)
    - Confused at how they even synthesized these *with* components specified in the timings they gave. Especially consider how much slower solvers were in 2011
- 


From your file:
```
In this case the second operand 'insn_1_opnd_1' of the 'not', 'neg' and 'bswap' components is unused and we can let the solver know that it can have any value. This is done through an implication because only if the operation 'insn_1_op' at 'loc_1' is 'not', 'neg' and 'bswap' we want to ignore the second operand. In the case the operation was a component with two operands, we wouldn't want to do this.
```

Why assert to the solver that it can have any value, instead of asserting that it must be zero? Doesn't `zero` prune the search space further?
