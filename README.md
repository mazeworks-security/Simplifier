# Simplifier
`Simplifier` is a framework for the deobfuscation of Mixed Boolean-Arithmetic (MBA) expressions. It was designed with a focus on performance and scalability to real-world MBAs. 

## Design
We implement several structural and algorithmic optimizations, namely:

* Expressions are represented as hash-consed, immutable nodes in a directed acyclic graph
* Term rewriting is performed using ISLE, allowing rules to be expressed declaratively and lowered to more efficient tree matching code.
* Caching is used to avoid duplicated work
* The number of substitutions and SiMBA invocations is carefully minimized

# Usage
To simplify a single expression, use:
```
Simplifier.exe "expr"
```

As an example:
```
$ Simplifier.exe "7471873370*~(16832296021645948&y) + 3735936685*16832296021645948 + 3735936685*y + 7471922744 - 49374"

Expression: (((((7471873370*(~(16832296021645948&y)))+(3735936685*16832296021645948))+(3735936685*y))+7471922744)-49374)

Simplified to: (3735936685*(16832296021645948^y))
```

The executable accepts several arguments, e.g., `-b` for specifying the bit width of the input expression, and `-z` for proving the equivalence between the input expression and the simplified result. Use the command line option `-h` to see the available settings.

# Supported Platforms 
`Simplifier` is only supported on Windows. Note that both Visual Studio 2022 and ClangCL are required to build the project.

# Building
Clone `Simplifier`:
```
git clone --recursive https://github.com/mazeworks-security/Simplifier.git
cd Simplifier
```

Build `EqSat` in release mode:
```
cd EqSat
cargo build --release
```
Build `Simplifier` in release mode:
- Open `Simplifier.sln` with visual studio
- Change the build configuration from `Debug` to `Release`
- Build the solution

Building `Simplifier` requires .NET 8 and Visual Studio 2022 w/ ClangCL.

# Status
`Simplifier` has reached a stage where it works quite well on general MBAs. That said, it is still under active development. 

# Equality Saturation
`Simplifier` contains an equality saturation based simplifier. To enable it alongside the standard simplification routine, use the `-e` flag.

Example:
```
Simplifier.exe "x+y" -e
```

Note that the equality saturation based simplifier should not be used in general - it is superseded by the general simplification algorithm.