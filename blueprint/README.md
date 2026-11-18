# Non-clairvoyant scheduling dependency graph

Open [the interactive blueprint](generated/Nonclairvoyant_Scheduling_Blueprint.html)
in a browser. Download the HTML first when viewing it on GitHub: it is
self-contained and works offline. Search declarations, select a proof view,
pan and zoom, and click nodes for Lean statements, source, prerequisites,
consequences, and collapsed dependency paths.

The overview is also available as [SVG](generated/Nonclairvoyant_Scheduling_Dependency_Graph.svg),
[PDF](generated/Nonclairvoyant_Scheduling_Dependency_Graph.pdf), and
[PNG](generated/Nonclairvoyant_Scheduling_Dependency_Graph.png).
The separate [module import graph](generated/modules.svg) shows file dependencies.

## Graph semantics

Arrows run from prerequisite to result. Proof dependencies come from
`ConstantInfo.getUsedConstantsAsSet` in the compiled Lean environment: references
in declaration types and proof or definition terms. The extractor includes
generated and private project helpers. Each view traverses omitted helpers to
the nearest displayed declaration, then removes redundant transitive arrows
when the displayed graph is acyclic. Every retained arrow includes its exact
compiled dependency path in `generated/graph_data.json`.

All 901 explicitly named source declarations are matched to compiled
constants, including the private helper. Mathlib dependencies are omitted.
The seven views cover the main results, upper bounds, general deterministic
lower bound, constant-OPT FIFO lower bound, batched deterministic lower bound,
randomized amplification, and all source declarations.

Ellipses denote theorems and lemmas; boxes denote other declarations.
Double borders identify main results. Green means part of the checked Lean
development, not independence from foundational axioms. The 210 reports in
`Audit.lean` are checked against `propext`, `Classical.choice`, and `Quot.sound`.
The overview labels are explanatory; click a result for its exact hypotheses.

## Rebuild

Install Graphviz (`dot`) and the project's pinned Lean/mathlib dependencies,
then run from the repository root:

```sh
./verify.sh
python3 blueprint/index_sources.py
lake env lean blueprint/Extract.lean
python3 blueprint/build_graph.py
python3 blueprint/check_graph.py
```

Source indexing supplies names, locations, and excerpts; it never supplies
dependency edges. The graph checker verifies complete source coverage, every
SVG node, and the compiled witness for every displayed arrow.
