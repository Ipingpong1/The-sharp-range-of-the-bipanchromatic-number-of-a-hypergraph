Lean certificate for the sharp bipanchromatic range theorem
=========================================================

STATUS: The full nontrivial hypergraph range theorem is proved in Lean.
The stronger realization by p-uniform hypergraphs with common core of
exactly a vertices is also proved. Publication novelty is not established.

Scope
-----
Natural-number parameters with p >= 2, 1 <= a < p, and 2*p <= n+a.
Hypergraphs have finite nonempty families of nonempty edges. Isolated
vertices are allowed. Colorings partition the entire vertex set into
nonempty transversals. Bipanchromatic classes have size >= 2 globally.
Alpha is minimized among optimal panchromatic colorings only.

Main results
------------
Bipanchromatic.sharp_range           Complete iff for every possible b.
Bipanchromatic.sharp_range_witness   p-uniform witness with core size a.
Bipanchromatic.universal_lower       Universal improved lower bound.
Bipanchromatic.model_value           Exact model formula, with q >= 1.

The first two are in SharpRange/Full.lean. The precise propositions and
lower/upper bound formulas are in SharpRange/Target.lean. The definitions
of hypergraphs, partitions, and the three parameters are in
SharpRange/Definitions.lean. All former target propositions now have proofs.

Build and verify
----------------
Pinned versions: Lean 4.34.1, mathlib v4.34.1. Exact dependency commits are
in lake-manifest.json. Keep that manifest when reproducing the build.
With elan installed, in this directory run:

    lake exe cache get
    python3 verify.py

The current local checkout already has the dependencies, so only the
second command is needed. Its .lake/packages symlink reuses an existing
local mathlib cache; it is not included in the source bundle and is not
needed for a fresh checkout.

verify.py builds the project without warnings, audits all 116 public
proved declarations, checks the final theorem types, and invokes:

    lake env leanchecker --fresh --verbose SharpRange.Full

This replays the final module and its imported declarations through the
same Lean kernel in a fresh environment. It is not an independent proof
assistant or an independently implemented checker. It includes Mathlib
and can take considerably longer than the project build; the checker
does not report intermediate progress. No native evaluation
is used in the proof dependencies. The allowed axioms are only propext,
Classical.choice, and Quot.sound; sorryAx and custom axioms are rejected.

Recorded evidence
-----------------
build.log             Build result.
verification.log      All public theorem axiom reports.
kernel-replay.log     Fresh kernel replay result.
verification.json     Status, toolchain, final theorems, hashes, and axioms.
theorem-index.json    Names and source locations of the proved declarations.

Proof map
---------
Arithmetic.lean                  Arithmetic and discrete intermediate values.
SharpRange/Definitions.lean       Exact definitions and general upper bounds.
SharpRange/Pairing.lean           Constructs disjoint core/partner pairs.
SharpRange/Packing.lean           Extends packings to full partitions.
SharpRange/Recoloring.lean        Actual whole-class dissolution construction.
SharpRange/UniversalLower.lean    Extracts a coloring's sizes; proves lower bound.
SharpRange/Construction.lean      Model hypergraph, n,p,a, and transversals.
SharpRange/ModelValue.lean        Exact bipanchromatic number of the model.
SharpRange/SizeVectors.lean       Majorization and one-vertex transfers.
SharpRange/TransferPath.lean      Transfer termination and intermediate values.
SharpRange/Endpoints.lean         Numerical bounds and concentrated endpoint.
SharpRange/Balanced.lean          Full numerical size-vector spectrum.
SharpRange/Relabel.lean           Preserves parameters on relabeled vertices.
SharpRange/Target.lean            Precise statement and formulas.
SharpRange/Full.lean              Final theorem and stronger witnesses.
SharpRange/Audit.lean             Type checks and complete axiom audit.
SharpRange.lean                   Project entry point.

Boundary correction
-------------------
The earlier auxiliary model-value target omitted q >= 1 and therefore
included the one-vertex case a=1,q=0, where no bipanchromatic partition
exists. The target now requires q >= 1, exactly as in the sharp-range
regime q=p-a>0. The main mathematical theorem was unchanged.

Other results in the working note (including the a=0 and a=p boundary
arguments) are not claimed as part of this formal certificate.
