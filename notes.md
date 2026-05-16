# Finite-category enumeration notes

This project enumerates finite categories by total morphism count, not by a fixed
object count.  The core representation follows the arrows-only view used in
Cruttwell/Leblanc and in the SmallCategories tooling:

- choose the identity arrows, one per object;
- assign every arrow a source and target identity;
- fill the partial composition table for composable pairs;
- enforce identities, typing, and associativity;
- classify by canonical relabelling of objects and arrows.

The current implementation is exact.  It searches canonical hom-count matrices,
fills the remaining composition table with incremental associativity propagation,
and stores one representative key per selected relation: categorical
equivalence, strict isomorphism, or raw generated-key equality.

Useful references:

- Geoff Cruttwell, "Counting finite categories":
  https://www.reluctantm.com/gcruttw/publications/ams2014CruttwellCountingFiniteCats.pdf
- SmallCategories database and code:
  https://smallcats.info/about
  https://github.com/diracdeltafunk/SmallCategories
- `nauty-parser`, used for the secondary `thin --digraph6` path:
  https://hackage.haskell.org/package/nauty-parser

Known total counts for all finite categories up to isomorphism by morphism count
start:

```text
n = 1: 1
n = 2: 3
n = 3: 11
n = 4: 55
n = 5: 329
n = 6: 2858
n = 7: 36440
```

The implementation should treat these as regression targets.  Small values are
unit-tested; larger values are intended as benchmark/check runs because exact
search grows quickly.

## Cauchy-complete focus

For ordinary finite `Set`-categories, Cauchy complete means idempotent complete:
every idempotent endomorphism `e : x -> x` must split through some object `y`.
With this code's left-to-right composition convention, a split is stored as
arrows `r : x -> y` and `s : y -> x` such that:

```text
r;s = e
s;r = id_y
```

This removes much of the one-object nilpotent-monoid mass.  In particular, a
finite one-object Cauchy-complete category has no non-identity idempotents, so
its endomorphism monoid is a group.

The CLI `count` and `generate` representative keys now default to quotienting
by categorical equivalence: each category is first replaced by a skeletal full
subcategory with one object from each isomorphism class, then canonicalized.
This explains the former `n = 9, k = 3` one-off against OEIS, reducing that
entry from 458 to 457.  It also reduces the local `n = 9` entries for `k = 4`
and `k = 5`, so OEIS as written is not simply this full equivalence quotient.

The representative relation is selectable on the CLI:

```text
--up-to equivalence   # default; skeletal category, then canonical key
--up-to isomorphism   # strict isomorphism; canonical key
--up-to equality      # raw generated category key, with no final quotient

--up-to-equivalence
--up-to-isomorphism
--up-to-equality
```

The `equality` mode is mostly a debugging/diagnostic view of the search output:
the upstream shape and component generation still use normalized internal
representatives, so it should not be interpreted as a count of all labelled
categories.

### OEIS discrepancy at n = 9, k = 3

OEIS A384134 and Cruttwell's Cauchy-complete table list the row

```text
n = 9: 2, 278, 457, 371, 151, 39, 10, 2, 1
```

The local strict-isomorphism generated row is

```text
n = 9: 2, 278, 458, 371, 151, 39, 10, 2, 1
```

The one extra strict class at `(n,k) = (9,3)` is not a canonicalization
duplicate.  The two categories have hom-count matrices

```text
1 1 2      1 2 2
1 1 2  and 0 1 1
0 0 1      0 1 1
```

They are equivalent to the same two-object skeleton, the category with two
parallel arrows, and they are opposites of each other: one duplicates the source
object of the skeleton and the other duplicates the target object.  They are not
isomorphic; for example, the multisets of object `(outgoing homs, incoming
homs)` are

```text
{(4,2), (4,2), (1,5)}
{(5,1), (2,4), (2,4)}
```

Since OEIS matches the strict-isomorphism row at `k = 4` and `k = 5`, but not
the equivalence row there, the discrepancy is probably a one-entry table error
or an unstated ad hoc convention in the source table rather than a systematic
equivalence quotient.

The current CLI supports:

```text
cat-enum count --max-morphisms N --cauchy-complete
cat-enum count --max-morphisms N --up-to isomorphism
cat-enum generate --morphisms N --cauchy-complete --up-to equality
cat-enum verify --cauchy-complete DIR
cat-enum copresheaves --morphisms N --max-elements M
```

The `copresheaves` command counts bounded finite copresheaves `C -> Set` over
the in-memory canonical base categories.  Counts are raw functors on standard
finite fibers, not yet quotient classes under natural isomorphism or base
automorphisms.

## Disjoint unions and connected components

The code now separates two notions of decomposition:

- support equivalence classes, used for biconnected components;
- undirected connected components of the support graph, used for disjoint
  unions.

If `C = C_1 + ... + C_r` is a disjoint union, then finite copresheaves factor:

```text
Set^C ~= Set^(C_1) x ... x Set^(C_r)
```

The size-counting generating functions therefore multiply.  The implementation
uses this by computing copresheaf counts on each connected component and
convolving the counts, rather than searching all object profiles of the
disconnected category at once.

The CLI also writes biconnected representative-key caches under:

```text
.cat-enum-cache/v1/biconnected/
```

Each cache file is keyed by `(morphisms, objects, cauchy)` and contains one
canonical representative key per line.  The pure enumeration functions are still
available for tests and deterministic in-memory use; the CLI `biconnected` and
`generate` paths use the file cache.

## Current generation speedups

The `generate --cauchy-complete` path now uses three targeted shortcuts in
addition to the biconnected cache:

- One-way gluings of one-object group components are generated as finite
  `(G,H)`-bisets.  Instead of enumerating labelled left/right action functions,
  the code enumerates subgroup conjugacy classes of `G x H^op`, forms
  transitive coset actions, and combines them as orbit multisets.  This gives
  one representative per biset isomorphism class before category
  canonicalization.
- Skeleton canonicalization first splits disconnected quotient-support
  components.  Sparse high-object skeletons therefore only use factorial
  relabelling inside small connected quotient pieces, instead of permuting all
  isolated biconnected components at once.
- For Cauchy-complete categories with `morphisms - objects <= 2`, the cached
  CLI path uses a direct list of connected building blocks: terminal objects,
  `C2`, `C3`, parallel arrows, singleton arrows attached to `C2`, the
  two-object trivial groupoid, and the two 3-object fork posets.  Disjoint
  unions of these blocks cover the whole small-extra range.
- For cached Cauchy-complete generation with total excess 3 or 4, the CLI
  assembles disjoint unions from cached connected blocks.  A connected category
  with excess `e = morphisms - objects` has at most `e + 1` objects, so these
  sparse high-object cases can avoid the full labelled skeleton walk.
- Full generated representative-key sets are cached under
  `.cat-enum-cache/v4/generated/<mode>/`.  The first run still computes and
  writes the missing object-count files; subsequent runs read representative
  keys directly.

Recent local timings on this machine:

```text
generate --morphisms 10 --objects 2 --cauchy-complete:
  before biset representatives: ~94.8s
  after:                         ~9.1s

generate --morphisms 10 --objects 7 --cauchy-complete:
  before quotient-component skeleton keys: ~114.8s
  after:                                    ~14.4s

generate --morphisms 10 --objects 8 --cauchy-complete:
  before small-extra shortcut: ~15.4s
  after:                        ~0.13s

generate --morphisms 10 --cauchy-complete:
  before this round: exceeded 120s
  after:             ~30.2s

generate --morphisms 11 --objects 3 --cauchy-complete:
  before independent one-object profunctor skeletons: exceeded 90s
  after:                                           ~35-40s

generate --morphisms 11 --objects 7 --cauchy-complete:
  before excess-4 connected-block assembly: ~57.3s
  after:                                    ~0.68s

generate --morphisms 11 --objects 8 --cauchy-complete:
  before excess-3 connected-block assembly: exceeded 120s
  after:                                    ~0.14s

generate --morphisms 11 --cauchy-complete:
  cold v2 generated-key cache: ~119.5s
  warm v2 generated-key cache: ~0.38s
```

The next cold-start bottleneck is low-object generation for `n = 11`, especially
the 2- and 3-object slices.  Warm-cache runs are now well below one minute.

## Group generation literature for one-object Cauchy components

One-object Cauchy-complete biconnected components are finite groups.  That is
good news algorithmically: enumerating groups up to isomorphism is a mature
computational group theory problem, and we should not keep treating it as a
generic associative multiplication-table search.

The main references worth tracking are:

- The GAP Small Groups library:
  https://docs.gap-system.org/pkg/smallgrp/doc/chap1.html
- Hans Ulrich Besche, Bettina Eick, E. A. O'Brien,
  "A millennium project: constructing small groups":
  https://www.worldscientific.com/doi/abs/10.1142/S0218196702001115
- Newman/O'Brien p-group generation, exposed in Magma and GAP/ANUPQ:
  https://www.math.ru.nl/magma/text286.html
  https://gap-packages.github.io/anupq/doc/chap1.html
- Bettina Eick, Max Horn, Alexander Hulpke,
  "Constructing groups of 'small' order: recent results and open problems":
  https://www.quendi.de/data/papers/EHH2018-small-groups.pdf
- GAP GrpConst, which packages several construction methods:
  https://gap-packages.github.io/grpconst/

### What the literature says

The Small Groups library is not just a lookup table of multiplication tables.  It
is organized in layers by families of orders and was built from specialized
construction algorithms.  GAP exposes this as `SmallGroup`, `AllSmallGroups`,
and `NumberSmallGroups`; the library documentation also records which ranges are
covered and which exceptional orders are hard.

The current algorithmic taxonomy is:

- Nilpotent groups: reduce to p-groups, because a finite nilpotent group is the
  direct product of its Sylow subgroups.
- p-groups: use the Newman/O'Brien p-group generation algorithm.  It builds a
  descendant tree along the lower exponent-p central series, using pc
  presentations, p-covering groups, p-multiplicators, nuclei, automorphism
  groups, and orbit reduction to produce one representative per isomorphism
  class.
- Solvable non-nilpotent groups: use extension methods.  The most important
  production method in the cited papers is the Frattini extension method:
  enumerate possible Frattini factors, then construct and reduce extensions
  having that factor.
- Special solvable orders: for orders `p^n q`, the cyclic split extension method
  constructs semidirect products from p-groups and cyclic groups, relying on
  automorphism groups of p-groups.
- Non-solvable groups: start from perfect groups and construct upward extensions
  or cyclic extensions, then reduce by isomorphism tests.  This is real
  machinery, but it is probably not the first thing this project needs.

### What we should implement first

For this category enumerator, the group order is the morphism count of a
one-object component.  Since the whole category has bounded morphism count, we
get a lot of value from small, exact constructors before attempting the full
SmallGroups/GrpConst stack.

Recommended implementation path:

1. Create a small `CodexSlop.Group` module whose output is a normalized
   multiplication table, then convert that table to a one-object
   `FiniteCategory`.

2. Replace the hard-coded order `<= 8` group list with general abelian group
   construction.  Factor `n`; for each prime-power part `p^a`, enumerate
   partitions of `a`; each partition gives a product of cyclic groups
   `C_(p^lambda_1) x ... x C_(p^lambda_r)`.  Combine prime parts by direct
   product.  This gives every finite abelian group exactly once up to
   isomorphism.

3. Add small nonabelian split extensions before full p-group generation.  A
   semidirect product `N semidirect Q` is determined by an action `Q -> Aut(N)`.  For
   `Q = C_m`, this is essentially a choice of an automorphism of `N` whose order
   divides `m`, modulo the natural conjugacies.  This covers many early
   nonabelian cases, including `S3 = C3 semidirect C2`, dihedral groups, and
   `A4 = V4 semidirect C3`.

4. Add explicit p-group classifications for very small exponents before the
   full Newman/O'Brien algorithm.  Orders `p`, `p^2`, and `p^3` are easy and
   would remove a lot of generic table search:
   `p`: `C_p`;
   `p^2`: `C_(p^2)`, `C_p x C_p`;
   `p^3`: the three abelian groups plus the standard nonabelian groups
   generated by a small number of presentations, with special handling for
   `p = 2`.

5. Use the SmallGroups counts as regression tests, not as runtime data.  For
   example, the current tests already check the known counts for orders through
   8.  We can extend this as constructors are added.

6. Defer the full p-group generation algorithm until the above stops being
   enough.  A real implementation needs:
   pc presentations, linear algebra over `F_p`, automorphism group actions,
   orbit-stabilizer reduction, p-covers, nuclei, standard presentations, and a
   table materializer.  It is implementable, but it is a much larger subsystem
   than the category generator itself.

7. Defer general Frattini extension construction even longer.  It is the right
   algorithmic family for broad solvable-group coverage, but it requires
   extension/cohomology machinery plus strong isomorphism rejection.  For our
   current bounded-morphism workflow, abelian groups, small p-groups, and
   semidirect products should move the practical frontier much sooner.

### Practical design notes

Represent groups internally by compact structural constructors for as long as
possible:

- `Cyclic Int`
- `DirectProduct GroupSpec GroupSpec`
- `Semidirect GroupSpec GroupSpec Action`
- later, `PcPresentation ...`

Only materialize the full multiplication table at the boundary where the category
enumerator needs a `FiniteCategory`.  This keeps group generation cheap, makes
isomorphism checks more structural, and avoids allocating `n^2` tables while
we are still pruning candidate groups.

Implemented so far:

- `CodexSlop.Group` owns one-object group construction.
- finite abelian groups are generated from prime factorizations and integer
  partitions;
- groups of orders `<= 15` are constructed directly from abelian groups,
  dihedral groups, dicyclic groups, and `A4`;
- groups of order `p^3` are constructed for odd primes using the three abelian
  groups, the Heisenberg group, and the nonabelian semidirect product
  `C_(p^2) semidirect C_p`;
- groups of order `pq` for distinct primes use the standard cyclic/semidirect
  classification;
- unsupported orders still fall back to the exact Latin-square/associativity
  search, preserving correctness at the cost of speed.

The next concrete patch should target multi-object biconnected Cauchy
components.  After the group constructors and group-specific canonicalizer, the
observed `n = 9` slowdown is dominated by two-object biconnected components,
not one-object groups.

## CSP backend experiment

The package includes an experimental `CodexSlop.CspSearch` module using the
Haskell `csp` package.  It models each composition-table cell as a finite-domain
variable and posts associativity as finite-domain constraints.  This validates
the CSP formulation and gives us a library-backed comparison point without
changing the main enumeration path.

Early benchmark results are not favorable for this particular library:

```text
biconnected shape, 6 morphisms, 2 objects, index 0:
  custom: 4 solutions, ~0.000s
  csp:    4 solutions, ~0.002s

biconnected shape, 7 morphisms, 2 objects, index 0:
  custom: 18 solutions, ~0.006s
  csp:    18 solutions, ~0.039s

biconnected shape, 8 morphisms, 2 objects, index 0:
  custom: 308 solutions, ~0.236s
  csp:    308 solutions, ~5.658s
```

On a 9-morphism, 2-object shape, the `csp` backend did not finish within the
two-minute probe window.  The likely reason is that associativity is not a
simple fixed-arity local constraint: the value of one composition cell selects
which other composition cell must be compared.  Encoding that through generic
n-ary arc consistency produces large constraints with expensive support checks.

Conclusion: the CSP idea is still good, but this Haskell `csp` library is not a
drop-in speedup.  Better next options are:

- keep improving the custom propagator with domain sets and watched
  associativity constraints;
- try a stronger external CP-SAT/SMT backend only behind an experiment flag;
- reformulate two-object biconnected components in terms of typed actions and
  pairings, where constraints are more local than whole-table associativity.

## Finite profunctor counts

The code now has a first `CodexSlop.Profunctor` layer for finite profunctors

```text
P : A^op x B -> Set
```

with fixed finite fibers.  A profile is a row-major matrix

```text
|A objects| x |B objects|
```

where entry `(a,b)` is the size of `P(a,b)`.  The solver uses two families of
action variables:

- left actions for each `f : a' -> a` in `A` and object `b` in `B`, mapping
  `P(a,b) -> P(a',b)`;
- right actions for each object `a` in `A` and `g : b -> b'` in `B`, mapping
  `P(a,b) -> P(a,b')`.

It enforces identity actions, left action composition, right action composition,
and the middle interchange law.  This is deliberately separate from the whole
category composition-table search: the constraints are action-shaped, so this is
the layer where CSP-style propagation is most likely to be useful.

Current exported functions:

```text
countProfunctorsForProfile :: FiniteCategory -> FiniteCategory -> [Int] -> Integer
countProfunctorsOfSize     :: FiniteCategory -> FiniteCategory -> Int -> Integer
profunctorCountsUpTo       :: Int -> FiniteCategory -> FiniteCategory -> [(Int, Integer)]

countProfunctorsForProfileCached :: FiniteCategory -> FiniteCategory -> [Int] -> IO Integer
profunctorCountsUpToCached       :: Int -> FiniteCategory -> FiniteCategory -> IO [(Int, Integer)]
```

Sanity checks in the test suite cover:

- terminal-terminal profunctors;
- terminal-to-category profunctors matching copresheaves;
- arrow-to-terminal profunctors giving presheaf-shaped counts;
- singleton fibers;
- disconnected source factorization.

Disconnectedness is already exploited: if either input category is a disjoint
union, `A^op x B` decomposes over pairs of connected components, and counts are
combined by convolution.  The next useful step is to cache these counts by
`(canonicalKey A, canonicalKey B, profile)`, then use the same action data to
replace cross-component composition-table search for two-component chains.

Profile counts are now cached under:

```text
.cat-enum-cache/v1/profunctor-counts/
```

The CLI exposes the cache-backed counter:

```text
cat-enum profunctors --left LEFT_KEY_OR_FILE --right RIGHT_KEY_OR_FILE --max-elements N
cat-enum profunctors --left LEFT_KEY_OR_FILE --right RIGHT_KEY_OR_FILE --profile CSV
```

The `--profile` CSV is row-major over `A` objects then `B` objects.  For example,
if `A` has one object and `B` has two, profile `2,3` means fibers of sizes
`2` and `3`.

## Up-to-equality (labelled-object) counting

The equality mode (`--up-to equality`) counts finite categories where object
labels matter but morphism labels within each hom-set do not.  Two categories
are equal iff they have the same object labelling, hom-count matrix, and
composition table.

This is the "labelled objects" semantics (Option A).  Objects are distinguished
by their index `0 .. k-1`; morphisms within a single hom-set are
indistinguishable except by their composition behaviour.

The equality mode is available through the `generate` subcommand:

```text
cat-enum generate --morphisms N --cauchy-complete --up-to equality
```

The `generate` pipeline uses cached biconnected-component and isomorphism keys.
The equality count for each isomorphism class is computed via a fast
hash-based routine (`equalityCount` in `CodexSlop.Canonical`) that generates
all `k!` object-permuted FNV-1a hashes of the composition table and
deduplicates by hash.  No full key strings are produced unless
`--write-reps` is also passed.

### Generation pipeline

```
isomorphism cache (pre-computed)
  → parseCategoryKey per key
  → equalityCount per category (hash-based, no strings)
  → sum per object count
```

### CLI

```text
cat-enum generate --morphisms 10 --cauchy-complete --up-to equality
10 morphisms: 45028 generated Cauchy-complete categories up to equality
  1 objects: 80
  2 objects: 2677
  3 objects: 10937
  4 objects: 18091
  5 objects: 10324
  6 objects: 2644
  7 objects: 267
  8 objects: 7
  9 objects: 1
```

With `--write-reps`, the full set of labelled-object category keys is written
to disk for each object count.  This is significantly slower (generates all
`k!` key strings per isomorphism class) and is intended for downstream tooling
rather than routine exploration.

### Performance notes

With warm caches (`.cat-enum-cache/v4/generated/`), equality counts are
available up to `n = 12` in roughly one minute.  The current bottleneck is
the O(k! × n²) hash computation for k ≥ 7, where hundreds of isomorphism
classes each produce 5040–40320 permutations.

Removing the large-`k` bottleneck requires computing the automorphism group
|Aut(C)| directly from the category's object equivalence classes rather than
brute‑forcing all `k!` permutations.  This would bring the per-category cost
from O(k! × n²) down to O(k²).

## Colimit–limit theorem for enrichment

The functor `U(-)-Cat : Preord^op → CAT/Set` (sending a preorder P to the
category of categories enriched over its underlying set) sends **all weighted
colimits** in the locally-posetal 2-category Preord to weighted limits in
CAT/Set.

This theorem is already at work in the decomposition pipeline but is not yet
fully exploited:

- **Coproducts → pullbacks over Set.**  A category whose support is a
  disjoint union of preorders factors over its connected components.
  The `supportsFor` blowup algorithm (`Shape.supportsForUncached`) is a
  concrete instance: a support preorder on k objects is decomposed into
  a quotient poset on q classes plus a composition of k into q parts,
  which is a colimit description.

- **Pushouts → pullbacks.**  The glueing of biconnected components along
  profunctor edges (the `generate` pipeline) can be understood as a
  weighted colimit in Preord, dualising to a weighted limit in CAT/Set.
  This suggests a systematic theory of "decomposition by profunctor
  profiles" where the enumeration of categories over a complex support
  is reduced to the enumeration over simpler supports and a limit
  computation.

A future optimisation: use the theorem to replace the brute-force
`enumerateCardinal` filter with a limit computation over a decomposition
of the Cardinal lattice, though the gains for ℕ with min are marginal
since ℕ has no non-trivial colimit decompositions.

The theorem is documented in `CodexSlop.Enrichment`.

## Up-set lattice enrichment benchmarks

We benchmarked enrichment over all 24 unlabeled posets on 1–4 elements
(Equivalently: all distributive lattices J(P) of up-sets of such posets).
For each lattice, we enumerated all valid J(P)-enriched categories for
k = 2, 3 objects.

### k = 2 (results for all lattices in <1ms)

| |J(P)|| Candidates | Valid | Ratio | Poset P |
|------|----------|-------|-------|
| 2 | 4 | 4 | 100% | 1-element |
| 3 | 9 | 9 | 100% | 2-chain |
| 4 | 16 | 16 | 100% | 2-antichain, 3-chain+tail |
| 5 | 25 | 25 | 100% | 3-element with 1 relation |
| 6 | 36 | 36 | 100% | 3-element with 2 relations |
| 8 | 64 | 64 | 100% | 3-antichain |
| 9 | 81 | 81 | 100% | 4-element with 0–1 relations |
| 10 | 100 | 100 | 100% | 4-element partially ordered |
| 12 | 144 | 144 | 100% | 4-element with 2+ relations |
| 16 | 256 | 256 | 100% | 4-antichain |

For k = 2 the composition axiom is vacuous: with only two objects, no
composable triple involves a non-identity cell twice.  All  2D0 candidate
matrices pass.

### k = 3 (selected results)

| |J(P)|| Candidates | Valid | Time | Poset |
|------|-----------|-------|------|------|
| 2 | 64 | 29 | <1ms | 1-element (Two) |
| 3 | 729 | 192 | <1ms | 2-chain |
| 4 | 4096 | 730–841 | <1ms | 2-antichain, 3-chain |
| 5 | 15625 | 2063–2168 | <1ms | 4-element sparse |
| 6 | 46656 | 4854–5568 | 15–31s | 4-element, some ordering |
| 7 | 117649 | 10096–10525 | 47–63s | 4-element, more ordering |
| 8 | 262144 | 19763–24389 | 94–109s | 3-antichain, 4-element |
| 9 | 531441 | 36864–37440 | 188–219s | 4-element mostly ordered |
| 10 | 1M | 62872 | 328–391s | 4-element, 2 components |
| 12 | 3M | 161472 | ~1060s | 4-element largely ordered |
| 16 | 16.8M | 707281 | ~5920s | 4-antichain (Boolean) |

### Key findings

1. **The Two lattice (J(1)) is the ideal first layer.** It captures exactly
   the support-preorder information (which hom-sets are nonempty) at
   minimal cost: 64 candidates for k=3, <1ms.

2. **Larger up-set lattices are exponentially more expensive.**
   The candidate count grows as |J(P)|^(k²−k).  For the Boolean lattice
   on 4 elements (|J(P)|=16), k=3 requires checking 16.8M candidates.

3. **The composition-axiom filter ratio drops with lattice size.**
   For m=2, 45% of candidates pass; for m=16, only 4% pass.  This means
   the extra information from larger lattices comes at rapidly
   diminishing returns.

4. **The ideal pipeline is exactly what the code already does.**
   - Layer 1: enrich over Two → support preorder (fast, 0ms)
   - Layer 2: enrich over Cardinal → hom-count matrices (fast, 0ms)
   - Layer 3: full Set composition table (the expensive but necessary step)

   The up-set lattices J(P) for |P| > 1 are the wrong middle ground:
   they are combinatorially more expensive than Two but don't provide
   enough constraint to replace the Set layer.

## Bug fixes (May 2026)

### Level-shifting in skeleton canonical key

`connectedSkeletonCanonicalKey` was trying ALL q! class permutations to
find the minimum skeleton key.  This let distinct skeletons collide when
a permutation of one skeleton matched another skeleton's minimum key.
The consequence: categories with different component-to-class assignments
(e.g., C₂ at class 0 with C₃ at class 1 vs C₃ at 0 with C₂ at 1) were
deduplicated even though they are non-isomorphic.

**Fix:** restrict permutations to only swap classes with identical
component keys (`partitionByKey` + per-group permutations).  This
recovered 164 missing isomorphism classes at (9,2) (114 → 278).

### Undercounting in `smallExtraCauchyKeys` shortcut

The shortcut was handling excess ≤ 4, but when it returned `Just`, the
full skeleton-assembly pipeline was never called, masking gaps.  Also:
- The distribution list was missing multi-object components (parallel
  arrows).
- Object counts were computed as `length dist` (number of components)
  instead of `sum (fcObjectCount . snd)` (total objects in those
  components).

**Fix:** union shortcut results with the full pipeline.  Added parallel
arrow categories to the distribution lists.  Fixed object counting.

### Stale cache files

0-byte cache files from cancelled partial runs were being reused by
`cachedGeneratedKeys`, preventing fresh computations from running even
after underlying bugs were fixed.

**Fix:** delete 0-byte cache files before re-running.




