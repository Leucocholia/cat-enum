# cat-enum

Exact enumeration and classification tools for **finite categories**.

Counts finite categories by total morphism count, using the arrows-only
representation.  Supports three quotient relations (equivalence, isomorphism,
equality) and several derived computations (copresheaves, profunctors,
thin-category classification, lattice-enriched categories).

## Build & test

Requires [Cabal](https://www.haskell.org/cabal/) ≥ 3.0 and GHC ≥ 9.4.

```bash
cabal build
cabal run cat-enum-test   # 47 tests
```

Benchmarks:

```bash
cabal run bench-enrich    # layer-by-layer timing
cabal run bench-upset     # up-set lattice enrichment benchmark
cabal run bench-center    # center/trace classification of biconnected components
```

## Data model

```haskell
FiniteCategory
  { fcMorphismCount :: Int      -- n
  , fcObjectCount   :: Int      -- k
  , fcSources       :: Vector Int  -- src(i) ∈ {0..k-1}
  , fcTargets       :: Vector Int  -- tgt(i) ∈ {0..k-1}
  , fcIdentities    :: Vector Int  -- id_j = index of identity at object j
  , fcCompose       :: Vector Int  -- flat n×n table, -1 for non-composable pairs
  }
```

(Cruttwell/Leblanc arrows-only view, left-to-right composition `f ; g`.)

## CLI reference

```
cat-enum COMMAND [OPTIONS]
```

### `count` — Enumerate categories by morphism count

```
cat-enum count --max-morphisms N [--objects K] [--connected-only]
               [--cauchy-complete] [--write-reps DIR] [--up-to MODE]
```

Shape-based exact search.  Enumerates all hom-count matrices and fills
composition tables via backtracking with associativity propagation.
Slow but exhaustive — useful as a ground-truth reference for small `N`.

### `generate` — Fast generation via component decomposition

```
cat-enum generate --morphisms N [--objects K] [--cauchy-complete]
                  [--write-reps DIR] [--up-to MODE]
```

Decomposes categories into biconnected components and assembles via
quotient-poset skeletons.  Much faster than `count` for larger `N`.
Results are cached under `.cat-enum-cache/v4/generated/`; first run
builds caches, subsequent runs read them directly.

The equality mode (`--up-to equality`) computes labelled-object counts
using an **analytic formula** (`k! / |Aut|` via object-class partitioning),
avoiding the O(k! × n²) hash brute-force.

The `--dual` flag further quotients by identifying a category with its
arrow-reversed opposite (C ≅ C^op).  This can be combined with any
`--up-to` mode.  For example:

```bash
cat-enum generate --morphisms 9 --cauchy-complete --up-to isomorphism --dual
```

### `verify`, `biconnected`, `copresheaves`, `profunctors`, `thin`

See `cat-enum --help` for the full subcommand reference.

### Quotient modes (`--up-to`)

| Mode | Key function | Semantics |
|------|-------------|-----------|
| `equivalence` (default for Cauchy) | `equivalenceKey` | Skeletal subcategory (one object per iso class), then canonical relabelling |
| `isomorphism` (default for general) | `canonicalKey` | Minimal key under object + morphism relabelling |
| `equality` | `categoryKey` | Object labels matter; morphism indices within each hom-set do not |

## Architecture

| Module | Responsibility |
|--------|---------------|
| `CodexSlop.Category` | `FiniteCategory` data type, validation, serialization |
| `CodexSlop.Shape` | Hom-count matrices, support preorders, shape construction (VU-optimized) |
| `CodexSlop.Search` | Backtracking composition-table solver with constraint propagation |
| `CodexSlop.Canonical` | Canonical/equivalence/equality key functions, `allEqualityKeys`, `equalityCount` |
| `CodexSlop.Enrichment` | `EnrichmentLattice` typeclass, `Two`/`Cardinal` instances, `enumerateTwo`/`enumerateCardinal`/`refine` |
| `CodexSlop.Decompose` | Support decomposition, connected components, disjoint union |
| `CodexSlop.Biconnected` | Biconnected component enumeration with disk caching |
| `CodexSlop.Generate` | Decomposition-based generation with skeleton assembly |
| `CodexSlop.Group` | Group construction (abelian, dihedral, p³, pq, Latin-square fallback) |
| `CodexSlop.Profunctor` | Finite profunctor counting |
| `CodexSlop.Copresheaf` | Bounded copresheaf counting |
| `CodexSlop.Thin` | digraph6 relation classification |
| `CodexSlop.CspSearch` | Experimental CSP backend using the `csp` library |
| `CodexSlop.CLI` | `optparse-applicative` CLI dispatch |

## Algorithms

### Shape-based search

1. **Generate shapes** — for each object count `k`, each hom-count matrix
   `H : k×k → ℕ` with `sum(H) = n`, `H[i][i] ≥ 1`, and support-transitivity.
2. **Search composition tables** — backtracking with constraint propagation,
   picking the cell with smallest domain.  Cauchy-completeness checked via
   `partialCauchyViable`.
3. **Quotient** — each valid table gets a canonical, equivalence, or
   equality key.

### Decomposition-based generation

Categories are decomposed into **biconnected components** (every hom-set
nonempty) connected by profunctor edges.  Skeletons are assembled from a
support preorder, a multiset of component keys, and a hom-count matrix
generated from poset relations.

The skeleton canonical key (`skeletonCanonicalKey`) correctly handles
**level-shifting**: only classes with identical component keys are
permuted when computing the canonical form, preventing different
component-to-class assignments from colliding.

### Equality mode (`--up-to equality`)

Equality counts are computed analytically from the automorphism group
under object permutation:

```
objectClasses  →  partition objects by hom-count profile
|Aut|  =  product over classes of |class|!
count  =  k! / |Aut|
```

This is O(k²) per isomorphism class instead of O(k! × n²).

### Lattice enrichment (`CodexSlop.Enrichment`)

The `EnrichmentLattice` typeclass formalises enrichment over a bounded
distributive lattice:

```haskell
class Eq a => EnrichmentLattice a where
  top  :: a
  meet :: a -> a -> a
  leq  :: a -> a -> Bool
```

Instances:
- **`Two`** — the two-element lattice `{0, 1}` with `meet = min`.  Enrichment
  over `Two` gives support preorders.  Enumeration via `enumerateTwo`.
- **`Cardinal`** — `ℕ` with `meet = min`.  Enrichment over `Cardinal` gives
  hom-count matrices.  Enumeration via `enumerateCardinal`.

The `refine` function bridges layers: given a `Two`-enriched category and
a total morphism count, list all compatible `Cardinal`-enriched categories.

A **colimit–limit theorem** (documented in the module) shows that
`U(-)-Cat : Preord^op → CAT/Set` sends all weighted colimits to weighted
limits, justifying the decomposition pipeline.

## Known counts

Cauchy-complete categories up to **strict isomorphism**:

| n | Count | OEIS match |
|---|-------|------------|
| 1 | 1 | |
| 2 | 2 | |
| 3 | 4 | |
| 4 | 11 | |
| 5 | 25 | |
| 6 | 63 | |
| 7 | 163 | |
| 8 | 451 | |
| 9 | 1312 | 2+278+458+371+151+39+10+2+1 matches strict-isomorphism row |
                                                                                                                
OEIS A384134 lists 457 at (9,3) instead of 458.  The missing class is a
genuine edge case: two categories with hom-count matrices

```
[1 1 2]   and   [1 2 2]
[1 1 2]         [0 1 1]  
[0 0 1]         [0 1 1]
```

that are equivalent (same two-object skeleton) but not isomorphic
(different object-hom multisets: {(4,2),(4,2),(1,5)} vs
{(5,1),(2,4),(2,4)}).  They are not formal duals either (see --dual
flag).  Our count of 458 is the correct strict-isomorphism count; the
OEIS likely uses a coarser convention or has a 1-entry error.
| 10 | 3359 | |
| 11 | 9309 | |

```bash
cat-enum generate --morphisms 9 --cauchy-complete --up-to isomorphism
```

Cauchy-complete categories up to **categorical equivalence**:

```bash
cat-enum generate --morphisms 9 --cauchy-complete --up-to equivalence
9 morphisms: 1121 generated Cauchy-complete categories up to equivalence
  1 objects: 2
  2 objects: 278
  3 objects: 457
  4 objects: 370
  5 objects: 6
  6 objects: 4
  7 objects: 2
  8 objects: 1
  9 objects: 1
```

## References

- Geoff Cruttwell, [Counting finite categories](https://www.reluctantm.com/gcruttw/publications/ams2014CruttwellCountingFiniteCats.pdf)
- [SmallCategories](https://smallcats.info/about) database and [source](https://github.com/diracdeltafunk/SmallCategories)
- nauty-traces / [nauty-parser](https://hackage.haskell.org/package/nauty-parser) (digraph6 I/O)
- OEIS [A384134](https://oeis.org/A384134) (Cauchy-complete finite categories)
