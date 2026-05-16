# cat-enum

Exact enumeration and classification tools for **finite categories**.

Counts finite categories by total morphism count, using the arrows-only
representation.  Supports three quotient relations (equivalence, isomorphism,
equality) and several derived computations (copresheaves, profunctors,
thin-category classification).

## Build & test

Requires [Cabal](https://www.haskell.org/cabal/) ≥ 3.0 and GHC ≥ 9.4.

```bash
cabal build
cabal run cat-enum-test   # 41 tests
```

## Data model

A finite category is stored as an **arrows-only** representation:

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

This follows Cruttwell/Leblanc's arrows-only view and the
[SmallCategories](https://smallcats.info/about) representation.
Composition is written left-to-right: `compose(f, g)` = `f ; g`.

## CLI reference

```
cat-enum COMMAND [OPTIONS]
```

### `count` — Enumerate categories by morphism count

```
cat-enum count --max-morphisms N
                 [--objects K]
                 [--connected-only]
                 [--cauchy-complete]
                 [--write-reps DIR]
                 [--up-to MODE]
```

Enumerates **all** finite categories (or all Cauchy-complete categories) with
up to `N` morphisms, using the shape-based exact search.  Breaks down results
by object count `k`.

### `generate` — Fast generation via component decomposition

```
cat-enum generate --morphisms N
                    [--objects K]
                    [--cauchy-complete]
                    [--write-reps DIR]
                    [--up-to MODE]
```

Generates categories by decomposing into biconnected components and
assembling via quotient-poset skeletons.  Much faster than `count` for
larger `N` thanks to cached building blocks and algorithmic shortcuts.

Results are cached under `.cat-enum-cache/v4/generated/`.  First run
builds caches; subsequent runs read them directly.

### `verify` — Validate representative key files

```
cat-enum verify FILE_OR_DIR [--cauchy-complete]
```

Checks that each line in the given file(s) is a well-formed canonical
category key.  Verifies category axioms, canonicality, and (optional)
Cauchy completeness.

### `biconnected` — Enumerate biconnected categories

```
cat-enum biconnected --max-morphisms N [--objects K]
                       [--cauchy-complete] [--write-reps DIR]
```

Every hom-set nonempty (`∀ a,b, Hom(a,b) ≠ ∅`).  Cached under
`.cat-enum-cache/v1/biconnected/`.

### `copresheaves` — Count finite Set-valued copresheaves

```
cat-enum copresheaves --morphisms N --max-elements M
                        [--objects K] [--connected-only]
                        [--all-categories]
```

Counts bounded finite copresheaves `F : C → Set` with `≤ M` total elements
across all fibers, summed over all base categories `C` of the given size.

### `profunctors` — Count finite profunctors

```
cat-enum profunctors --left KEY_OR_FILE --right KEY_OR_FILE
                       --max-elements N [--profile CSV]
```

Counts finite profunctors `P : Aᵒᵖ × B → Set` between two fixed categories.
The `--profile` option gives a single row-major fiber-size profile to count;
without it, all profiles up to `N` total elements are counted.  Results are
cached under `.cat-enum-cache/v1/profunctor-counts/`.

### `thin` — Classify digraph6 relations

```
cat-enum thin DIGRAPH6_FILE
```

For each digraph6-encoded directed graph in the file, reports whether the
relation is reflexive, transitive, antisymmetric — and therefore whether it
forms a preorder or a poset.

### Quotient modes (`--up-to`)

| Mode | Key function | Semantics |
|------|-------------|-----------|
| `equivalence` (default for Cauchy) | `equivalenceKey` | Skeletal subcategory (one object per iso class), then canonical relabelling |
| `isomorphism` (default for general) | `canonicalKey` | Minimal key under object + morphism relabelling |
| `equality` | `categoryKey` | Key = raw serialization; object labels matter, morphism indices within each hom-set do not |

## Algorithms

### Shape-based search (`CodexSlop.Search`, `CodexSlop.Shape`)

The direct enumeration pipeline:

1. **Generate shapes**.  For each object count `k`, each hom-count matrix
   `H : k×k → ℕ` with `sum(H) = n`, `H[i][i] ≥ 1`, and support-transitivity
   (`H[i][j] > 0 ∧ H[j][ℓ] > 0 ⇒ H[i][ℓ] > 0`).  Matrices are canonicalized
   (reduced under object permutation) to avoid redundant work.

2. **Search composition tables**.  For each shape, fill the partial
   composition table using backtracking with constraint propagation.
   Identity cells are pre-filled.  The solver picks the cell with the
   smallest domain and explores each candidate value, propagating
   associativity constraints forward.  Cauchy-completeness is checked
   during search via `partialCauchyViable` (no non-identity idempotents
   in the partial table).

3. **Quotient**.  Each valid table is relabelled to a canonical key
   (object + morphism permutation) or an equivalence key (skeletal
   subcategory + canonical relabelling).

### Decomposition-based generation (`CodexSlop.Generate`)

The fast generation pipeline decomposes categories into **biconnected
components** (categories where every hom-set is nonempty) connected by
**profunctor edges** (functors `Aᵒᵖ × B → Set`).

1. **Biconnected components** are enumerated by the shape-search solver
   and cached by `(morphisms, objects, cauchy)`.

2. **Skeletons** are built from a support preorder (a poset of biconnected
   component classes), a multiset of biconnected component keys, and a
   hom-count matrix generated from the poset relations and component sizes.

3. **Shortcuts** for small extra morphisms:
   - `excess = n − k ≤ 2`: direct list of connected building blocks
     (terminal objects, C₂, C₃, parallel arrows, forks, etc.)
   - `excess = 3, 4`: assembled from cached connected blocks
   - One-way group-terminal gluings: enumerated as finite `(G, H)`-bisets
     using subgroup conjugacy classes of `G × Hᵒᵖ`

### Group construction (`CodexSlop.Group`)

One-object Cauchy-complete categories are finite groups.  The module
constructs groups structurally (avoiding generic table search):

- **Abelian groups**: prime factorization + integer partitions of each
  exponent → product of cyclic groups
- **Small orders (≤15)**: abelian + dihedral, dicyclic, A₄
- **p³ orders**: 3 abelian + Heisenberg + nonabelian semidirect product
- **pq orders**: cyclic or semidirect via unit group of ℤ/qℤ
- **Fallback**: Latin-square + associativity search for unsupported orders

### Finite profunctors (`CodexSlop.Profunctor`)

Counts profunctors `P : Aᵒᵖ × B → Set` with fixed finite fibers using a
backtracking solver over left-action (morphisms of `A`) and right-action
(morphisms of `B`) variables, enforcing composition and the middle
interchange law.

One-object group profunctors use an algebraic shortcut: enumerate transitive
coset actions of `G × Hᵒᵖ` and combine as orbit multisets.

### Copresheaves (`CodexSlop.Copresheaf`)

Counts bounded Set-valued copresheaves over a fixed base category.
Factors over connected components via convolution of generating functions.

### Equality (labelled-object) mode (`--up-to equality`)

Under equality semantics, object labels matter but morphism labels within
each hom-set do not.  The `generate` pipeline computes equality counts from
the isomorphism cache:

```
isomorphism cache → parseCategoryKey → equalityCount per category → sum
```

The `equalityCount` function (in `CodexSlop.Canonical`) generates all `k!`
object-permuted FNV-1a hashes of the composition table and deduplicates by
hash — no full key strings are produced unless `--write-reps` is passed.
This keeps the common case (just the count) fast while supporting full key
output for downstream tooling.

## Module architecture

| Module | Responsibility |
|--------|---------------|
| `CodexSlop.Category` | `FiniteCategory` data type, validation, serialization (`categoryKey`/`parseCategoryKey`) |
| `CodexSlop.Shape` | Hom-count matrices, support preorders, shape construction and canonicalization |
| `CodexSlop.Search` | Backtracking composition-table solver with constraint propagation |
| `CodexSlop.Canonical` | Canonical/equivalence/equality key functions, `allEqualityKeys`, `equalityCount` |
| `CodexSlop.Decompose` | Support decomposition, connected components, disjoint union construction |
| `CodexSlop.Biconnected` | Biconnected component enumeration with disk caching |
| `CodexSlop.Generate` | Decomposition-based category generation with skeleton assembly |
| `CodexSlop.Group` | Group construction (abelian, dihedral, p³, pq, Latin-square fallback) |
| `CodexSlop.Profunctor` | Finite profunctor counting with action-variable solver |
| `CodexSlop.Copresheaf` | Bounded copresheaf counting with connected-component convolution |
| `CodexSlop.Thin` | digraph6 relation classification (reflexive, transitive, antisymmetric) |
| `CodexSlop.CspSearch` | Experimental CSP backend using the `csp` library |
| `CodexSlop.CLI` | `optparse-applicative` CLI dispatch |
| `Main` | `runCLI` entry point |

## Known counts

All finite categories up to strict isomorphism, by total morphism count:

| n | Count |
|---|-------|
| 1 | 1 |
| 2 | 3 |
| 3 | 11 |
| 4 | 55 |
| 5 | 329 |
| 6 | 2858 |
| 7 | 36440 |

Cauchy-complete categories up to categorical equivalence (default for
`generate --cauchy-complete`):

```
cat-enum generate --morphisms 7 --cauchy-complete --up-to equivalence
7 morphisms: 6520 generated Cauchy-complete categories up to equivalence
  1 objects: 2
  2 objects: 151
  3 objects: 779
  4 objects: 1971
  5 objects: 2192
  6 objects: 1142
  7 objects: 283
```

## References

- Geoff Cruttwell, [Counting finite categories](https://www.reluctantm.com/gcruttw/publications/ams2014CruttwellCountingFiniteCats.pdf) (AMS 2014)
- [SmallCategories](https://smallcats.info/about) database and [source](https://github.com/diracdeltafunk/SmallCategories)
- nauty-traces / [nauty-parser](https://hackage.haskell.org/package/nauty-parser) for digraph6 I/O
- OEIS [A384134](https://oeis.org/A384134) (Cauchy-complete finite categories)
