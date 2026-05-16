module CodexSlop.Enrichment
  ( EnrichmentLattice(..)
  , EnrichedCategory(..)
  , ecHom
  , Two(..)
  , Cardinal(..)
  , validEnrichment
  , enumerateTwo
  , enumerateCardinal
  , refine
  , composeEnrichments
  , canonicalEnrichment
  ) where

import qualified CodexSlop.Shape as Shape

import Data.Bits (shiftL, (.|.))
import Data.Function (on)
import Data.List (permutations, sortBy)
import qualified Data.Vector as V
import Data.Word (Word64)

------------------------------------------------------------------------------
-- Lattice typeclass

-- | A monoidal poset (bounded distributive lattice) used as the enriching
-- base.  For a category enriched over @a@, each hom-set is assigned a value
-- @Hom(x,y) :: a@ satisfying:
--
--   @⊤ ≤ Hom(x,x)@                       (identity)
--   @Hom(y,z) ∧ Hom(x,y) ≤ Hom(x,z)@    (composition)
--
-- /Theorem/ (colimit–limit preservation).  Let @U : Preord → Set@ be the
-- forgetful functor.  Write @U(P)-Cat@ for the category of categories
-- enriched over the underlying set @U(P)@ with its preorder monoidal
-- structure (where the monoidal product is the meet of @P@).  Then the
-- functor
--
-- \[
-- U(-)\text{-Cat} : \mathbf{Preord}^{op} \longrightarrow \mathbf{CAT}/\mathbf{Set}
-- \]
--
-- sends /all weighted colimits/ in the locally-posetal 2-category
-- @Preord@ to weighted limits in @CAT/Set@.
--
-- /Consequences for this module./
--
-- 1. **Coproducts become pullbacks over Set.**  
--    If @P+Q@ is the coproduct (disjoint union) of two preorders, then
--
--    \[
--    U(P+Q)\text{-Cat} \cong U(P)\text{-Cat} \times_{\mathbf{Set}} U(Q)\text{-Cat}.
--    \]
--
--    This justifies factoring the support-preorder enumeration over
--    connected components: a category whose support is a disjoint union
--    is determined by its restrictions to each component, pinned
--    together by a common object set.  The existing support-blowing
--    algorithm (@supportsForUncached@ in "Shape.hs") already exploits
--    this by decomposing a preorder into a quotient poset and a
--    collection of equivalence classes (the "blow-up" factorisation).
--
-- 2. **Profunctor composition as pullback.**  
--    The decomposition of a category into biconnected components
--    connected by profunctor edges (the @generate@ pipeline) is the
--    colimit–limit dual of this theorem: assembling components along
--    profunctors corresponds to a weighted limit in @CAT/Set@.
--
-- 3. **Template for new lattices.**  
--    Any enrichment lattice @L@ that arises as @U(P)@ for some
--    preorder @P@ inherits this decomposition property.  The
--    enumeration can be factored over the poset of support preorders
--    (Layer 1) and then refined to hom-counts (Layer 2) and
--    composition tables (Layer 3), each step respecting the
--    colimit–limit duality.
--
class Eq a => EnrichmentLattice a where
  top  :: a
  meet :: a -> a -> a
  leq  :: a -> a -> Bool

------------------------------------------------------------------------------
-- Enriched category type

-- | A category enriched over lattice @a@.
-- Hom-objects are stored as a flat @k×k@ vector in row-major order.
data EnrichedCategory a = EnrichedCategory
  { ecObjectCount :: !Int
  , ecHomMatrix   :: !(V.Vector a)
  } deriving (Eq, Ord, Show)

ecHom :: EnrichedCategory a -> Int -> Int -> a
ecHom cat i j = ecHomMatrix cat V.! (i * ecObjectCount cat + j)

------------------------------------------------------------------------------
-- Two-element lattice (support preorders)

data Two = Zero | One deriving (Eq, Ord, Show)

instance EnrichmentLattice Two where
  top  = One
  meet Zero _ = Zero
  meet One  x = x
  leq  Zero _ = True
  leq  One  x = x == One

-- | All labelled support preorders for @k@ objects.
--
-- Uses the existing fast poset+blowup algorithm from
-- 'Shape.supportsFor', then expands each canonical support into all
-- @k!@ object-permuted versions.  Dedups via 'Word64' bitmask.
--
-- Cold cache (first call) is slow because 'Shape.supportsFor' builds
-- the labelled-poset enumeration cache for all sizes up to k;
-- subsequent calls are fast.
enumerateTwo :: Int -> [EnrichedCategory Two]
enumerateTwo k = map snd $ dedupFst $ sortBy (compare `on` fst)
  [ (relBits k rel, EnrichedCategory k (V.map (\b -> if b then One else Zero) rel))
  | s <- Shape.supportsFor k False
  , p <- permutations [0 .. k - 1]
  , let rel = permuteRelation k (Shape.supportRelation s) p
  ]

relBits :: Int -> V.Vector Bool -> Word64
relBits k rel =
  foldl (\acc i -> if rel V.! i then acc .|. (1 `shiftL` i) else acc) 0 [0 .. k * k - 1]

permuteRelation :: Int -> V.Vector Bool -> [Int] -> V.Vector Bool
permuteRelation k rel perm =
  V.fromList
    [ rel V.! (perm !! i * k + perm !! j)
    | i <- [0 .. k - 1]
    , j <- [0 .. k - 1]
    ]

dedupFst :: Eq a => [(a, b)] -> [(a, b)]
dedupFst [] = []
dedupFst ((k, v) : xs) = (k, v) : dedupFst (dropWhile (\(k', _) -> k' == k) xs)

------------------------------------------------------------------------------
-- Cardinal lattice (hom-count matrices)

newtype Cardinal = Cardinal { unCardinal :: Int }
  deriving (Eq, Ord, Show)

instance EnrichmentLattice Cardinal where
  top = Cardinal maxBound
  meet (Cardinal x) (Cardinal y) = Cardinal (min x y)
  leq  (Cardinal x) (Cardinal y) = x <= y

-- | All hom-count matrices with @k@ objects and @n@ total morphisms.
-- Each diagonal entry is at least 1 (identity).  The remaining @n - k@
-- morphisms are distributed across all @k²@ hom-cells via weak compositions.
-- Filters by the Cardinal-enrichment composition axiom
-- (@min(H[j][l], H[i][j]) ≤ H[i][l]@), which is typically always satisfied.
enumerateCardinal :: Int -> Int -> [EnrichedCategory Cardinal]
enumerateCardinal n k
  | k <= 0 || n < k = []
  | otherwise       = filter validEnrichment
      [ EnrichedCategory k (V.fromList (map Cardinal vals))
      | extras <- compositions (n - k) (k * k)
      , let vals = addDiagonalUnits k extras
      ]
  where
    addDiagonalUnits k' ws =
      [ w + if i == j then 1 else 0
      | i <- [0 .. k' - 1]
      , j <- [0 .. k' - 1]
      , let w = ws !! (i * k' + j)
      ]

------------------------------------------------------------------------------
-- Generic validity: the composition axiom only
-- (identity is enforced by each concrete enumeration separately)

validEnrichment :: EnrichmentLattice a => EnrichedCategory a -> Bool
validEnrichment ec =
  and [ (ecHom ec j l `meet` ecHom ec i j) `leq` ecHom ec i l
      | i <- [0 .. k - 1]
      , j <- [0 .. k - 1]
      , l <- [0 .. k - 1]
      ]
  where k = ecObjectCount ec

------------------------------------------------------------------------------
-- Layer composition

-- | Refine a support preorder into all compatible hom-count matrices
-- with @n@ total morphisms.
refine :: EnrichedCategory Two -> Int -> [EnrichedCategory Cardinal]
refine support n =
  filter (composeEnrichments support) (enumerateCardinal n k)
  where k = ecObjectCount support

-- | Check that hom-counts respect the support:
--   @H[i][j] > 0  iff  S[i][j] = One@
composeEnrichments :: EnrichedCategory Two -> EnrichedCategory Cardinal -> Bool
composeEnrichments s c =
  ecObjectCount s == ecObjectCount c
  && and
    [ (ecHom s i j == One) == (unCardinal (ecHom c i j) > 0)
    | i <- [0 .. k - 1]
    , j <- [0 .. k - 1]
    ]
  where k = ecObjectCount s

------------------------------------------------------------------------------
-- Canonicalization under object permutation

canonicalEnrichment :: (EnrichmentLattice a, Ord a) => EnrichedCategory a -> EnrichedCategory a
canonicalEnrichment ec =
  minimumBy (\a b -> compare (ecHomMatrix a) (ecHomMatrix b))
    [ permuteEnrichment ec p
    | p <- permutations [0 .. ecObjectCount ec - 1]
    ]

permuteEnrichment :: EnrichmentLattice a => EnrichedCategory a -> [Int] -> EnrichedCategory a
permuteEnrichment ec perm =
  EnrichedCategory
    { ecObjectCount = k
    , ecHomMatrix = V.fromList
        [ ecHom ec (perm !! i) (perm !! j)
        | i <- [0 .. k - 1]
        , j <- [0 .. k - 1]
        ]
    }
  where k = ecObjectCount ec

------------------------------------------------------------------------------
-- Internal helpers

compositions :: Int -> Int -> [[Int]]
compositions total parts
  | parts <= 0 = if total == 0 then [[]] else []
  | total < 0  = []
  | parts == 1 = [[total]]
  | otherwise  =
      [ x : xs
      | x <- [0 .. total]
      , xs <- compositions (total - x) (parts - 1)
      ]

minimumBy :: (a -> a -> Ordering) -> [a] -> a
minimumBy cmp (x:xs) = go x xs
  where
    go best []     = best
    go best (y:ys) = if cmp y best == LT then go y ys else go best ys
minimumBy _ [] = error "minimumBy: empty list"
