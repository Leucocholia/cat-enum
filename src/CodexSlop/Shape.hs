module CodexSlop.Shape
  ( SupportPreorder(..)
  , Shape(..)
  , biconnectedShapesFor
  , posetsFor
  , shapeFromHomMatrix
  , supportsFor
  , shapesFor
  , supportAt
  , homAt
  , blockAt
  , isConnectedShape
  ) where

import Data.List (permutations)
import qualified Data.Set as Set
import qualified Data.Vector as V

data SupportPreorder = SupportPreorder
  { supportObjectCount :: !Int
  , supportRelation :: !(V.Vector Bool)
  } deriving (Eq, Ord, Show)

data Shape = Shape
  { shapeObjectCount :: !Int
  , shapeMorphismCount :: !Int
  , shapeHom :: !(V.Vector Int)
  , shapeBlocks :: !(V.Vector [Int])
  , shapeSources :: !(V.Vector Int)
  , shapeTargets :: !(V.Vector Int)
  , shapeIdentities :: !(V.Vector Int)
  , shapeIsIdentity :: !(V.Vector Bool)
  } deriving (Eq, Show)

supportsFor :: Int -> Bool -> [SupportPreorder]
supportsFor k connectedOnly =
  if connectedOnly
    then connectedSupportCache !! k
    else supportCache !! k

supportCache :: [[SupportPreorder]]
supportCache =
  [ supportsForUncached k False
  | k <- [0 ..]
  ]

connectedSupportCache :: [[SupportPreorder]]
connectedSupportCache =
  [ supportsForUncached k True
  | k <- [0 ..]
  ]

supportsForUncached :: Int -> Bool -> [SupportPreorder]
supportsForUncached k connectedOnly =
  [ SupportPreorder k (V.fromList relation)
  | relation <- Set.toAscList canonicalRelations
  ]
  where
    canonicalRelations =
      Set.fromList
        [ canonicalRelation k relation
        | q <- [1 .. k]
        , classSizes <- positiveCompositions k q
        , quotient <- canonicalPosetRelations q
        , let relation = blowUpRelation quotient classSizes
        , not connectedOnly || connectedRelation k relation
        ]

shapesFor :: Int -> Maybe Int -> Bool -> [Shape]
shapesFor n objectFilter connectedOnly =
  [ shape
  | k <- maybe [1 .. n] (:[]) objectFilter
  , k >= 1
  , k <= n
  , extras <- compositions (n - k) (k * k)
  , let matrix = addDiagonalUnits k extras
  , supportTransitiveMatrix k matrix
  , canonicalMatrix k matrix == matrix
  , not connectedOnly || connectedMatrix k matrix
  , let shape = buildShape k n matrix
  ]

biconnectedShapesFor :: Int -> Maybe Int -> [Shape]
biconnectedShapesFor n objectFilter =
  [ shape
  | k <- maybe [1 .. floor (sqrt (fromIntegral n :: Double))] (:[]) objectFilter
  , k >= 1
  , k * k <= n
  , extras <- compositions (n - k * k) (k * k)
  , let matrix = map (+ 1) extras
  , canonicalMatrix k matrix == matrix
      , let shape = buildShape k n matrix
  ]

posetsFor :: Int -> [SupportPreorder]
posetsFor q =
  [ SupportPreorder q (V.fromList relation)
  | relation <- canonicalPosetRelations q
  ]

shapeFromHomMatrix :: Int -> [Int] -> Maybe Shape
shapeFromHomMatrix k matrix
  | k < 1 = Nothing
  | length matrix /= k * k = Nothing
  | any (< 0) matrix = Nothing
  | any (\i -> matrix !! (i * k + i) < 1) [0 .. k - 1] = Nothing
  | otherwise = Just (buildShape k (sum matrix) matrix)

supportAt :: SupportPreorder -> Int -> Int -> Bool
supportAt support i j = supportRelation support V.! (i * supportObjectCount support + j)

homAt :: Shape -> Int -> Int -> Int
homAt shape i j = shapeHom shape V.! (i * shapeObjectCount shape + j)

blockAt :: Shape -> Int -> Int -> [Int]
blockAt shape i j = shapeBlocks shape V.! (i * shapeObjectCount shape + j)

isConnectedShape :: Shape -> Bool
isConnectedShape shape
  | k <= 1 = True
  | otherwise = length (reachable [0] []) == k
  where
    k = shapeObjectCount shape
    neighbors i =
      [ j
      | j <- [0 .. k - 1]
      , j /= i
      , homAt shape i j > 0 || homAt shape j i > 0
      ]
    reachable [] seen = seen
    reachable (x:xs) seen
      | x `elem` seen = reachable xs seen
      | otherwise = reachable (neighbors x ++ xs) (x : seen)

buildShape :: Int -> Int -> [Int] -> Shape
buildShape k n matrix =
  Shape
    { shapeObjectCount = k
    , shapeMorphismCount = n
    , shapeHom = V.fromList matrix
    , shapeBlocks = V.fromList blocks
    , shapeSources = V.fromList sources
    , shapeTargets = V.fromList targets
    , shapeIdentities = V.fromList identities
    , shapeIsIdentity = V.fromList [m `elem` identities | m <- [0 .. n - 1]]
    }
  where
    blockSpecs =
      [ (i, j, matrix !! (i * k + j))
      | i <- [0 .. k - 1]
      , j <- [0 .. k - 1]
      ]

    (blocks, sources, targets, identities, _) =
      foldl assignBlock ([], [], [], replicate k (-1), 0) blockSpecs

    assignBlock (bs, ss, ts, ids, next) (i, j, size) =
      let morphs = [next .. next + size - 1]
          ids' = if i == j && size > 0 then replaceAt i next ids else ids
      in
        ( bs ++ [morphs]
        , ss ++ replicate size i
        , ts ++ replicate size j
        , ids'
        , next + size
        )

replaceAt :: Int -> a -> [a] -> [a]
replaceAt index value xs =
  take index xs ++ [value] ++ drop (index + 1) xs

addDiagonalUnits :: Int -> [Int] -> [Int]
addDiagonalUnits k extras =
  [ extra + if i == j then 1 else 0
  | i <- [0 .. k - 1]
  , j <- [0 .. k - 1]
  , let extra = extras !! (i * k + j)
  ]

supportTransitiveMatrix :: Int -> [Int] -> Bool
supportTransitiveMatrix k matrix =
  and
    [ matrix !! (i * k + l) > 0
    | i <- [0 .. k - 1]
    , j <- [0 .. k - 1]
    , l <- [0 .. k - 1]
    , matrix !! (i * k + j) > 0
    , matrix !! (j * k + l) > 0
    ]

connectedMatrix :: Int -> [Int] -> Bool
connectedMatrix k matrix
  | k <= 1 = True
  | otherwise = length (reachable [0] []) == k
  where
    neighbors i =
      [ j
      | j <- [0 .. k - 1]
      , j /= i
      , matrix !! (i * k + j) > 0 || matrix !! (j * k + i) > 0
      ]
    reachable [] seen = seen
    reachable (x:xs) seen
      | x `elem` seen = reachable xs seen
      | otherwise = reachable (neighbors x ++ xs) (x : seen)

canonicalMatrix :: Int -> [Int] -> [Int]
canonicalMatrix k matrix =
  minimum [permuteMatrix p | p <- permutations [0 .. k - 1]]
  where
    permuteMatrix p =
      [ matrix !! ((p !! i) * k + (p !! j))
      | i <- [0 .. k - 1]
      , j <- [0 .. k - 1]
      ]

compositions :: Int -> Int -> [[Int]]
compositions total parts
  | parts <= 0 = if total == 0 then [[]] else []
  | total < 0 = []
  | parts == 1 = [[total]]
  | otherwise =
      [ x : xs
      | x <- [0 .. total]
      , xs <- compositions (total - x) (parts - 1)
      ]

positiveCompositions :: Int -> Int -> [[Int]]
positiveCompositions total parts =
  map (map (+ 1)) (compositions (total - parts) parts)

canonicalPosetRelations :: Int -> [[Bool]]
canonicalPosetRelations q = canonicalPosetCache !! q

canonicalPosetCache :: [[[Bool]]]
canonicalPosetCache =
  [ canonicalPosetRelationsUncached q
  | q <- [0 ..]
  ]

canonicalPosetRelationsUncached :: Int -> [[Bool]]
canonicalPosetRelationsUncached q =
  Set.toAscList $
    Set.fromList
      [ canonicalRelation q relation
      | relation <- labelledPosetRelations q
      ]

labelledPosetRelations :: Int -> [[Bool]]
labelledPosetRelations q = labelledPosetCache !! q

labelledPosetCache :: [[[Bool]]]
labelledPosetCache =
  [ labelledPosetRelationsUncached q
  | q <- [0 ..]
  ]

labelledPosetRelationsUncached :: Int -> [[Bool]]
labelledPosetRelationsUncached q
  | q <= 0 = [[]]
  | q == 1 = [[True]]
  | otherwise =
      [ extendRelation old lower upper
      | old <- labelledPosetRelations (q - 1)
      , lower <- subsets [0 .. q - 2]
      , isDownSet old lower
      , upper <- subsets [0 .. q - 2]
      , isUpSet old upper
      , null (lower `intersectList` upper)
      , all (\l -> all (relationAt old (q - 1) l) upper) lower
      ]

extendRelation :: [Bool] -> [Int] -> [Int] -> [Bool]
extendRelation old lower upper =
  [ cell i j
  | i <- [0 .. q - 1]
  , j <- [0 .. q - 1]
  ]
  where
    q = relationSize old + 1
    new = q - 1
    cell i j
      | i < new && j < new = relationAt old new i j
      | i == new && j == new = True
      | j == new = i `elem` lower
      | i == new = j `elem` upper
      | otherwise = False

isDownSet :: [Bool] -> [Int] -> Bool
isDownSet relation xs =
  all
    ( \x ->
        all
          ( \y ->
              not (relationAt relation k y x) || y `elem` xs
          )
          [0 .. k - 1]
    )
    xs
  where
    k = relationSize relation

isUpSet :: [Bool] -> [Int] -> Bool
isUpSet relation xs =
  all
    ( \x ->
        all
          ( \y ->
              not (relationAt relation k x y) || y `elem` xs
          )
          [0 .. k - 1]
    )
    xs
  where
    k = relationSize relation

blowUpRelation :: [Bool] -> [Int] -> [Bool]
blowUpRelation quotient classSizes =
  [ relationAt quotient q (classes !! i) (classes !! j)
  | i <- [0 .. k - 1]
  , j <- [0 .. k - 1]
  ]
  where
    q = length classSizes
    classes = concat [replicate size classId | (classId, size) <- zip [0 ..] classSizes]
    k = length classes

canonicalRelation :: Int -> [Bool] -> [Bool]
canonicalRelation k relation =
  minimum [permuteRelation p | p <- permutations [0 .. k - 1]]
  where
    permuteRelation p =
      [ relationAt relation k (p !! i) (p !! j)
      | i <- [0 .. k - 1]
      , j <- [0 .. k - 1]
      ]

connectedRelation :: Int -> [Bool] -> Bool
connectedRelation k relation
  | k <= 1 = True
  | otherwise = length (reachable [0] []) == k
  where
    neighbors i =
      [ j
      | j <- [0 .. k - 1]
      , j /= i
      , relationAt relation k i j || relationAt relation k j i
      ]
    reachable [] seen = seen
    reachable (x:xs) seen
      | x `elem` seen = reachable xs seen
      | otherwise = reachable (neighbors x ++ xs) (x : seen)

relationAt :: [Bool] -> Int -> Int -> Int -> Bool
relationAt relation k i j = relation !! (i * k + j)

relationSize :: [Bool] -> Int
relationSize relation = floor (sqrt (fromIntegral (length relation) :: Double))

subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x:xs) =
  let rest = subsets xs
  in rest ++ map (x :) rest

intersectList :: Eq a => [a] -> [a] -> [a]
intersectList xs ys = [x | x <- xs, x `elem` ys]
