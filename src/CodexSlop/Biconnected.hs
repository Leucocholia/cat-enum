module CodexSlop.Biconnected
  ( biconnectedCanonicalCategories
  , biconnectedCanonicalCategoriesCached
  , biconnectedCanonicalKeys
  , biconnectedCanonicalKeysCached
  ) where

import CodexSlop.Canonical (canonicalKey)
import CodexSlop.Category
import CodexSlop.Group
import CodexSlop.Search
import CodexSlop.Shape

import qualified Data.Set as Set
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((</>))

biconnectedCanonicalCategories :: Int -> Maybe Int -> Bool -> [(Int, [FiniteCategory])]
biconnectedCanonicalCategories n objectFilter cauchyOnly =
  [ (k, map parseKey (Set.toAscList keys))
  | (k, keys) <- biconnectedCanonicalKeys n objectFilter cauchyOnly
  ]
  where
    parseKey key =
      case parseCategoryKey key of
        Right cat -> cat
        Left err -> error ("internal biconnected key parse failure: " ++ err)

biconnectedCanonicalCategoriesCached :: Int -> Maybe Int -> Bool -> IO [(Int, [FiniteCategory])]
biconnectedCanonicalCategoriesCached n objectFilter cauchyOnly = do
  groups <- biconnectedCanonicalKeysCached n objectFilter cauchyOnly
  pure
    [ (k, map parseKey (Set.toAscList keys))
    | (k, keys) <- groups
    ]
  where
    parseKey key =
      case parseCategoryKey key of
        Right cat -> cat
        Left err -> error ("cached biconnected key parse failure: " ++ err)

biconnectedCanonicalKeys :: Int -> Maybe Int -> Bool -> [(Int, Set.Set String)]
biconnectedCanonicalKeys n objectFilter cauchyOnly =
  [ (k, keys)
  | k <- maybe [1 .. integerSquareRoot n] (:[]) objectFilter
  , k >= 1
  , k * k <= n
  , let keys = biconnectedKeys cauchyOnly n k
  , not (Set.null keys)
  ]

biconnectedCanonicalKeysCached :: Int -> Maybe Int -> Bool -> IO [(Int, Set.Set String)]
biconnectedCanonicalKeysCached n objectFilter cauchyOnly = do
  groups <-
    traverse
      ( \k -> do
          keys <- cachedBiconnectedKeys cauchyOnly n k
          pure (k, keys)
      )
      [ k
      | k <- maybe [1 .. integerSquareRoot n] (:[]) objectFilter
      , k >= 1
      , k * k <= n
      ]
  pure [(k, keys) | (k, keys) <- groups, not (Set.null keys)]

biconnectedKeys :: Bool -> Int -> Int -> Set.Set String
biconnectedKeys cauchyOnly n k
  | n < 1 || k < 1 || k * k > n = Set.empty
  | cauchyOnly = biconnectedCauchyKeyCache !! n !! k
  | otherwise = biconnectedAllKeyCache !! n !! k

biconnectedAllKeyCache :: [[Set.Set String]]
biconnectedAllKeyCache =
  [ [ computeBiconnectedKeys n k False
    | k <- [0 .. n]
    ]
  | n <- [0 ..]
  ]

biconnectedCauchyKeyCache :: [[Set.Set String]]
biconnectedCauchyKeyCache =
  [ [ computeBiconnectedKeys n k True
    | k <- [0 .. n]
    ]
  | n <- [0 ..]
  ]

computeBiconnectedKeys :: Int -> Int -> Bool -> Set.Set String
computeBiconnectedKeys n k cauchyOnly =
  if cauchyOnly && k == 1
    then Set.fromList [canonicalKey cat | cat <- finiteGroupCategories n]
    else
      Set.fromList
        [ canonicalKey cat
        | shape <- biconnectedShapesFor n (Just k)
        , cat <- if cauchyOnly then enumerateShapeCauchy shape else enumerateShape shape
        , isBiconnectedCategory cat
        , not cauchyOnly || isCauchyComplete cat
        ]

integerSquareRoot :: Int -> Int
integerSquareRoot n =
  floor (sqrt (fromIntegral n :: Double))

cachedBiconnectedKeys :: Bool -> Int -> Int -> IO (Set.Set String)
cachedBiconnectedKeys cauchyOnly n k
  | n < 1 || k < 1 || k * k > n = pure Set.empty
  | otherwise = do
      createDirectoryIfMissing True biconnectedCacheDir
      exists <- doesFileExist path
      if exists
        then readCacheFile path
        else do
          let keys = biconnectedKeys cauchyOnly n k
          writeFile path (unlines (Set.toAscList keys))
          pure keys
  where
    path = biconnectedCacheFile cauchyOnly n k

biconnectedCacheDir :: FilePath
biconnectedCacheDir =
  ".cat-enum-cache" </> "v1" </> "biconnected"

biconnectedCacheFile :: Bool -> Int -> Int -> FilePath
biconnectedCacheFile cauchyOnly n k =
  biconnectedCacheDir
    </> ("cauchy-" ++ boolName cauchyOnly ++ "-morphisms-" ++ show n ++ "-objects-" ++ show k ++ ".cats")

readCacheFile :: FilePath -> IO (Set.Set String)
readCacheFile path =
  Set.fromList . filter (not . null) . lines <$> readFile path

boolName :: Bool -> String
boolName True = "true"
boolName False = "false"
