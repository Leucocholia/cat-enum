module Main (main) where

import CodexSlop.Category
import CodexSlop.Biconnected (biconnectedCanonicalCategoriesCached)
import qualified Data.Set as Set
import qualified Data.Vector as V
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

main :: IO ()
main = do
  putStrLn "=== Center and trace of biconnected components ===\n"

  forM_ [3 .. 9] $ \n -> do
    groups <- biconnectedCanonicalCategoriesCached n Nothing True
    let cats = concatMap snd groups
    putStrLn $ "--- n = " ++ show n ++ " (" ++ show (length cats) ++ " biconnected, Cauchy) ---"

    let czs = [center cat | cat <- cats]
        trs = [trace cat | cat <- cats]
        cSizes = [Set.size cz | cz <- czs]
        tSizes = [Set.size tr | tr <- trs]

    printf "  Center sizes:  "
    showDistrib cSizes
    printf "  Trace sizes:   "
    showDistrib tSizes
    printf "  (|Z|,|Tr|) pairs:\n"
    let pairs = [(czSize, trSize, cnt)
                | let ps = [(Set.size (czs !! i), Set.size (trs !! i)) | i <- [0..length cats-1]]
                , p <- Set.toList (Set.fromList ps)
                , let (czSize, trSize) = p
                , let cnt = length (filter (== p) ps)
                ]
    forM_ pairs $ \(cz, tr, cnt) ->
      printf "    (%d,%d): %d components\n" cz tr cnt
    putStrLn ""

showDistrib :: [Int] -> IO ()
showDistrib xs = do
  let uniq = Set.toList (Set.fromList xs)
  forM_ uniq $ \sz ->
    printf "%d(x%d) " sz (length (filter (== sz) xs))
  putStrLn ""

-- | Center: natural endomorphisms of the identity functor.
-- Returns a set of action vectors [α_0 .. α_{k-1}] where α_x is an
-- endomorphism of x satisfying α_y ∘ f = f ∘ α_x for all f: x→y.
center :: FiniteCategory -> Set.Set [Int]
center cat =
  Set.fromList [alpha | alpha <- sequence choices, natural alpha]
  where
    k = fcObjectCount cat
    n = fcMorphismCount cat
    morphs = [0 .. n - 1]
    objs = [0 .. k - 1]

    endos x = [f | f <- morphs, fcSources cat V.! f == x, fcTargets cat V.! f == x]
    choices = [endos x | x <- objs]

    natural alpha =
      and [ composeAt cat (alpha !! y) f == composeAt cat f (alpha !! x)
          | x <- objs, y <- objs
          , f <- homMorphisms cat x y
          ]

-- | Trace: endomorphisms modulo f∘g ∼ g∘f.
-- Returns a set of representatives (one per equivalence class).
trace :: FiniteCategory -> Set.Set Int
trace cat
  | null endos = Set.empty
  | otherwise  = Set.fromList (map minimum classes)
  where
    n = fcMorphismCount cat
    morphs = [0 .. n - 1]
    endos = [f | f <- morphs, isEndomorphism cat f]

    -- Build adjacency: a → b if there exist composable p,q with p∘q=a, q∘p=b
    adj a = [b | b <- endos, a /= b
              , or [ composeAt cat p q == a && composeAt cat q p == b
                   | p <- morphs, q <- morphs
                   , isComposable cat p q && isComposable cat q p
                   ]
            ]

    -- Connected components via depth-first search
    classes = go (Set.fromList endos) []
    go remaining acc
      | Set.null remaining = acc
      | otherwise =
          let x = Set.findMin remaining
              cls = dfs x Set.empty
          in go (Set.difference remaining cls) (cls : acc)

    dfs x visited
      | x `Set.member` visited = visited
      | otherwise = foldl (flip dfs) (Set.insert x visited) (adj x)

forM_ :: [a] -> (a -> IO b) -> IO ()
forM_ []     _ = return ()
forM_ (x:xs) f = f x >> forM_ xs f
