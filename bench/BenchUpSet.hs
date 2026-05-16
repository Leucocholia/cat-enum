module Main (main) where

import CodexSlop.Enrichment
import CodexSlop.Shape (posetsFor, supportRelation)
import qualified Data.Vector as V
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

------------------------------------------------------------------------------
-- Lattice of up-sets of a poset

data Lattice = Lattice
  { latSize :: !Int
  , latTop  :: !Int          -- index of top = the whole carrier set
  , latBot  :: !Int          -- index of bottom = empty set
  , latMeet :: V.Vector Int  -- flat (n×n) meet table: meet[a][b] = a∧b
  , latLeq  :: V.Vector Bool -- flat (n×n) leq table: leq[a][b] = a≤b
  }

-- | Build the lattice J(P) of up-sets of a poset P.
-- The poset is given as a q×q Bool matrix in row-major order.
buildUpSetLattice :: Int -> [Bool] -> Lattice
buildUpSetLattice q poset =
  Lattice
    { latSize = length upsets
    , latTop  = topIdx
    , latBot  = botIdx
    , latMeet = V.fromList [meet a b | a <- [0 .. n-1], b <- [0 .. n-1]]
    , latLeq  = V.fromList [a `leq` b   | a <- [0 .. n-1], b <- [0 .. n-1]]
    }
  where
    n = length upsets
    -- upsets :: [V.Vector Bool]  each is a Bool mask of the up-set
    upsets = filter isUpSet (allSubsets q)
    topIdx = case [i | i <- [0..n-1], and (V.toList (upsets !! i))] of
               (i:_) -> i
               []    -> error "no top"
    botIdx = case [i | i <- [0..n-1], not (or (V.toList (upsets !! i)))] of
               (i:_) -> i
               []    -> error "no bottom"

    isUpSet mask = and
      [ not (posetAt x y) || mask V.! y
      | x <- [0..q-1], y <- [0..q-1]
      , mask V.! x
      ]

    posetAt i j = poset !! (i * q + j)

    a `leq` b = and (V.zipWith (\x y -> not x || y) (upsets !! a) (upsets !! b))

    meet a b =
      let merged = V.zipWith (\x y -> x && y) (upsets !! a) (upsets !! b)
      in case [i | i <- [0..n-1], upsets !! i == merged] of
           (i:_) -> i
           []    -> error "meet not found"

allSubsets :: Int -> [V.Vector Bool]
allSubsets q = map V.fromList (go q)
  where
    go 0 = [[]]
    go n = [False:rest | rest <- go (n-1)] ++ [True:rest | rest <- go (n-1)]

------------------------------------------------------------------------------
-- Enumerate J(P)-enriched categories

-- | Enumerate J(P)-enriched categories with @k@ objects.
-- Each off-diagonal hom-entry is any element of the lattice (0..latSize-1).
-- Diagonal entries are fixed to top.
-- This enumerates all (latSize)^(k² - k) possible matrices.
enumerateLattice :: Lattice -> Int -> [EnrichedCategory Int]
enumerateLattice lat k
  | k <= 0 = []
  | otherwise = filter (validLattice lat)
      [ EnrichedCategory k (V.fromList vals)
      | offDiag <- sequence (replicate (k * (k - 1)) [0 .. latSize lat - 1])
      , let vals = fillDiag k offDiag
      ]
  where
    fillDiag k' offDiag =
      [ if i == j then latTop lat else offDiag !! offIndex k' i j
      | i <- [0 .. k' - 1]
      , j <- [0 .. k' - 1]
      ]
    offIndex k' i j
      | j < i     = i * (k' - 1) + j
      | otherwise = i * (k' - 1) + j - 1

validLattice :: Lattice -> EnrichedCategory Int -> Bool
validLattice lat ec =
  and [ leq (meet (ecHom ec j l) (ecHom ec i j)) (ecHom ec i l)
      | i <- [0 .. k-1], j <- [0 .. k-1], l <- [0 .. k-1]
      ]
  where
    k = ecObjectCount ec
    leq a b = latLeq lat V.! (a * latSize lat + b)
    meet a b = latMeet lat V.! (a * latSize lat + b)

------------------------------------------------------------------------------
-- Benchmark helpers

main :: IO ()
main = do
  putStrLn "=== Up-set lattice enrichment benchmarks ===\n"

  -- Warm up the poset cache
  putStrLn "Warming cache..."
  let _ = posetsFor 4
  putStrLn ""

  -- Enumerate all posets up to 4 elements
  let allPosets = concat
        [ [(q, rel) | let ss = posetsFor q, s <- ss, let rel = V.toList (supportRelation s)]
        | q <- [1, 2, 3, 4]
        ]

  printf "Total posets (unlabeled, q=1..4): %d\n\n" (length allPosets)

  forM_ allPosets $ \(q, poset) -> do
    let lat = buildUpSetLattice q poset
        latName = showPoset q poset

    printf "--- J(P) for P = %s (|J(P)|=%d) ---\n" latName (latSize lat)

    -- Benchmark k=2,3
    forM_ [2, 3] $ \k -> do
      (count, time) <- timeIt (length (enumerateLattice lat k))
      printf "  k=%d: %6d cats  %8.2f ms\n" k count (time / 1000)

    putStrLn ""

  -- Comparison: Two-enrichment and Cardinal-enrichment times
  putStrLn "--- Comparison: existing Two / Cardinal enrichment ---"
  forM_ [2, 3] $ \k -> do
    (c2, t2) <- timeIt (length (enumerateTwo k))
    printf "  Two-enrichment:       k=%d: %6d supports  %8.2f ms\n" k c2 (t2 / 1000)
  forM_ [2, 3] $ \k -> do
    forM_ [k .. k + 3] $ \n -> do
      (cc, tc) <- timeIt (length (enumerateCardinal n k))
      printf "  Cardinal-enrichment:  n=%d k=%d: %6d mats  %8.2f ms\n" n k cc (tc / 1000)

  putStrLn "\nDone."

------------------------------------------------------------------------------
-- Utilities

showPoset :: Int -> [Bool] -> String
showPoset q rel = "[" ++ intercalate "," (map fmt [0..q-1]) ++ "]"
  where
    fmt i = "{" ++ concat [show j | j <- [0..q-1], i /= j, relAt i j] ++ "}"
    relAt i j = rel !! (i * q + j)

intercalate :: String -> [String] -> String
intercalate _ []     = ""
intercalate _ [x]    = x
intercalate s (x:xs) = x ++ s ++ intercalate s xs

timeIt :: a -> IO (a, Double)
timeIt action = do
  start <- getCPUTime
  let result = action
  result `seq` return ()
  end <- getCPUTime
  pure (result, fromIntegral (end - start) :: Double)

forM_ :: [a] -> (a -> IO b) -> IO ()
forM_ []     _ = return ()
forM_ (x:xs) f = f x >> forM_ xs f
