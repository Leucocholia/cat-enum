module Main (main) where

import CodexSlop.Enrichment
import CodexSlop.Shape (supportsFor)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

main :: IO ()
main = do
  -- Warm the poset cache so layer-1 times reflect only the expansion.
  putStrLn "Warming support cache..."
  let _ = supportsFor 6
  putStrLn ""

  putStrLn "=== Enrichment layer benchmarks (warm cache) ===\n"

  -- Layer 1: Two lattice (support preorders)
  putStrLn "--- Layer 1: enumerateTwo k (support preorders) ---"
  benchTwo [1 .. 6]

  -- Layer 2: Cardinal lattice (hom-count matrices)
  putStrLn ""
  putStrLn "--- Layer 2: enumerateCardinal n k (hom-count matrices) ---"
  putStrLn "  [fixed k=2, varying n]"
  benchCardinal [(n, 2) | n <- [3, 5, 7, 9, 11]]
  putStrLn "  [fixed n=10, varying k]"
  benchCardinal [(10, k) | k <- [2, 3, 4, 5]]
  putStrLn "  [fixed n=12, varying k]"
  benchCardinal [(12, k) | k <- [2, 3, 4]]

  -- Pipeline: Two + refine + Cardinal
  putStrLn ""
  putStrLn "--- Pipeline: supports + refine ---"
  benchPipeline [(6, k) | k <- [2, 3, 4]]
  benchPipeline [(8, k) | k <- [2, 3]]
  benchPipeline [(10, k) | k <- [2, 3]]

  putStrLn ""
  putStrLn "Done."

benchTwo :: [Int] -> IO ()
benchTwo ks = do
  forM_ ks $ \k -> do
    (count, time) <- timeIt (length (enumerateTwo k))
    printf "  k=%d: %5d supports  %8.2f ms\n" k count (time / 1000)

benchCardinal :: [(Int, Int)] -> IO ()
benchCardinal nks = do
  forM_ nks $ \(n, k) -> do
    (count, time) <- timeIt (length (enumerateCardinal n k))
    printf "  n=%d k=%d: %8d matrices  %8.2f ms\n" n k count (time / 1000)

benchPipeline :: [(Int, Int)] -> IO ()
benchPipeline nks = do
  forM_ nks $ \(n, k) -> do
    (totalCount, time) <- timeIt $ do
      let supports = enumerateTwo k
      sum [length (refine sup n) | sup <- supports]
    printf "  n=%d k=%d: %8d pairs  %8.2f ms\n" n k totalCount (time / 1000)

timeIt :: a -> IO (a, Double)
timeIt action = do
  start <- getCPUTime
  let result = action
  result `seq` return ()
  end <- getCPUTime
  let us = fromIntegral (end - start) :: Double
  return (result, us / 1000)

forM_ :: [a] -> (a -> IO b) -> IO ()
forM_ []     _ = return ()
forM_ (x:xs) f = f x >> forM_ xs f
