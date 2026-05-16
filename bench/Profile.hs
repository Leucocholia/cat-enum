module Main (main) where

import CodexSlop.Shape (SupportPreorder(..), posetsFor)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

main :: IO ()
main = do
  putStrLn "Timing canonicalPosetRelations (forcing full evaluation)..."
  forceList (posetsFor 3) `seq` return ()
  t3 <- timed $ length (posetsFor 3)
  printf "  q=3: %d posets, %.2f ms\n" (fst t3) (snd t3 / 1000)
  forceList (posetsFor 4) `seq` return ()
  t4 <- timed $ length (posetsFor 4)
  printf "  q=4: %d posets, %.2f ms\n" (fst t4) (snd t4 / 1000)
  forceList (posetsFor 5) `seq` return ()
  t5 <- timed $ length (posetsFor 5)
  printf "  q=5: %d posets, %.2f ms\n" (fst t5) (snd t5 / 1000)
  forceList (posetsFor 6) `seq` return ()
  t6 <- timed $ length (posetsFor 6)
  printf "  q=6: %d posets, %.2f ms\n" (fst t6) (snd t6 / 1000)

forceList :: [a] -> ()
forceList [] = ()
forceList (x:xs) = x `seq` forceList xs

timed :: a -> IO (a, Double)
timed action = do
  start <- getCPUTime
  let result = action
  result `seq` return ()
  end <- getCPUTime
  return (result, fromIntegral (end - start) :: Double)
