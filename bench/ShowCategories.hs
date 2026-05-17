module Main where

import CodexSlop.Canonical
import CodexSlop.Category
import qualified Data.Vector as V
import qualified Data.Set as Set
import Data.List (intercalate, sort, group)

main :: IO ()
main = do
  contents <- readFile ".cat-enum-cache/v4/generated/isomorphism/cauchy-true-morphisms-9-objects-3.cats"
  let lines' = filter (not . null) (lines contents)
      cats = [(line, case parseCategoryKey line of Right c -> c; Left e -> error e) | line <- lines']
      withSig = [(makeSignature c, line, c) | (line, c) <- cats]
      sigGroups = groupBySignatures withSig

  putStrLn $ "Total: " ++ show (length cats) ++ " categories.\n"
  putStrLn $ "Distinct signatures: " ++ show (length sigGroups) ++ "\n"

  -- Find the two disputed categories from the notes
  let m1 = [[1,1,2],[1,1,2],[0,0,1]]
      m2 = [[1,2,2],[0,1,1],[0,1,1]]
      disputed1 = [(sig, k, c) | (sig, k, c) <- withSig, sigMatrix sig == m1]
      disputed2 = [(sig, k, c) | (sig, k, c) <- withSig, sigMatrix sig == m2]

  putStrLn $ "Categories matching matrix 1: " ++ show (length disputed1)
  if not (null disputed1) then
    let (sig, key, cat) = head disputed1 in do
      putStrLn $ "  Key: " ++ take 80 key ++ "..."
      putStrLn $ "  Out/in pairs: " ++ show (sigOutIn sig)
      putStrLn $ "  dualKey: " ++ dualKey UpToIsomorphism cat
  else pure ()

  putStrLn $ "Categories matching matrix 2: " ++ show (length disputed2)
  if not (null disputed2) then
    let (sig, key, cat) = head disputed2 in do
      putStrLn $ "  Key: " ++ take 80 key ++ "..."
      putStrLn $ "  Out/in pairs: " ++ show (sigOutIn sig)
      putStrLn $ "  dualKey: " ++ dualKey UpToIsomorphism cat
      let opp = oppositeCategory cat
          key1 = let (_, k1, _) = head disputed1 in k1
      putStrLn $ "  canonicalKey(opposite) matches key of matrix-1? "
        ++ show (canonicalKey opp == key1)
  else pure ()

  putStrLn ""

  -- Print each distinct signature
  putStrLn $ "All distinct signatures (matrix | out/in pairs | count):\n"
  forM_ (zip [1..] sigGroups) $ \(idx, group) -> do
    let (sig, _, _) = head group
    putStrLn $ show idx ++ ". Matrix:"
    forM_ (sigMatrix sig) $ \row ->
      putStrLn $ "     " ++ show row
    putStrLn $ "    Out/in: " ++ show (sigOutIn sig) 
    putStrLn $ "    Endos:  " ++ show (sigEndos sig)
    putStrLn $ "    Count:  " ++ show (length group)
    putStrLn ""

data Signature = Signature
  { sigMatrix :: [[Int]]
  , sigOutIn  :: [(Int, Int)]
  , sigEndos  :: [Int]
  } deriving (Eq, Ord, Show)

makeSignature :: FiniteCategory -> Signature
makeSignature cat =
  Signature
    { sigMatrix = [[homCount i j | j <- [0..k-1]] | i <- [0..k-1]]
    ,     sigOutIn  = sort [(out, inn) | i <- [0..k-1]
                    , let out = sum [homCount i col | col <- [0..k-1]]
                    , let inn = sum [homCount row i | row <- [0..k-1]]]
    , sigEndos  = sort [homCount i i | i <- [0..k-1]]
    }
  where
    k = fcObjectCount cat
    n = fcMorphismCount cat
    src = fcSources cat
    tgt = fcTargets cat
    homCount s t = length [f | f <- [0..n-1], src V.! f == s, tgt V.! f == t]

groupBySignatures :: [(Signature, String, FiniteCategory)] -> [[(Signature, String, FiniteCategory)]]
groupBySignatures [] = []
groupBySignatures (x:xs) = 
  let (same, rest) = partition (\(s, _, _) -> s == fst3 x) xs
  in (x : same) : groupBySignatures rest
  where
    fst3 (a, _, _) = a
    partition p = foldr (\x (ts, fs) -> if p x then (x:ts, fs) else (ts, x:fs)) ([], [])

forM_ :: [a] -> (a -> IO b) -> IO ()
forM_ []     _ = return ()
forM_ (x:xs) f = f x >> forM_ xs f
