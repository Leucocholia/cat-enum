module Main where

import CodexSlop.Canonical
import CodexSlop.Category
import qualified Data.Set as Set

main :: IO ()
main = do
  contents <- readFile ".cat-enum-cache/v4/generated/isomorphism/cauchy-true-morphisms-9-objects-3.cats"
  let lines' = filter (not . null) (lines contents)
      cats = [case parseCategoryKey line of Right c -> c; Left e -> error e | line <- lines']
      allKeys = Set.fromList [canonicalKey c | c <- cats]
      dualKeys = Set.fromList [dualKey UpToIsomorphism c | c <- cats]
  
  putStrLn $ "Total cats: " ++ show (length cats)
  putStrLn $ "Unique canonicalKeys: " ++ show (Set.size allKeys)
  putStrLn $ "Unique dualKeys: " ++ show (Set.size dualKeys)
  putStrLn $ "Reduction: " ++ show (Set.size allKeys - Set.size dualKeys)
  putStrLn ""

  -- Find categories matching the two OEIS matrices
  let m1 = [[1,1,2],[1,1,2],[0,0,1]]
      m2 = [[1,2,2],[0,1,1],[0,1,1]]
      match m c = all (\(i,j) -> length (homMorphisms c i j) == (m !! i !! j)) 
                     [(i,j) | i <- [0..2], j <- [0..2]]
      cat1 = [c | c <- cats, match m1 c]
      cat2 = [c | c <- cats, match m2 c]
  
  putStrLn $ "Cats matching matrix 1: " ++ show (length cat1)
  putStrLn $ "Cats matching matrix 2: " ++ show (length cat2)
  
  if not (null cat1) && not (null cat2) then do
    let c1 = head cat1
        c2 = head cat2
        k1 = canonicalKey c1
        k2 = canonicalKey c2
        dk1 = dualKey UpToIsomorphism c1
        dk2 = dualKey UpToIsomorphism c2
    putStrLn $ "canonicalKey(c1) == canonicalKey(c2)? " ++ show (k1 == k2)
    putStrLn $ "dualKey(c1) == dualKey(c2)? " ++ show (dk1 == dk2)
    putStrLn $ "canonicalKey(c1) == canonicalKey(opp(c2))? " ++ show (k1 == canonicalKey (oppositeCategory c2))
    putStrLn $ "canonicalKey(opp(c1)) == canonicalKey(c2)? " ++ show (canonicalKey (oppositeCategory c1) == k2)
  else
    putStrLn "Could not find matching categories"
