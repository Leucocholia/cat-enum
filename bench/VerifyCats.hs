module Main where

import CodexSlop.Canonical
import CodexSlop.Category
import qualified Data.Set as Set

main :: IO ()
main = do
  forM_ [3, 4, 5] $ \k -> do
    contents <- readFile $ ".cat-enum-cache/v4/generated/isomorphism/cauchy-true-morphisms-9-objects-" ++ show k ++ ".cats"
    let lines' = filter (not . null) (lines contents)
        cats = [case parseCategoryKey line of Right c -> c; Left e -> error e | line <- lines']
        keys = [canonicalKey c | c <- cats]
        unique = Set.fromList keys

    putStrLn $ "k=" ++ show k ++ ": " ++ show (length cats) ++ " cats, "
           ++ show (Set.size unique) ++ " unique keys, "
           ++ show (length cats - Set.size unique == 0)

    -- Also verify dualKey is consistent
    let dkeys = Set.fromList [dualKey UpToIsomorphism c | c <- cats]
    putStrLn $ "  dualKey -> " ++ show (Set.size dkeys) ++ " unique"

    -- Check: are any two cats that share a dualKey actually isomorphic?
    -- (If two cats have the same dualKey but different canonicalKey, they're formal duals.)
    let dbl = [(dualKey UpToIsomorphism c, canonicalKey c) | c <- cats]
        dblKeys = [(dk, ck) | (dk, ck) <- dbl]
        dblSet = Set.fromList dblKeys
    putStrLn $ "  (dualKey, canonicalKey) pairs: " ++ show (Set.size dblSet)
    putStrLn ""

forM_ :: [a] -> (a -> IO b) -> IO ()
forM_ []     _ = return ()
forM_ (x:xs) f = f x >> forM_ xs f
