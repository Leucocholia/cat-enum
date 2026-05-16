module CodexSlop.Copresheaf
  ( copresheafCountsUpTo
  , countCopresheavesOfSize
  , countCopresheavesForProfile
  ) where

import CodexSlop.Category
import CodexSlop.Decompose

import Control.Monad (foldM)
import Data.Maybe (fromMaybe)
import qualified Data.Vector as V

copresheafCountsUpTo :: Int -> FiniteCategory -> [(Int, Integer)]
copresheafCountsUpTo maxElements cat =
  case disjointUnionComponents cat of
    [] -> directCopresheafCountsUpTo maxElements cat
    [_] -> directCopresheafCountsUpTo maxElements cat
    components ->
      convolveMany maxElements
        [ copresheafCountsUpTo maxElements component
        | component <- components
        ]

directCopresheafCountsUpTo :: Int -> FiniteCategory -> [(Int, Integer)]
directCopresheafCountsUpTo maxElements cat =
  [ (size, directCountCopresheavesOfSize cat size)
  | size <- [0 .. maxElements]
  ]

countCopresheavesOfSize :: FiniteCategory -> Int -> Integer
countCopresheavesOfSize cat total =
  fromMaybe 0 (lookup total (countCopresheavesDirectOrFactored total cat))

countCopresheavesDirectOrFactored :: Int -> FiniteCategory -> [(Int, Integer)]
countCopresheavesDirectOrFactored maxElements cat =
  case disjointUnionComponents cat of
    [] -> directCounts
    [_] -> directCounts
    components ->
      convolveMany maxElements
        [ copresheafCountsUpTo maxElements component
        | component <- components
        ]
  where
    directCounts =
      [ (size, directCountCopresheavesOfSize cat size)
      | size <- [0 .. maxElements]
      ]

directCountCopresheavesOfSize :: FiniteCategory -> Int -> Integer
directCountCopresheavesOfSize cat total =
  sum
    [ countCopresheavesForProfile cat profile
    | profile <- compositions total (fcObjectCount cat)
    ]

countCopresheavesForProfile :: FiniteCategory -> [Int] -> Integer
countCopresheavesForProfile cat profile
  | length profile /= fcObjectCount cat = 0
  | length components > 1 =
      product
        [ countCopresheavesForProfile (componentCategory cat objects) [profile !! obj | obj <- objects]
        | objects <- components
        ]
  | otherwise =
      case propagate initialMaps of
        Nothing -> 0
        Just maps0 -> search maps0
  where
    components = connectedObjectComponents cat
    n = fcMorphismCount cat
    morphs = [0 .. n - 1]

    initialMaps =
      V.fromList
        [ if isIdentity cat f
            then Just [0 .. profile !! (fcSources cat V.! f) - 1]
            else Nothing
        | f <- morphs
        ]

    search maps =
      case chooseMorphism maps of
        Nothing -> 1
        Just f ->
          sum
            [ maybe 0 search (assignAndPropagate maps f fn)
            | fn <- functionChoices (profile !! (fcSources cat V.! f)) (profile !! (fcTargets cat V.! f))
            ]

    chooseMorphism maps =
      case unknowns of
        [] -> Nothing
        _ -> Just (foldl1 better unknowns)
      where
        unknowns = [f | f <- morphs, maps V.! f == Nothing]
        better f g
          | functionCount f <= functionCount g = f
          | otherwise = g
        functionCount f =
          let sourceSize = profile !! (fcSources cat V.! f)
              targetSize = profile !! (fcTargets cat V.! f)
          in if sourceSize == 0
               then 1
               else if targetSize == 0
                 then 0
                 else targetSize ^ sourceSize

    assignAndPropagate maps f fn = do
      maps' <- setMap maps f fn
      propagate maps'

    propagate maps = do
      (maps', changed) <- foldM step (maps, False) composablePairs
      if changed then propagate maps' else Just maps'

    step (maps, changed) (f, g) =
      let fg = composeAt cat f g
      in case (maps V.! f, maps V.! g) of
           (Just ff, Just gg) -> do
             let forced = composeFunctions ff gg
             maps' <- setMap maps fg forced
             Just (maps', changed || maps' /= maps)
           _ -> Just (maps, changed)

    setMap maps f fn
      | not (wellTyped f fn) = Nothing
      | otherwise =
          case maps V.! f of
            Nothing -> Just (maps V.// [(f, Just fn)])
            Just old
              | old == fn -> Just maps
              | otherwise -> Nothing

    wellTyped f fn =
      length fn == profile !! (fcSources cat V.! f)
        && all (\x -> x >= 0 && x < profile !! (fcTargets cat V.! f)) fn

    composablePairs =
      [ (f, g)
      | f <- morphs
      , g <- morphs
      , isComposable cat f g
      ]

functionChoices :: Int -> Int -> [[Int]]
functionChoices domainSize codomainSize
  | domainSize == 0 = [[]]
  | codomainSize == 0 = []
  | otherwise = sequence (replicate domainSize [0 .. codomainSize - 1])

composeFunctions :: [Int] -> [Int] -> [Int]
composeFunctions f g = map (g !!) f

convolveMany :: Int -> [[(Int, Integer)]] -> [(Int, Integer)]
convolveMany maxElements =
  foldl (convolveCounts maxElements) [(0, 1)]

convolveCounts :: Int -> [(Int, Integer)] -> [(Int, Integer)] -> [(Int, Integer)]
convolveCounts maxElements left right =
  [ (size, coefficient size)
  | size <- [0 .. maxElements]
  ]
  where
    coefficient size =
      sum
        [ leftCount * rightCount
        | (leftSize, leftCount) <- left
        , (rightSize, rightCount) <- right
        , leftSize + rightSize == size
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
