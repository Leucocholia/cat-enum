module CodexSlop.Search
  ( enumerateCanonicalCategories
  , enumerateCanonicalKeys
  , enumerateRepresentativeCategories
  , enumerateRepresentativeKeys
  , enumerateShape
  , enumerateShapeCauchy
  , enumerateShapeFromTable
  , initialTableForShape
  ) where

import CodexSlop.Canonical (RepresentativeMode(..), representativeKey)
import CodexSlop.Category
import CodexSlop.Shape

import Control.Monad (foldM)
import qualified Data.Set as Set
import qualified Data.Vector as V

enumerateCanonicalCategories :: Int -> Maybe Int -> Bool -> Bool -> [(Int, [FiniteCategory])]
enumerateCanonicalCategories n objectFilter connectedOnly cauchyOnly =
  enumerateRepresentativeCategories (defaultCanonicalMode cauchyOnly) n objectFilter connectedOnly cauchyOnly

enumerateRepresentativeCategories :: RepresentativeMode -> Int -> Maybe Int -> Bool -> Bool -> [(Int, [FiniteCategory])]
enumerateRepresentativeCategories mode n objectFilter connectedOnly cauchyOnly =
  [ (k, map parseKey (Set.toAscList keys))
  | (k, keys) <- enumerateRepresentativeKeys mode n objectFilter connectedOnly cauchyOnly
  ]
  where
    parseKey key =
      case parseCategoryKey key of
        Right cat -> cat
        Left err -> error ("internal representative key parse failure: " ++ err)

enumerateCanonicalKeys :: Int -> Maybe Int -> Bool -> Bool -> [(Int, Set.Set String)]
enumerateCanonicalKeys n objectFilter connectedOnly cauchyOnly =
  enumerateRepresentativeKeys (defaultCanonicalMode cauchyOnly) n objectFilter connectedOnly cauchyOnly

enumerateRepresentativeKeys :: RepresentativeMode -> Int -> Maybe Int -> Bool -> Bool -> [(Int, Set.Set String)]
enumerateRepresentativeKeys mode n objectFilter connectedOnly cauchyOnly =
  [ (k, keys)
  | k <- maybe [1 .. n] (:[]) objectFilter
  , let keys =
          Set.fromList
            [ representativeKey mode cat
            | shape <- shapesFor n (Just k) connectedOnly
            , cat <- if cauchyOnly then enumerateShapeCauchy shape else enumerateShape shape
            , not cauchyOnly || isCauchyComplete cat
            ]
  , not (Set.null keys)
  ]

defaultCanonicalMode :: Bool -> RepresentativeMode
defaultCanonicalMode True = UpToEquivalence
defaultCanonicalMode False = UpToIsomorphism

enumerateShape :: Shape -> [FiniteCategory]
enumerateShape = enumerateShapeWith False

enumerateShapeCauchy :: Shape -> [FiniteCategory]
enumerateShapeCauchy = enumerateShapeWith True

enumerateShapeWith :: Bool -> Shape -> [FiniteCategory]
enumerateShapeWith requireCauchy shape =
  enumerateShapeFromTable requireCauchy shape initialTable
  where
    initialTable = initialTableForShape shape

enumerateShapeFromTable :: Bool -> Shape -> V.Vector Int -> [FiniteCategory]
enumerateShapeFromTable requireCauchy shape table0 =
  case propagateAndPrune requireCauchy shape table0 of
    Nothing -> []
    Just table -> search table
  where
    n = shapeMorphismCount shape
    sources = shapeSources shape
    targets = shapeTargets shape
    identities = shapeIdentities shape

    search table =
      case chooseCell shape table of
        Nothing ->
          let cat = makeCategory table
          in if null (validateCategory cat) && cauchyOk cat then [cat] else []
        Just idx ->
          concat
            [ maybe [] search (assignAndPropagate requireCauchy shape table idx value)
            | value <- domainForCell shape idx
            ]

    makeCategory table =
      FiniteCategory
        { fcMorphismCount = n
        , fcObjectCount = shapeObjectCount shape
        , fcSources = sources
        , fcTargets = targets
        , fcIdentities = identities
        , fcCompose = table
        }

    cauchyOk cat = not requireCauchy || isCauchyComplete cat

initialTableForShape :: Shape -> V.Vector Int
initialTableForShape shape =
  V.fromList
    [ initialCell f g
    | f <- [0 .. n - 1]
    , g <- [0 .. n - 1]
    ]
  where
    n = shapeMorphismCount shape
    sources = shapeSources shape
    targets = shapeTargets shape
    isId = shapeIsIdentity shape
    initialCell f g
      | targets V.! f /= sources V.! g = -1
      | isId V.! f = g
      | isId V.! g = f
      | otherwise = -2

chooseCell :: Shape -> V.Vector Int -> Maybe Int
chooseCell shape table =
  case candidates of
    [] -> Nothing
    _ -> Just (minimumByDomain candidates)
  where
    candidates = [idx | idx <- [0 .. V.length table - 1], table V.! idx == -2]
    minimumByDomain = foldl1 better
    better a b
      | score a <= score b = a
      | otherwise = b
    score idx =
      ( length (domainForCell shape idx)
      , - constraintDegree shape idx
      )

constraintDegree :: Shape -> Int -> Int
constraintDegree shape idx =
  length
    [ ()
    | (f, g, h) <- composableTriples shape
    , pairIndex n f g == idx
        || pairIndex n g h == idx
        || pairIndex n f h == idx
    ]
  where
    n = shapeMorphismCount shape

domainForCell :: Shape -> Int -> [Int]
domainForCell shape idx =
  blockAt shape (shapeSources shape V.! f) (shapeTargets shape V.! g)
  where
    n = shapeMorphismCount shape
    (f, g) = idx `divMod` n

assignAndPropagate :: Bool -> Shape -> V.Vector Int -> Int -> Int -> Maybe (V.Vector Int)
assignAndPropagate requireCauchy shape table idx value = do
  (table', _) <- setCell shape table idx value
  propagateAndPrune requireCauchy shape table'

propagateAndPrune :: Bool -> Shape -> V.Vector Int -> Maybe (V.Vector Int)
propagateAndPrune requireCauchy shape table = do
  table' <- propagate shape table
  if not requireCauchy || partialCauchyViable shape table'
    then Just table'
    else Nothing

propagate :: Shape -> V.Vector Int -> Maybe (V.Vector Int)
propagate shape table = do
  (table', changed) <- foldM step (table, False) (composableTriples shape)
  if changed then propagate shape table' else Just table'
  where
    n = shapeMorphismCount shape

    step (current, changed) (f, g, h) =
      let fg = current V.! pairIndex n f g
          gh = current V.! pairIndex n g h
      in if assigned fg && assigned gh
           then
             let leftIndex = pairIndex n fg h
                 rightIndex = pairIndex n f gh
                 left = current V.! leftIndex
                 right = current V.! rightIndex
             in case (assigned left, assigned right) of
                  (True, True) ->
                    if left == right then Just (current, changed) else Nothing
                  (True, False) -> do
                    (next, didChange) <- setCell shape current rightIndex left
                    Just (next, changed || didChange)
                  (False, True) -> do
                    (next, didChange) <- setCell shape current leftIndex right
                    Just (next, changed || didChange)
                  (False, False) -> Just (current, changed)
           else Just (current, changed)

setCell :: Shape -> V.Vector Int -> Int -> Int -> Maybe (V.Vector Int, Bool)
setCell shape table idx value
  | value < 0 || value >= n = Nothing
  | not (resultInExpectedBlock shape idx value) = Nothing
  | old == -2 = Just (table V.// [(idx, value)], True)
  | old == value = Just (table, False)
  | otherwise = Nothing
  where
    n = shapeMorphismCount shape
    old = table V.! idx

partialCauchyViable :: Shape -> V.Vector Int -> Bool
partialCauchyViable shape table =
  if shapeObjectCount shape == 1
    then all (== shapeIdentities shape V.! 0) forcedIdempotents
    else all hasPotentialSplit forcedIdempotents
  where
    n = shapeMorphismCount shape
    objects = [0 .. shapeObjectCount shape - 1]
    morphs = [0 .. n - 1]

    forcedIdempotents =
      [ e
      | e <- morphs
      , shapeSources shape V.! e == shapeTargets shape V.! e
      , table V.! pairIndex n e e == e
      ]

    hasPotentialSplit e =
      or
        [ compatibleCell (pairIndex n r s) e
            && compatibleCell (pairIndex n s r) (shapeIdentities shape V.! y)
        | y <- objects
        , r <- blockAt shape x y
        , s <- blockAt shape y x
        ]
      where
        x = shapeSources shape V.! e

    compatibleCell idx expected =
      let actual = table V.! idx
      in actual == -2 || actual == expected

resultInExpectedBlock :: Shape -> Int -> Int -> Bool
resultInExpectedBlock shape idx value =
  (shapeSources shape V.! value, shapeTargets shape V.! value)
    == (shapeSources shape V.! f, shapeTargets shape V.! g)
  where
    n = shapeMorphismCount shape
    (f, g) = idx `divMod` n

assigned :: Int -> Bool
assigned = (>= 0)

pairIndex :: Int -> Int -> Int -> Int
pairIndex n f g = f * n + g

composableTriples :: Shape -> [(Int, Int, Int)]
composableTriples shape =
  [ (f, g, h)
  | f <- morphs
  , g <- morphs
  , h <- morphs
  , shapeTargets shape V.! f == shapeSources shape V.! g
  , shapeTargets shape V.! g == shapeSources shape V.! h
  ]
  where
    morphs = [0 .. shapeMorphismCount shape - 1]
