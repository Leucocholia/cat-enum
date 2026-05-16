module CodexSlop.Generate
  ( componentGeneratedCategories
  , componentGeneratedCategoriesWith
  , componentGeneratedKeys
  , componentGeneratedKeysWith
  , componentGeneratedKeysCached
  , componentGeneratedKeysCachedWith
  , equalityGeneratedCounts
  ) where

import CodexSlop.Biconnected
import CodexSlop.Canonical (RepresentativeMode(..), allEqualityKeys, equalityCount, representativeKey, representativeModeName)
import CodexSlop.Category
import CodexSlop.Decompose (disjointUnionCategory, isConnectedCategory)
import CodexSlop.Group (finiteGroupCategories)
import CodexSlop.Profunctor
import CodexSlop.Search
import CodexSlop.Shape

import Control.Monad (forM)
import Data.List (intercalate, permutations, sort)
import qualified Data.Set as Set
import qualified Data.Vector as V
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((</>))

data GeneratedSkeleton = GeneratedSkeleton
  { gsPoset :: !SupportPreorder
  , gsComponents :: ![FiniteCategory]
  , gsMatrix :: ![Int]
  } deriving (Eq, Show)

data ConnectedBlock = ConnectedBlock
  { cbMorphisms :: !Int
  , cbObjects :: !Int
  , cbCategory :: !FiniteCategory
  } deriving (Eq, Ord, Show)

componentGeneratedCategories :: Int -> Maybe Int -> Bool -> [(Int, [FiniteCategory])]
componentGeneratedCategories n objectFilter cauchyOnly =
  componentGeneratedCategoriesWith (defaultGeneratedMode cauchyOnly) n objectFilter cauchyOnly

componentGeneratedCategoriesWith :: RepresentativeMode -> Int -> Maybe Int -> Bool -> [(Int, [FiniteCategory])]
componentGeneratedCategoriesWith mode n objectFilter cauchyOnly =
  [ (k, map parseKey (Set.toAscList keys))
  | (k, keys) <- componentGeneratedKeysWith mode n objectFilter cauchyOnly
  ]
  where
    parseKey key =
      case parseCategoryKey key of
        Right cat -> cat
        Left err -> error ("internal generated key parse failure: " ++ err)

componentGeneratedKeys :: Int -> Maybe Int -> Bool -> [(Int, Set.Set String)]
componentGeneratedKeys n objectFilter cauchyOnly =
  componentGeneratedKeysWith (defaultGeneratedMode cauchyOnly) n objectFilter cauchyOnly

componentGeneratedKeysWith :: RepresentativeMode -> Int -> Maybe Int -> Bool -> [(Int, Set.Set String)]
componentGeneratedKeysWith mode n objectFilter cauchyOnly =
  [ (k, keys)
  | k <- maybe [1 .. n] (:[]) objectFilter
  , let keys =
          Set.fromList
            [ representativeKey mode cat
            | cat <- generatedCategoriesForObjectCount n k cauchyOnly
            , not cauchyOnly || isCauchyComplete cat
            ]
  , not (Set.null keys)
  ]

componentGeneratedKeysCached :: Int -> Maybe Int -> Bool -> IO [(Int, Set.Set String)]
componentGeneratedKeysCached n objectFilter cauchyOnly = do
  componentGeneratedKeysCachedWith (defaultGeneratedMode cauchyOnly) n objectFilter cauchyOnly

componentGeneratedKeysCachedWith :: RepresentativeMode -> Int -> Maybe Int -> Bool -> IO [(Int, Set.Set String)]
componentGeneratedKeysCachedWith mode n objectFilter cauchyOnly = do
  let requestedObjects = maybe [1 .. n] (:[]) objectFilter
      requestedSmallExtras =
        [ n - k
        | k <- requestedObjects
        , n - k >= 3
        , n - k <= 4
        ]
  smallExtraBlocks <-
    if cauchyOnly && not (null requestedSmallExtras)
      then connectedBlocksUpToExtraCached (maximum requestedSmallExtras)
      else pure []
  groups <-
    forM requestedObjects $ \k -> do
      keys <- cachedGeneratedKeys mode n k cauchyOnly (computeKeys smallExtraBlocks k)
      pure (k, keys)
  pure [(k, keys) | (k, keys) <- groups, not (Set.null keys)]
  where
    computeKeys smallExtraBlocks k
      | mode == UpToEquality = do
          isoKeys <- cachedGeneratedKeys UpToIsomorphism n k cauchyOnly (isoComputeKeys smallExtraBlocks k)
          let cats = [cat | key <- Set.toAscList isoKeys, Right cat <- [parseCategoryKey key]]
          pure (Set.unions (map allEqualityKeys cats))
      | otherwise = isoComputeKeys smallExtraBlocks k

    isoComputeKeys smallExtraBlocks k =
      case smallExtraCauchyKeys mode n k cauchyOnly of
        Just fastKeys -> pure fastKeys
        Nothing
          | Just fastKeys <- smallExtraCauchyKeysFromBlocks mode smallExtraBlocks n k cauchyOnly ->
              pure fastKeys
          | otherwise -> do
              cats <- generatedCategoriesForObjectCountCached n k cauchyOnly
              pure
                ( Set.fromList
                    [ representativeKey mode cat
                    | cat <- cats
                    , not cauchyOnly || isCauchyComplete cat
                    ]
                )

equalityGeneratedCounts :: Int -> Maybe Int -> Bool -> IO [(Int, Int)]
equalityGeneratedCounts n objectFilter cauchyOnly = do
  let requestedObjects = maybe [1 .. n] (:[]) objectFilter
  forM requestedObjects $ \k -> do
    isoKeys <- cachedGeneratedKeys UpToIsomorphism n k cauchyOnly (isoComputeForCounts n k cauchyOnly)
    let cats = [cat | key <- Set.toAscList isoKeys, Right cat <- [parseCategoryKey key]]
        count = sum (map equalityCount cats)
    pure (k, count)
  where
    isoComputeForCounts n' k' cauchyOnly' = do
      cats <- generatedCategoriesForObjectCountCached n' k' cauchyOnly'
      pure
        ( Set.fromList
            [ representativeKey UpToIsomorphism cat
            | cat <- cats
            , not cauchyOnly' || isCauchyComplete cat
            ]
        )

defaultGeneratedMode :: Bool -> RepresentativeMode
defaultGeneratedMode True = UpToEquivalence
defaultGeneratedMode False = UpToIsomorphism

cachedGeneratedKeys :: RepresentativeMode -> Int -> Int -> Bool -> IO (Set.Set String) -> IO (Set.Set String)
cachedGeneratedKeys mode morphisms objects cauchyOnly compute = do
  createDirectoryIfMissing True (generatedCacheDir mode)
  exists <- doesFileExist path
  if exists
    then Set.fromList . filter (not . null) . lines <$> readFile path
    else do
      keys <- compute
      writeFile path (unlines (Set.toAscList keys))
      pure keys
  where
    path = generatedCacheFile mode morphisms objects cauchyOnly

generatedCacheDir :: RepresentativeMode -> FilePath
generatedCacheDir mode =
  ".cat-enum-cache" </> "v4" </> "generated" </> representativeModeName mode

generatedCacheFile :: RepresentativeMode -> Int -> Int -> Bool -> FilePath
generatedCacheFile mode morphisms objects cauchyOnly =
  generatedCacheDir mode
    </> ("cauchy-" ++ boolName cauchyOnly ++ "-morphisms-" ++ show morphisms ++ "-objects-" ++ show objects ++ ".cats")

boolName :: Bool -> String
boolName True = "true"
boolName False = "false"

smallExtraCauchyKeysFromBlocks :: RepresentativeMode -> [ConnectedBlock] -> Int -> Int -> Bool -> Maybe (Set.Set String)
smallExtraCauchyKeysFromBlocks mode blocks morphisms objects cauchyOnly
  | not cauchyOnly = Nothing
  | extra < 3 || extra > 4 = Nothing
  | otherwise =
      Just
        ( Set.fromList
            [ representativeKey mode (disjointUnionCategory cats)
            | cats <- connectedBlockMultisets blocks morphisms objects
            ]
        )
  where
    extra = morphisms - objects

connectedBlocksUpToExtraCached :: Int -> IO [ConnectedBlock]
connectedBlocksUpToExtraCached maxExtra =
  concat <$> traverse connectedBlocksForExtraCached [0 .. maxExtra]

connectedBlocksForExtraCached :: Int -> IO [ConnectedBlock]
connectedBlocksForExtraCached 0 =
  pure [ConnectedBlock 1 1 terminalCategory]
connectedBlocksForExtraCached extra =
  concat
    <$> sequence
      [ do
          cats <- generatedCategoriesForObjectCountCached (objects + extra) objects True
          pure
            [ ConnectedBlock (objects + extra) objects cat
            | cat <- cats
            , isConnectedCategory cat
            ]
      | objects <- [1 .. extra + 1]
      ]

connectedBlockMultisets :: [ConnectedBlock] -> Int -> Int -> [[FiniteCategory]]
connectedBlockMultisets blocks targetMorphisms targetObjects =
  assemble targetMorphisms targetObjects 0
  where
    indexed = zip [0 :: Int ..] blocks

    assemble 0 0 _ = [[]]
    assemble remainingMorphisms remainingObjects start
      | remainingMorphisms <= 0 || remainingObjects <= 0 = []
      | otherwise =
          [ cbCategory block : rest
          | (index, block) <- drop start indexed
          , cbMorphisms block <= remainingMorphisms
          , cbObjects block <= remainingObjects
          , rest <-
              assemble
                (remainingMorphisms - cbMorphisms block)
                (remainingObjects - cbObjects block)
                index
          ]

smallExtraCauchyKeys :: RepresentativeMode -> Int -> Int -> Bool -> Maybe (Set.Set String)
smallExtraCauchyKeys mode morphisms objects cauchyOnly
  | not cauchyOnly = Nothing
  | objects < 1 = Just Set.empty
  | extra < 0 = Just Set.empty
  | extra > 2 = Nothing
  | otherwise =
      Just
        ( Set.fromList
            [ representativeKey mode (disjointUnionCategory (component : replicate remaining terminalCategory))
            | (component, componentObjects) <- oneComponentCases
            , let remaining = objects - componentObjects
            , remaining >= 0
            ]
            `Set.union`
          Set.fromList
            [ representativeKey mode (disjointUnionCategory (left : right : replicate remaining terminalCategory))
            | extra == 2
            , (i, (left, leftObjects)) <- indexedExtraOne
            , (j, (right, rightObjects)) <- indexedExtraOne
            , i <= j
            , let remaining = objects - leftObjects - rightObjects
            , remaining >= 0
            ]
        )
  where
    extra = morphisms - objects
    oneComponentCases =
      case extra of
        0 -> [(terminalCategory, 1)]
        1 -> extraOneConnected
        2 -> extraTwoConnected
        _ -> []
    indexedExtraOne = zip [0 :: Int ..] extraOneConnected

terminalCategory :: FiniteCategory
terminalCategory =
  FiniteCategory
    { fcMorphismCount = 1
    , fcObjectCount = 1
    , fcSources = V.singleton 0
    , fcTargets = V.singleton 0
    , fcIdentities = V.singleton 0
    , fcCompose = V.singleton 0
    }

extraOneConnected :: [(FiniteCategory, Int)]
extraOneConnected =
  [ (groupCategoryOfOrder 2, 1)
  , (parallelArrowCategory 1, 2)
  ]

extraTwoConnected :: [(FiniteCategory, Int)]
extraTwoConnected =
  [ (groupCategoryOfOrder 3, 1)
  , (parallelArrowCategory 2, 2)
  , (oneWayGroupTerminalCategory True, 2)
  , (oneWayGroupTerminalCategory False, 2)
  , (twoObjectIsoGroupoid, 2)
  , (thinCategory 3 [(0, 1), (0, 2)], 3)
  , (thinCategory 3 [(0, 2), (1, 2)], 3)
  ]

groupCategoryOfOrder :: Int -> FiniteCategory
groupCategoryOfOrder order =
  case finiteGroupCategories order of
    [cat] -> cat
    cat:_ -> cat
    [] -> error ("no group category of order " ++ show order)

parallelArrowCategory :: Int -> FiniteCategory
parallelArrowCategory arrowCount =
  FiniteCategory
    { fcMorphismCount = 2 + arrowCount
    , fcObjectCount = 2
    , fcSources = V.fromList (0 : replicate arrowCount 0 ++ [1])
    , fcTargets = V.fromList (0 : replicate arrowCount 1 ++ [1])
    , fcIdentities = V.fromList [0, 1 + arrowCount]
    , fcCompose =
        V.fromList
          [ compose f g
          | f <- [0 .. 1 + arrowCount]
          , g <- [0 .. 1 + arrowCount]
          ]
    }
  where
    target :: Int -> Int
    target f
      | f == 0 = 0
      | f == 1 + arrowCount = 1
      | otherwise = 1
    source :: Int -> Int
    source f
      | f == 0 = 0
      | f == 1 + arrowCount = 1
      | otherwise = 0
    compose f g
      | target f /= source g = -1
      | f == 0 = g
      | g == 1 + arrowCount = f
      | otherwise = -1

oneWayGroupTerminalCategory :: Bool -> FiniteCategory
oneWayGroupTerminalCategory groupFirst =
  categoryFromOneWayProfunctor component0 component1 True prof
  where
    group = groupCategoryOfOrder 2
    component0 = if groupFirst then group else terminalCategory
    component1 = if groupFirst then terminalCategory else group
    prof =
      FiniteProfunctor
        { fpProfile = [1]
        , fpLeftActions = V.replicate (fcMorphismCount component0) [0]
        , fpRightActions = V.replicate (fcMorphismCount component1) [0]
        }

twoObjectIsoGroupoid :: FiniteCategory
twoObjectIsoGroupoid =
  FiniteCategory
    { fcMorphismCount = 4
    , fcObjectCount = 2
    , fcSources = V.fromList [0, 0, 1, 1]
    , fcTargets = V.fromList [0, 1, 0, 1]
    , fcIdentities = V.fromList [0, 3]
    , fcCompose =
        V.fromList
          [ compose f g
          | f <- [0 .. 3]
          , g <- [0 .. 3]
          ]
    }
  where
    source :: Int -> Int
    source = ([0, 0, 1, 1] !!)
    target :: Int -> Int
    target = ([0, 1, 0, 1] !!)
    compose f g
      | target f /= source g = -1
      | f == 0 || f == 3 = g
      | g == 0 || g == 3 = f
      | f == 1 && g == 2 = 0
      | f == 2 && g == 1 = 3
      | otherwise = -1

thinCategory :: Int -> [(Int, Int)] -> FiniteCategory
thinCategory objectCount comparablePairs =
  FiniteCategory
    { fcMorphismCount = length morphisms
    , fcObjectCount = objectCount
    , fcSources = V.fromList [source | (source, _) <- morphisms]
    , fcTargets = V.fromList [target | (_, target) <- morphisms]
    , fcIdentities =
        V.fromList
          [ morphismIndex (object, object)
          | object <- [0 .. objectCount - 1]
          ]
    , fcCompose =
        V.fromList
          [ compose f g
          | f <- [0 .. length morphisms - 1]
          , g <- [0 .. length morphisms - 1]
          ]
    }
  where
    relation =
      [ (object, object)
      | object <- [0 .. objectCount - 1]
      ]
        ++ comparablePairs
    morphisms =
      [ (source, target)
      | source <- [0 .. objectCount - 1]
      , target <- [0 .. objectCount - 1]
      , (source, target) `elem` relation
      ]
    morphismIndex pair =
      case lookup pair (zip morphisms [0 ..]) of
        Just index -> index
        Nothing -> error "thin morphism missing"
    compose f g =
      let (_, middleLeft) = morphisms !! f
          (middleRight, _) = morphisms !! g
      in if middleLeft == middleRight
           then morphismIndex (fst (morphisms !! f), snd (morphisms !! g))
           else -1

generatedCategoriesForObjectCount :: Int -> Int -> Bool -> [FiniteCategory]
generatedCategoriesForObjectCount n objectCount cauchyOnly =
  concat
    [ runSkeleton cauchyOnly skeleton
    | skeleton <- uniqueSkeletons (generatedSkeletons n objectCount cauchyOnly)
    ]

generatedCategoriesForObjectCountCached :: Int -> Int -> Bool -> IO [FiniteCategory]
generatedCategoriesForObjectCountCached n objectCount cauchyOnly = do
  skeletons <- uniqueSkeletons <$> generatedSkeletonsCached n objectCount cauchyOnly
  pure
    ( concat
        [ runSkeleton cauchyOnly skeleton
        | skeleton <- skeletons
        ]
    )

generatedSkeletons :: Int -> Int -> Bool -> [GeneratedSkeleton]
generatedSkeletons n objectCount cauchyOnly =
  [ GeneratedSkeleton poset components matrix
    | q <- [1 .. objectCount]
    , components <- chooseComponents q n objectCount cauchyOnly
    , let relationBudget = n - sum (map fcMorphismCount components)
    , relationBudget >= 0
    , poset <- quotientPosetsWithBudget (map fcObjectCount components) relationBudget
    , matrix <- skeletonMatrices n poset components
    ]

generatedSkeletonsCached :: Int -> Int -> Bool -> IO [GeneratedSkeleton]
generatedSkeletonsCached n objectCount cauchyOnly = do
  candidates <- componentCandidatesCached cauchyOnly n objectCount
  pure
    [ GeneratedSkeleton poset components matrix
    | q <- [1 .. objectCount]
    , components <- chooseComponentsFrom candidates q n objectCount
    , let relationBudget = n - sum (map fcMorphismCount components)
    , relationBudget >= 0
    , poset <- quotientPosetsWithBudget (map fcObjectCount components) relationBudget
    , matrix <- skeletonMatrices n poset components
    ]

runSkeleton :: Bool -> GeneratedSkeleton -> [FiniteCategory]
runSkeleton cauchyOnly skeleton
  | Just cats <- independentOneObjectProfunctorSkeletonCategories skeleton = cats
  | Just cats <- oneWayProfunctorSkeletonCategories skeleton = cats
  | otherwise =
  case shapeFromHomMatrix objectCount (gsMatrix skeleton) of
    Nothing -> []
    Just shape ->
      case initialTableWithComponents shape (gsComponents skeleton) of
        Nothing -> []
        Just table -> enumerateShapeFromTable cauchyOnly shape table
  where
    objectCount = sum (map fcObjectCount (gsComponents skeleton))

data EdgeProfunctor = EdgeProfunctor
  { epSource :: !Int
  , epTarget :: !Int
  , epOffset :: !Int
  , epProfunctor :: !FiniteProfunctor
  } deriving (Eq, Show)

independentOneObjectProfunctorSkeletonCategories :: GeneratedSkeleton -> Maybe [FiniteCategory]
independentOneObjectProfunctorSkeletonCategories skeleton
  | not (all ((== 1) . fcObjectCount) components) = Nothing
  | not diagonalMatchesComponents = Nothing
  | hasOffDiagonalChain = Nothing
  | null edgeSpecs = Nothing
  | otherwise =
      Just
        [ categoryFromIndependentOneObjectProfunctors components edges
        | edgeChoices <- traverse profunctorsForEdge edgeSpecs
        , let edges = assignEdgeOffsets componentMorphisms edgeChoices
        ]
  where
    components = gsComponents skeleton
    matrix = gsMatrix skeleton
    q = length components
    componentMorphisms = sum (map fcMorphismCount components)

    diagonalMatchesComponents =
      and
        [ matrix !! (i * q + i) == fcMorphismCount (components !! i)
        | i <- [0 .. q - 1]
        ]

    edgeSpecs =
      [ (i, j, matrix !! (i * q + j))
      | i <- [0 .. q - 1]
      , j <- [0 .. q - 1]
      , i /= j
      , matrix !! (i * q + j) > 0
      ]

    hasOffDiagonalChain =
      or
        [ matrix !! (i * q + j) > 0 && matrix !! (j * q + k) > 0
        | i <- [0 .. q - 1]
        , j <- [0 .. q - 1]
        , k <- [0 .. q - 1]
        , i /= j
        , j /= k
        , i /= k
        ]

    profunctorsForEdge (i, j, size) =
      [ (i, j, prof)
      | prof <- enumerateProfunctorsForProfile (components !! i) (components !! j) [size]
      ]

assignEdgeOffsets :: Int -> [(Int, Int, FiniteProfunctor)] -> [EdgeProfunctor]
assignEdgeOffsets firstOffset =
  snd . foldl assign (firstOffset, [])
  where
    assign (offset, acc) (source, target, prof) =
      let size =
            case fpProfile prof of
              [profileSize] -> profileSize
              _ -> error "one-object edge profunctor profile must have one entry"
      in ( offset + size
         , acc
            ++ [ EdgeProfunctor
                  { epSource = source
                  , epTarget = target
                  , epOffset = offset
                  , epProfunctor = prof
                  }
               ]
         )

categoryFromIndependentOneObjectProfunctors :: [FiniteCategory] -> [EdgeProfunctor] -> FiniteCategory
categoryFromIndependentOneObjectProfunctors components edges =
  FiniteCategory
    { fcMorphismCount = totalMorphisms
    , fcObjectCount = q
    , fcSources =
        V.fromList
          ( concat
              [ replicate (fcMorphismCount component) componentIndex
              | (componentIndex, component) <- indexedComponents
              ]
              ++ concat
                [ replicate (edgeSize edge) (epSource edge)
                | edge <- edges
                ]
          )
    , fcTargets =
        V.fromList
          ( concat
              [ replicate (fcMorphismCount component) componentIndex
              | (componentIndex, component) <- indexedComponents
              ]
              ++ concat
                [ replicate (edgeSize edge) (epTarget edge)
                | edge <- edges
                ]
          )
    , fcIdentities =
        V.fromList
          [ componentOffsets !! componentIndex + fcIdentities component V.! 0
          | (componentIndex, component) <- indexedComponents
          ]
    , fcCompose =
        V.fromList
          [ composeGlobal f g
          | f <- [0 .. totalMorphisms - 1]
          , g <- [0 .. totalMorphisms - 1]
          ]
    }
  where
    q = length components
    indexedComponents = zip [0 ..] components
    componentOffsets = scanl (+) 0 (map fcMorphismCount components)
    componentMorphisms = sum (map fcMorphismCount components)
    totalMorphisms = componentMorphisms + sum (map edgeSize edges)

    composeGlobal f g =
      case (componentOfMorphism f, componentOfMorphism g, edgeOfMorphism f, edgeOfMorphism g) of
        (Just componentF, Just componentG, _, _)
          | componentF == componentG ->
              let localResult =
                    composeAt
                      (components !! componentF)
                      (f - componentOffsets !! componentF)
                      (g - componentOffsets !! componentG)
              in if localResult < 0 then -1 else componentOffsets !! componentF + localResult
        (Just componentF, _, _, Just edgeG)
          | componentF == epSource edgeG ->
              epOffset edgeG
                + ((fpLeftActions (epProfunctor edgeG) V.! (f - componentOffsets !! componentF)) !! (g - epOffset edgeG))
        (_, Just componentG, Just edgeF, _)
          | componentG == epTarget edgeF ->
              epOffset edgeF
                + ((fpRightActions (epProfunctor edgeF) V.! (g - componentOffsets !! componentG)) !! (f - epOffset edgeF))
        _ -> -1

    componentOfMorphism morphism =
      case [ i | i <- [0 .. q - 1], morphism >= componentOffsets !! i, morphism < componentOffsets !! (i + 1) ] of
        i:_ -> Just i
        [] -> Nothing

    edgeOfMorphism morphism =
      case [ edge | edge <- edges, morphism >= epOffset edge, morphism < epOffset edge + edgeSize edge ] of
        edge:_ -> Just edge
        [] -> Nothing

edgeSize :: EdgeProfunctor -> Int
edgeSize edge =
  case fpProfile (epProfunctor edge) of
    [size] -> size
    _ -> error "one-object edge profunctor profile must have one entry"

oneWayProfunctorSkeletonCategories :: GeneratedSkeleton -> Maybe [FiniteCategory]
oneWayProfunctorSkeletonCategories skeleton =
  case (gsComponents skeleton, gsMatrix skeleton) of
    ([leftComponent, rightComponent], [leftSize, forwardSize, backwardSize, rightSize])
      | fcObjectCount leftComponent == 1
      , fcObjectCount rightComponent == 1
      , leftSize == fcMorphismCount leftComponent
      , rightSize == fcMorphismCount rightComponent
      , forwardSize > 0
      , backwardSize == 0 ->
          Just
            [ categoryFromOneWayProfunctor leftComponent rightComponent True prof
            | prof <- enumerateProfunctorsForProfile leftComponent rightComponent [forwardSize]
            ]
      | fcObjectCount leftComponent == 1
      , fcObjectCount rightComponent == 1
      , leftSize == fcMorphismCount leftComponent
      , rightSize == fcMorphismCount rightComponent
      , forwardSize == 0
      , backwardSize > 0 ->
          Just
            [ categoryFromOneWayProfunctor leftComponent rightComponent False prof
            | prof <- enumerateProfunctorsForProfile rightComponent leftComponent [backwardSize]
            ]
    _ -> Nothing

categoryFromOneWayProfunctor :: FiniteCategory -> FiniteCategory -> Bool -> FiniteProfunctor -> FiniteCategory
categoryFromOneWayProfunctor component0 component1 forward prof =
  FiniteCategory
    { fcMorphismCount = totalMorphisms
    , fcObjectCount = 2
    , fcSources =
        V.fromList
          ( replicate n0 0
              ++ replicate n1 1
              ++ replicate p crossSource
          )
    , fcTargets =
        V.fromList
          ( replicate n0 0
              ++ replicate n1 1
              ++ replicate p crossTarget
          )
    , fcIdentities =
        V.fromList
          [ fcIdentities component0 V.! 0
          , offset1 + fcIdentities component1 V.! 0
          ]
    , fcCompose =
        V.fromList
          [ composeGlobal f g
          | f <- [0 .. totalMorphisms - 1]
          , g <- [0 .. totalMorphisms - 1]
          ]
    }
  where
    n0 = fcMorphismCount component0
    n1 = fcMorphismCount component1
    p =
      case fpProfile prof of
        [size] -> size
        _ -> error "one-way profunctor profile must have one entry"
    offset1 = n0
    offsetCross = n0 + n1
    totalMorphisms = n0 + n1 + p
    crossSource = if forward then 0 else 1
    crossTarget = if forward then 1 else 0

    composeGlobal f g
      | inComponent0 f && inComponent0 g =
          composeComponent component0 0 f g
      | inComponent1 f && inComponent1 g =
          composeComponent component1 offset1 (f - offset1) (g - offset1)
      | forward && inComponent0 f && inCross g =
          offsetCross + ((fpLeftActions prof V.! f) !! (g - offsetCross))
      | forward && inCross f && inComponent1 g =
          offsetCross + ((fpRightActions prof V.! (g - offset1)) !! (f - offsetCross))
      | not forward && inComponent1 f && inCross g =
          offsetCross + ((fpLeftActions prof V.! (f - offset1)) !! (g - offsetCross))
      | not forward && inCross f && inComponent0 g =
          offsetCross + ((fpRightActions prof V.! g) !! (f - offsetCross))
      | otherwise = -1

    composeComponent component offset f g =
      let result = composeAt component f g
      in if result < 0 then -1 else offset + result

    inComponent0 f = f >= 0 && f < n0
    inComponent1 f = f >= offset1 && f < offsetCross
    inCross f = f >= offsetCross && f < totalMorphisms

uniqueSkeletons :: [GeneratedSkeleton] -> [GeneratedSkeleton]
uniqueSkeletons =
  go Set.empty
  where
    go _ [] = []
    go seen (s:ss)
      | key `Set.member` seen = go seen ss
      | otherwise = s : go (Set.insert key seen) ss
      where
        key = skeletonCanonicalKey s

skeletonCanonicalKey :: GeneratedSkeleton -> String
skeletonCanonicalKey skeleton
  | length connectedClasses > 1 =
      "disconnected{"
        ++ intercalate
          "~"
          ( sort
              [ connectedSkeletonCanonicalKey (restrictSkeleton skeleton classes)
              | classes <- connectedClasses
              ]
          )
        ++ "}"
  | otherwise = connectedSkeletonCanonicalKey skeleton
  where
    connectedClasses = connectedSupportClasses (gsPoset skeleton)

connectedSkeletonCanonicalKey :: GeneratedSkeleton -> String
connectedSkeletonCanonicalKey skeleton =
  minimum
    [ skeletonKeyForPermutation skeleton p
    | p <- permutations [0 .. q - 1]
    ]
  where
    q = length (gsComponents skeleton)

skeletonKeyForPermutation :: GeneratedSkeleton -> [Int] -> String
skeletonKeyForPermutation skeleton oldForNewClass =
  intercalate
    "|"
    [ intercalate "#" componentKeys
    , boolCsv relation
    , intCsv matrix
    ]
  where
    q = length (gsComponents skeleton)
    objectCount = sum (map fcObjectCount (gsComponents skeleton))
    relation =
      [ supportAt (gsPoset skeleton) (oldForNewClass !! i) (oldForNewClass !! j)
      | i <- [0 .. q - 1]
      , j <- [0 .. q - 1]
      ]
    componentKeys =
      [ categoryKey (gsComponents skeleton !! oldClass)
      | oldClass <- oldForNewClass
      ]
    oldOffsets = objectOffsets (gsComponents skeleton)
    oldObjectOrder =
      concat
        [ [ oldOffsets !! oldClass .. oldOffsets !! oldClass + fcObjectCount (gsComponents skeleton !! oldClass) - 1]
        | oldClass <- oldForNewClass
        ]
    matrix =
      [ gsMatrix skeleton !! (oldX * objectCount + oldY)
      | oldX <- oldObjectOrder
      , oldY <- oldObjectOrder
      ]

connectedSupportClasses :: SupportPreorder -> [[Int]]
connectedSupportClasses support =
  go [0 .. supportObjectCount support - 1] []
  where
    go [] acc = reverse acc
    go (x:xs) acc =
      let cls = sort (reachable [x] [])
          rest = [y | y <- xs, y `notElem` cls]
      in go rest (cls : acc)

    reachable [] seen = seen
    reachable (x:xs) seen
      | x `elem` seen = reachable xs seen
      | otherwise = reachable (neighbors x ++ xs) (x : seen)

    neighbors x =
      [ y
      | y <- [0 .. supportObjectCount support - 1]
      , y /= x
      , supportAt support x y || supportAt support y x
      ]

restrictSkeleton :: GeneratedSkeleton -> [Int] -> GeneratedSkeleton
restrictSkeleton skeleton classes =
  GeneratedSkeleton
    { gsPoset =
        SupportPreorder
          (length classes)
          ( V.fromList
              [ supportAt (gsPoset skeleton) oldSource oldTarget
              | oldSource <- classes
              , oldTarget <- classes
              ]
          )
    , gsComponents = [gsComponents skeleton !! classIndex | classIndex <- classes]
    , gsMatrix =
        [ oldMatrix !! (oldSourceObject * oldObjectCount + oldTargetObject)
        | oldSourceObject <- oldObjects
        , oldTargetObject <- oldObjects
        ]
    }
  where
    oldMatrix = gsMatrix skeleton
    oldObjectCount = sum (map fcObjectCount (gsComponents skeleton))
    offsets = objectOffsets (gsComponents skeleton)
    oldObjects =
      concat
        [ [ offsets !! classIndex .. offsets !! classIndex + fcObjectCount (gsComponents skeleton !! classIndex) - 1]
        | classIndex <- classes
        ]

boolCsv :: [Bool] -> String
boolCsv = intCsv . map (\b -> if b then 1 else 0)

intCsv :: [Int] -> String
intCsv = intercalate "," . map show

skeletonMatrices :: Int -> SupportPreorder -> [FiniteCategory] -> [[Int]]
skeletonMatrices n poset components =
  [ matrixFromExtras extras
  | let componentMorphisms = sum (map fcMorphismCount components)
  , let baseOff = length offPairs
  , let remaining = n - componentMorphisms - baseOff
  , remaining >= 0
  , extras <- compositions remaining baseOff
  ]
  where
    offsets = objectOffsets components
    objectCount = sum (map fcObjectCount components)
    classOfObject =
      [ classIndex
      | (classIndex, component) <- zip [0 ..] components
      , _ <- [0 .. fcObjectCount component - 1]
      ]
    localObject global =
      global - offsets !! (classOfObject !! global)
    offPairs =
      [ (x, y)
      | x <- [0 .. objectCount - 1]
      , y <- [0 .. objectCount - 1]
      , let cx = classOfObject !! x
      , let cy = classOfObject !! y
      , cx /= cy
      , supportAt poset cx cy
      ]
    extraFor extras pair =
      case lookup pair (zip offPairs extras) of
        Just extra -> extra
        Nothing -> 0
    matrixFromExtras extras =
      [ cell extras x y
      | x <- [0 .. objectCount - 1]
      , y <- [0 .. objectCount - 1]
      ]
    cell extras x y
      | cx == cy = length (homMorphisms component lx ly)
      | supportAt poset cx cy = 1 + extraFor extras (x, y)
      | otherwise = 0
      where
        cx = classOfObject !! x
        cy = classOfObject !! y
        component = components !! cx
        lx = localObject x
        ly = localObject y

initialTableWithComponents :: Shape -> [FiniteCategory] -> Maybe (V.Vector Int)
initialTableWithComponents shape components =
  foldl applyFixed (Just (initialTableForShape shape)) fixedCells
  where
    mappings = componentMorphismsInShape shape components
    fixedCells =
      concat
        [ [ (pairIndex globalN gf gg, mappedResult mapping localResult)
          | f <- [0 .. fcMorphismCount component - 1]
          , g <- [0 .. fcMorphismCount component - 1]
          , let gf = mappedResult mapping f
          , let gg = mappedResult mapping g
          , let localResult = composeAt component f g
          , localResult >= 0
          ]
        | (component, mapping) <- zip components mappings
        ]
    globalN = shapeMorphismCount shape

    applyFixed Nothing _ = Nothing
    applyFixed (Just table) (idx, value) =
      let old = table V.! idx
      in if old == -2 || old == value
           then Just (table V.// [(idx, value)])
           else Nothing

componentMorphismsInShape :: Shape -> [FiniteCategory] -> [V.Vector Int]
componentMorphismsInShape shape components =
  snd $
    foldl
      step
      (0, [])
      components
  where
    step (objectOffset, acc) component =
      let mapping = localToGlobalMorphism shape objectOffset component
      in (objectOffset + fcObjectCount component, acc ++ [mapping])

localToGlobalMorphism :: Shape -> Int -> FiniteCategory -> V.Vector Int
localToGlobalMorphism shape objectOffset component =
  V.fromList
    [ globalFor local
    | local <- [0 .. fcMorphismCount component - 1]
    ]
  where
    globalFor local =
      case lookup local localGlobalPairs of
        Just global -> global
        Nothing -> error "component morphism was not mapped into global shape"
    localGlobalPairs =
      concat
        [ zip localBlock globalBlock
        | source <- [0 .. fcObjectCount component - 1]
        , target <- [0 .. fcObjectCount component - 1]
        , let localBlock = homMorphisms component source target
        , let globalBlock = blockAt shape (objectOffset + source) (objectOffset + target)
        ]

mappedResult :: V.Vector Int -> Int -> Int
mappedResult mapping local = mapping V.! local

quotientPosetsWithBudget :: [Int] -> Int -> [SupportPreorder]
quotientPosetsWithBudget classSizes maxOffPairs =
  [ SupportPreorder q (V.fromList relation)
  | (relation, _) <- boundedLabelledPosetRelations classSizes maxOffPairs
  ]
  where
    q = length classSizes

boundedLabelledPosetRelations :: [Int] -> Int -> [([Bool], Int)]
boundedLabelledPosetRelations classSizes maxOffPairs =
  extend 0 [] 0
  where
    q = length classSizes

    extend currentSize relation offPairs
      | currentSize == q = [(relation, offPairs)]
      | otherwise =
          [ result
          | lower <- subsets [0 .. currentSize - 1]
          , isDownSet relation currentSize lower
          , upper <- subsets [0 .. currentSize - 1]
          , isUpSet relation currentSize upper
          , null (intersectList lower upper)
          , all (\l -> all (relationAt relation currentSize l) upper) lower
          , let added = addedOffPairs currentSize lower upper
          , offPairs + added <= maxOffPairs
          , result <- extend (currentSize + 1) (extendRelation relation lower upper) (offPairs + added)
          ]

    addedOffPairs new lower upper =
      let newSize = classSizes !! new
          lowerSize = sum [classSizes !! i | i <- lower]
          upperSize = sum [classSizes !! i | i <- upper]
      in newSize * (lowerSize + upperSize)

extendRelation :: [Bool] -> [Int] -> [Int] -> [Bool]
extendRelation old lower upper =
  [ cell i j
  | i <- [0 .. newSize - 1]
  , j <- [0 .. newSize - 1]
  ]
  where
    oldSize = relationSize old
    newSize = oldSize + 1
    new = oldSize
    cell i j
      | i < new && j < new = relationAt old oldSize i j
      | i == new && j == new = True
      | j == new = i `elem` lower
      | i == new = j `elem` upper
      | otherwise = False

isDownSet :: [Bool] -> Int -> [Int] -> Bool
isDownSet relation currentSize xs =
  all
    ( \x ->
        all
          ( \y ->
              not (relationAt relation currentSize y x) || y `elem` xs
          )
          [0 .. currentSize - 1]
    )
    xs

isUpSet :: [Bool] -> Int -> [Int] -> Bool
isUpSet relation currentSize xs =
  all
    ( \x ->
        all
          ( \y ->
              not (relationAt relation currentSize x y) || y `elem` xs
          )
          [0 .. currentSize - 1]
    )
    xs

relationAt :: [Bool] -> Int -> Int -> Int -> Bool
relationAt relation size i j = relation !! (i * size + j)

relationSize :: [Bool] -> Int
relationSize relation = floor (sqrt (fromIntegral (length relation) :: Double))

subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x:xs) =
  let rest = subsets xs
  in rest ++ map (x :) rest

intersectList :: Eq a => [a] -> [a] -> [a]
intersectList xs ys = [x | x <- xs, x `elem` ys]

chooseComponents :: Int -> Int -> Int -> Bool -> [[FiniteCategory]]
chooseComponents q maxMorphisms objectCount cauchyOnly =
  chooseComponentsFrom candidates q maxMorphisms objectCount
  where
    candidates = componentCandidates cauchyOnly maxMorphisms objectCount

chooseComponentsFrom :: [FiniteCategory] -> Int -> Int -> Int -> [[FiniteCategory]]
chooseComponentsFrom candidates q maxMorphisms objectCount =
  choose q maxMorphisms objectCount
  where
    choose 0 _ remainingObjects =
      if remainingObjects == 0 then [[]] else []
    choose count remainingMorphisms remainingObjects =
      [ cat : rest
      | cat <- candidates
      , let morphisms = fcMorphismCount cat
      , let objects = fcObjectCount cat
      , morphisms <= remainingMorphisms
      , objects <= remainingObjects
      , remainingObjects - objects >= count - 1
      , remainingMorphisms - morphisms >= count - 1
      , rest <- choose (count - 1) (remainingMorphisms - morphisms) (remainingObjects - objects)
      ]

componentCandidates :: Bool -> Int -> Int -> [FiniteCategory]
componentCandidates cauchyOnly maxMorphisms maxObjects
  | maxMorphisms < 1 || maxObjects < 1 = []
  | cauchyOnly = cauchyComponentCandidateCache !! maxMorphisms !! boundedObjects
  | otherwise = allComponentCandidateCache !! maxMorphisms !! boundedObjects
  where
    boundedObjects = min maxObjects maxMorphisms

cauchyComponentCandidateCache :: [[[FiniteCategory]]]
cauchyComponentCandidateCache =
  [ [ componentCandidatesUncached True maxMorphisms maxObjects
    | maxObjects <- [0 .. maxMorphisms]
    ]
  | maxMorphisms <- [0 ..]
  ]

allComponentCandidateCache :: [[[FiniteCategory]]]
allComponentCandidateCache =
  [ [ componentCandidatesUncached False maxMorphisms maxObjects
    | maxObjects <- [0 .. maxMorphisms]
    ]
  | maxMorphisms <- [0 ..]
  ]

componentCandidatesUncached :: Bool -> Int -> Int -> [FiniteCategory]
componentCandidatesUncached cauchyOnly maxMorphisms maxObjects =
  [ cat
  | m <- [1 .. maxMorphisms]
  , k <- [1 .. min maxObjects m]
  , (_, cats) <- biconnectedCanonicalCategories m (Just k) cauchyOnly
  , cat <- cats
  ]

componentCandidatesCached :: Bool -> Int -> Int -> IO [FiniteCategory]
componentCandidatesCached cauchyOnly maxMorphisms maxObjects =
  concat
    <$> sequence
      [ do
          groups <- biconnectedCanonicalCategoriesCached m (Just k) cauchyOnly
          pure (concatMap snd groups)
      | m <- [1 .. maxMorphisms]
      , k <- [1 .. min maxObjects m]
      ]

objectOffsets :: [FiniteCategory] -> [Int]
objectOffsets components =
  scanl (+) 0 (map fcObjectCount components)

pairIndex :: Int -> Int -> Int -> Int
pairIndex n f g = f * n + g

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
