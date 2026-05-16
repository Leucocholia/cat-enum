module CodexSlop.Profunctor
  ( FiniteProfunctor(..)
  , countProfunctorsForProfile
  , countProfunctorsForProfileCached
  , countProfunctorsOfSize
  , enumerateProfunctorsForProfile
  , profunctorCountsUpTo
  , profunctorCountsUpToCached
  ) where

import CodexSlop.Canonical (canonicalKey)
import CodexSlop.Category
import CodexSlop.Decompose

import Control.Monad (foldM)
import Data.Bits (xor)
import Data.Char (ord)
import Data.List (intercalate, sort)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import qualified Data.Vector as V
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((</>))

data FiniteProfunctor = FiniteProfunctor
  { fpProfile :: ![Int]
  , fpLeftActions :: !(V.Vector [Int])
  , fpRightActions :: !(V.Vector [Int])
  } deriving (Eq, Ord, Show)

profunctorCountsUpTo :: Int -> FiniteCategory -> FiniteCategory -> [(Int, Integer)]
profunctorCountsUpTo maxElements left right =
  case componentPairs of
    [_] -> directProfunctorCountsUpTo maxElements left right
    _ ->
      convolveMany maxElements
        [ profunctorCountsUpTo maxElements leftComponent rightComponent
        | (leftComponent, rightComponent) <- componentPairs
        ]
  where
    componentPairs =
      [ (leftComponent, rightComponent)
      | leftComponent <- disjointUnionComponents left
      , rightComponent <- disjointUnionComponents right
      ]

directProfunctorCountsUpTo :: Int -> FiniteCategory -> FiniteCategory -> [(Int, Integer)]
directProfunctorCountsUpTo maxElements left right =
  [ (size, countProfunctorsOfSize left right size)
  | size <- [0 .. maxElements]
  ]

profunctorCountsUpToCached :: Int -> FiniteCategory -> FiniteCategory -> IO [(Int, Integer)]
profunctorCountsUpToCached maxElements left right =
  case componentPairs of
    [_] ->
      sequence
        [ do
            count <- countProfunctorsOfSizeCached left right size
            pure (size, count)
        | size <- [0 .. maxElements]
        ]
    _ -> do
      componentCounts <-
        sequence
          [ profunctorCountsUpToCached maxElements leftComponent rightComponent
          | (leftComponent, rightComponent) <- componentPairs
          ]
      pure (convolveMany maxElements componentCounts)
  where
    componentPairs =
      [ (leftComponent, rightComponent)
      | leftComponent <- disjointUnionComponents left
      , rightComponent <- disjointUnionComponents right
      ]

countProfunctorsOfSize :: FiniteCategory -> FiniteCategory -> Int -> Integer
countProfunctorsOfSize left right total =
  fromMaybe 0 (lookup total (countProfunctorsDirectOrFactored total left right))

countProfunctorsOfSizeCached :: FiniteCategory -> FiniteCategory -> Int -> IO Integer
countProfunctorsOfSizeCached left right total =
  sum
    <$> sequence
      [ countProfunctorsForProfileCached left right profile
      | profile <- compositions total (fcObjectCount left * fcObjectCount right)
      ]

countProfunctorsDirectOrFactored :: Int -> FiniteCategory -> FiniteCategory -> [(Int, Integer)]
countProfunctorsDirectOrFactored maxElements left right =
  case componentPairs of
    [_] -> directCounts
    _ ->
      convolveMany maxElements
        [ profunctorCountsUpTo maxElements leftComponent rightComponent
        | (leftComponent, rightComponent) <- componentPairs
        ]
  where
    componentPairs =
      [ (leftComponent, rightComponent)
      | leftComponent <- disjointUnionComponents left
      , rightComponent <- disjointUnionComponents right
      ]
    directCounts =
      [ (size, directCountProfunctorsOfSize left right size)
      | size <- [0 .. maxElements]
      ]

directCountProfunctorsOfSize :: FiniteCategory -> FiniteCategory -> Int -> Integer
directCountProfunctorsOfSize left right total =
  sum
    [ countProfunctorsForProfile left right profile
    | profile <- compositions total (fcObjectCount left * fcObjectCount right)
    ]

countProfunctorsForProfile :: FiniteCategory -> FiniteCategory -> [Int] -> Integer
countProfunctorsForProfile left right profile
  | length profile /= objectPairs = 0
  | length leftComponents > 1 || length rightComponents > 1 =
      product
        [ countProfunctorsForProfile
            (componentCategory left leftComponentObjects)
            (componentCategory right rightComponentObjects)
            [ profileAt a b
            | a <- leftComponentObjects
            , b <- rightComponentObjects
            ]
        | leftComponentObjects <- leftComponents
        , rightComponentObjects <- rightComponents
        ]
  | otherwise =
      case propagate initialActions of
        Nothing -> 0
        Just actions0 -> search actions0
  where
    leftComponents = connectedObjectComponents left
    rightComponents = connectedObjectComponents right
    leftObjects = fcObjectCount left
    rightObjects = fcObjectCount right
    leftMorphisms = fcMorphismCount left
    rightMorphisms = fcMorphismCount right
    objectPairs = leftObjects * rightObjects
    leftActionCount = leftMorphisms * rightObjects
    actionCount = leftActionCount + leftObjects * rightMorphisms

    initialActions =
      V.fromList
        [ initialAction action
        | action <- [0 .. actionCount - 1]
        ]

    initialAction action
      | isIdentityAction action = Just [0 .. actionDomainSize action - 1]
      | otherwise = Nothing

    search actions =
      case chooseAction actions of
        Nothing -> 1
        Just action ->
          sum
            [ maybe 0 search (assignAndPropagate actions action fn)
            | fn <- functionChoices (actionDomainSize action) (actionCodomainSize action)
            ]

    chooseAction actions =
      case unknowns of
        [] -> Nothing
        _ -> Just (foldl1 better unknowns)
      where
        unknowns = [action | action <- [0 .. actionCount - 1], actions V.! action == Nothing]
        better f g
          | functionCount f <= functionCount g = f
          | otherwise = g
        functionCount action =
          let domainSize = actionDomainSize action
              codomainSize = actionCodomainSize action
          in if domainSize == 0
               then 1
               else if codomainSize == 0
                 then 0
                 else codomainSize ^ domainSize

    assignAndPropagate actions action fn = do
      actions' <- setAction actions action fn
      propagate actions'

    propagate actions = do
      (afterLeft, leftChanged) <- foldM propagateLeftComposition (actions, False) leftCompositionConstraints
      (afterRight, rightChanged) <- foldM propagateRightComposition (afterLeft, False) rightCompositionConstraints
      (afterMiddle, middleChanged) <- foldM checkMiddleInterchange (afterRight, False) middleInterchangeConstraints
      if leftChanged || rightChanged || middleChanged
        then propagate afterMiddle
        else Just afterMiddle

    propagateLeftComposition (actions, changed) (f, g, b) =
      let fg = composeAt left f g
          lf = leftActionIndex f b
          lg = leftActionIndex g b
          lfg = leftActionIndex fg b
      in case (actions V.! lf, actions V.! lg, actions V.! lfg) of
           (Just ff, Just gg, _) -> do
             let forced = composeFunctions gg ff
             actions' <- setAction actions lfg forced
             Just (actions', changed || actions' /= actions)
           (_, _, _) -> Just (actions, changed)

    propagateRightComposition (actions, changed) (a, g, h) =
      let gh = composeAt right g h
          rg = rightActionIndex a g
          rh = rightActionIndex a h
          rgh = rightActionIndex a gh
      in case (actions V.! rg, actions V.! rh, actions V.! rgh) of
           (Just gg, Just hh, _) -> do
             let forced = composeFunctions gg hh
             actions' <- setAction actions rgh forced
             Just (actions', changed || actions' /= actions)
           (_, _, _) -> Just (actions, changed)

    checkMiddleInterchange (actions, changed) (f, h) =
      let x = fcSources left V.! f
          y = fcTargets left V.! f
          b = fcSources right V.! h
          b' = fcTargets right V.! h
          leftThenRight =
            ( leftActionIndex f b
            , rightActionIndex x h
            )
          rightThenLeft =
            ( rightActionIndex y h
            , leftActionIndex f b'
            )
      in case
           ( actions V.! fst leftThenRight
           , actions V.! snd leftThenRight
           , actions V.! fst rightThenLeft
           , actions V.! snd rightThenLeft
           )
         of
           (Just lb, Just rx, Just ry, Just lb') ->
             if composeFunctions lb rx == composeFunctions ry lb'
               then Just (actions, changed)
               else Nothing
           _ -> Just (actions, changed)

    setAction actions action fn
      | not (wellTyped action fn) = Nothing
      | otherwise =
          case actions V.! action of
            Nothing -> Just (actions V.// [(action, Just fn)])
            Just old
              | old == fn -> Just actions
              | otherwise -> Nothing

    wellTyped action fn =
      length fn == actionDomainSize action
        && all (\x -> x >= 0 && x < actionCodomainSize action) fn

    isIdentityAction action =
      case decodeAction action of
        Left (f, _) -> isIdentity left f
        Right (_, g) -> isIdentity right g

    actionDomainSize action =
      case decodeAction action of
        Left (f, b) -> profileAt (fcTargets left V.! f) b
        Right (a, g) -> profileAt a (fcSources right V.! g)

    actionCodomainSize action =
      case decodeAction action of
        Left (f, b) -> profileAt (fcSources left V.! f) b
        Right (a, g) -> profileAt a (fcTargets right V.! g)

    decodeAction action
      | action < leftActionCount =
          let (f, b) = action `divMod` rightObjects
          in Left (f, b)
      | otherwise =
          let (a, g) = (action - leftActionCount) `divMod` rightMorphisms
          in Right (a, g)

    leftActionIndex f b = f * rightObjects + b
    rightActionIndex a g = leftActionCount + a * rightMorphisms + g
    profileAt a b = profile !! (a * rightObjects + b)

    leftCompositionConstraints =
      [ (f, g, b)
      | f <- [0 .. leftMorphisms - 1]
      , g <- [0 .. leftMorphisms - 1]
      , isComposable left f g
      , b <- [0 .. rightObjects - 1]
      ]

    rightCompositionConstraints =
      [ (a, g, h)
      | a <- [0 .. leftObjects - 1]
      , g <- [0 .. rightMorphisms - 1]
      , h <- [0 .. rightMorphisms - 1]
      , isComposable right g h
      ]

    middleInterchangeConstraints =
      [ (f, h)
      | f <- [0 .. leftMorphisms - 1]
      , h <- [0 .. rightMorphisms - 1]
      ]

enumerateProfunctorsForProfile :: FiniteCategory -> FiniteCategory -> [Int] -> [FiniteProfunctor]
enumerateProfunctorsForProfile left right profile
  | length profile /= objectPairs = []
  | Just profunctors <- enumerateOneObjectGroupProfunctors left right profile = profunctors
  | length leftComponents > 1 || length rightComponents > 1 =
      error "enumerateProfunctorsForProfile currently expects connected inputs"
  | otherwise =
      case propagate initialActions of
        Nothing -> []
        Just actions0 -> map materialize (search actions0)
  where
    leftComponents = connectedObjectComponents left
    rightComponents = connectedObjectComponents right
    leftObjects = fcObjectCount left
    rightObjects = fcObjectCount right
    leftMorphisms = fcMorphismCount left
    rightMorphisms = fcMorphismCount right
    objectPairs = leftObjects * rightObjects
    leftActionCount = leftMorphisms * rightObjects
    actionCount = leftActionCount + leftObjects * rightMorphisms

    initialActions =
      V.fromList
        [ initialAction action
        | action <- [0 .. actionCount - 1]
        ]

    initialAction action
      | isIdentityAction action = Just [0 .. actionDomainSize action - 1]
      | otherwise = Nothing

    search actions =
      case chooseAction actions of
        Nothing -> [actions]
        Just action ->
          concat
            [ maybe [] search (assignAndPropagate actions action fn)
            | fn <- functionChoices (actionDomainSize action) (actionCodomainSize action)
            ]

    chooseAction actions =
      case unknowns of
        [] -> Nothing
        _ -> Just (foldl1 better unknowns)
      where
        unknowns = [action | action <- [0 .. actionCount - 1], actions V.! action == Nothing]
        better f g
          | functionCount f <= functionCount g = f
          | otherwise = g
        functionCount action =
          let domainSize = actionDomainSize action
              codomainSize = actionCodomainSize action
          in if domainSize == 0
               then 1
               else if codomainSize == 0
                 then 0
                 else codomainSize ^ domainSize

    assignAndPropagate actions action fn = do
      actions' <- setAction actions action fn
      propagate actions'

    propagate actions = do
      (afterLeft, leftChanged) <- foldM propagateLeftComposition (actions, False) leftCompositionConstraints
      (afterRight, rightChanged) <- foldM propagateRightComposition (afterLeft, False) rightCompositionConstraints
      (afterMiddle, middleChanged) <- foldM checkMiddleInterchange (afterRight, False) middleInterchangeConstraints
      if leftChanged || rightChanged || middleChanged
        then propagate afterMiddle
        else Just afterMiddle

    propagateLeftComposition (actions, changed) (f, g, b) =
      let fg = composeAt left f g
          lf = leftActionIndex f b
          lg = leftActionIndex g b
          lfg = leftActionIndex fg b
      in case (actions V.! lf, actions V.! lg, actions V.! lfg) of
           (Just ff, Just gg, _) -> do
             let forced = composeFunctions gg ff
             actions' <- setAction actions lfg forced
             Just (actions', changed || actions' /= actions)
           _ -> Just (actions, changed)

    propagateRightComposition (actions, changed) (a, g, h) =
      let gh = composeAt right g h
          rg = rightActionIndex a g
          rh = rightActionIndex a h
          rgh = rightActionIndex a gh
      in case (actions V.! rg, actions V.! rh, actions V.! rgh) of
           (Just gg, Just hh, _) -> do
             let forced = composeFunctions gg hh
             actions' <- setAction actions rgh forced
             Just (actions', changed || actions' /= actions)
           _ -> Just (actions, changed)

    checkMiddleInterchange (actions, changed) (f, h) =
      let x = fcSources left V.! f
          y = fcTargets left V.! f
          b = fcSources right V.! h
          b' = fcTargets right V.! h
          leftThenRight = (leftActionIndex f b, rightActionIndex x h)
          rightThenLeft = (rightActionIndex y h, leftActionIndex f b')
      in case
           ( actions V.! fst leftThenRight
           , actions V.! snd leftThenRight
           , actions V.! fst rightThenLeft
           , actions V.! snd rightThenLeft
           )
         of
           (Just lb, Just rx, Just ry, Just lb') ->
             if composeFunctions lb rx == composeFunctions ry lb'
               then Just (actions, changed)
               else Nothing
           _ -> Just (actions, changed)

    setAction actions action fn
      | not (wellTyped action fn) = Nothing
      | otherwise =
          case actions V.! action of
            Nothing -> Just (actions V.// [(action, Just fn)])
            Just old
              | old == fn -> Just actions
              | otherwise -> Nothing

    wellTyped action fn =
      length fn == actionDomainSize action
        && all (\x -> x >= 0 && x < actionCodomainSize action) fn

    isIdentityAction action =
      case decodeAction action of
        Left (f, _) -> isIdentity left f
        Right (_, g) -> isIdentity right g

    actionDomainSize action =
      case decodeAction action of
        Left (f, b) -> profileAt (fcTargets left V.! f) b
        Right (a, g) -> profileAt a (fcSources right V.! g)

    actionCodomainSize action =
      case decodeAction action of
        Left (f, b) -> profileAt (fcSources left V.! f) b
        Right (a, g) -> profileAt a (fcTargets right V.! g)

    decodeAction action
      | action < leftActionCount =
          let (f, b) = action `divMod` rightObjects
          in Left (f, b)
      | otherwise =
          let (a, g) = (action - leftActionCount) `divMod` rightMorphisms
          in Right (a, g)

    leftActionIndex f b = f * rightObjects + b
    rightActionIndex a g = leftActionCount + a * rightMorphisms + g
    profileAt a b = profile !! (a * rightObjects + b)

    leftCompositionConstraints =
      [ (f, g, b)
      | f <- [0 .. leftMorphisms - 1]
      , g <- [0 .. leftMorphisms - 1]
      , isComposable left f g
      , b <- [0 .. rightObjects - 1]
      ]

    rightCompositionConstraints =
      [ (a, g, h)
      | a <- [0 .. leftObjects - 1]
      , g <- [0 .. rightMorphisms - 1]
      , h <- [0 .. rightMorphisms - 1]
      , isComposable right g h
      ]

    middleInterchangeConstraints =
      [ (f, h)
      | f <- [0 .. leftMorphisms - 1]
      , h <- [0 .. rightMorphisms - 1]
      ]

    materialize actions =
      FiniteProfunctor
        { fpProfile = profile
        , fpLeftActions =
            V.fromList
              [ actionValue actions (leftActionIndex f b)
              | f <- [0 .. leftMorphisms - 1]
              , b <- [0 .. rightObjects - 1]
              ]
        , fpRightActions =
            V.fromList
              [ actionValue actions (rightActionIndex a g)
              | a <- [0 .. leftObjects - 1]
              , g <- [0 .. rightMorphisms - 1]
              ]
        }

    actionValue actions action =
      case actions V.! action of
        Just fn -> fn
        Nothing -> error "profunctor action was not assigned"

enumerateOneObjectGroupProfunctors :: FiniteCategory -> FiniteCategory -> [Int] -> Maybe [FiniteProfunctor]
enumerateOneObjectGroupProfunctors left right [size]
  | isOneObjectGroupCategory left && isOneObjectGroupCategory right =
      Just
        [ profunctorFromOrbitMultiset left right group orbitMultiset size
        | orbitMultiset <- orbitMultisets size transitiveOrbits
        ]
  where
    group = productGroupTable left right
    transitiveOrbits =
      sort
        [ (groupOrder group `div` length subgroup, subgroup)
        | subgroup <- subgroupConjugacyRepresentatives group
        ]
enumerateOneObjectGroupProfunctors _ _ _ = Nothing

data ProductGroup = ProductGroup
  { pgLeftSize :: !Int
  , pgRightSize :: !Int
  , pgOrder :: !Int
  , pgCompose :: !(V.Vector Int)
  , pgInverse :: !(V.Vector Int)
  } deriving (Eq, Show)

groupOrder :: ProductGroup -> Int
groupOrder = pgOrder

productGroupTable :: FiniteCategory -> FiniteCategory -> ProductGroup
productGroupTable left right =
  ProductGroup
    { pgLeftSize = leftSize
    , pgRightSize = rightSize
    , pgOrder = order
    , pgCompose = table
    , pgInverse = inverses
    }
  where
    leftSize = fcMorphismCount left
    rightSize = fcMorphismCount right
    order = leftSize * rightSize
    table =
      V.fromList
        [ encode (composeAt left l l') (composeAt right r' r)
        | element <- [0 .. order - 1]
        , element' <- [0 .. order - 1]
        , let (l, r) = decodeProduct rightSize element
        , let (l', r') = decodeProduct rightSize element'
        ]
    inverses =
      V.fromList
        [ inverseOf table order element
        | element <- [0 .. order - 1]
        ]
    encode l r = l * rightSize + r

productCompose :: ProductGroup -> Int -> Int -> Int
productCompose group x y =
  pgCompose group V.! (x * pgOrder group + y)

decodeProduct :: Int -> Int -> (Int, Int)
decodeProduct rightSize element = element `divMod` rightSize

productElement :: ProductGroup -> Int -> Int -> Int
productElement group l r = l * pgRightSize group + r

inverseOf :: V.Vector Int -> Int -> Int -> Int
inverseOf table order element =
  head
    [ candidate
    | candidate <- [0 .. order - 1]
    , table V.! (element * order + candidate) == 0
    , table V.! (candidate * order + element) == 0
    ]

isOneObjectGroupCategory :: FiniteCategory -> Bool
isOneObjectGroupCategory cat =
  fcObjectCount cat == 1
    && n >= 1
    && V.length (fcIdentities cat) == 1
    && fcIdentities cat V.! 0 == 0
    && V.length (fcSources cat) == n
    && V.length (fcTargets cat) == n
    && V.length (fcCompose cat) == n * n
    && all (== 0) (V.toList (fcSources cat))
    && all (== 0) (V.toList (fcTargets cat))
    && all identityLaw elements
    && all lineIsPermutation rows
    && all lineIsPermutation columns
  where
    n = fcMorphismCount cat
    elements = [0 .. n - 1]
    allElements = Set.fromList elements
    identityLaw x = composeAt cat 0 x == x && composeAt cat x 0 == x
    rows = [[composeAt cat x y | y <- elements] | x <- elements]
    columns = [[composeAt cat x y | x <- elements] | y <- elements]
    lineIsPermutation values = Set.fromList values == allElements

subgroupConjugacyRepresentatives :: ProductGroup -> [[Int]]
subgroupConjugacyRepresentatives group =
  Set.toAscList $
    Set.fromList
      [ canonicalSubgroupConjugate group subgroup
      | subgroup <- allSubgroups group
      ]

allSubgroups :: ProductGroup -> [[Int]]
allSubgroups group =
  go Set.empty [[0]]
  where
    elements = [0 .. pgOrder group - 1]

    go seen [] = Set.toAscList seen
    go seen (subgroup:queue)
      | subgroup `Set.member` seen = go seen queue
      | otherwise =
          let extensions =
                [ subgroupClosure group (generator : subgroup)
                | generator <- elements
                , generator `notElem` subgroup
                ]
          in go (Set.insert subgroup seen) (queue ++ extensions)

subgroupClosure :: ProductGroup -> [Int] -> [Int]
subgroupClosure group generators =
  close (Set.fromList (0 : generators))
  where
    close current =
      let products =
            Set.fromList
              [ productCompose group x y
              | x <- Set.toList current
              , y <- Set.toList current
              ]
          next = Set.union current products
      in if Set.size next == Set.size current
           then Set.toAscList current
           else close next

canonicalSubgroupConjugate :: ProductGroup -> [Int] -> [Int]
canonicalSubgroupConjugate group subgroup =
  minimum
    [ sort
        [ productCompose group (productCompose group g h) (pgInverse group V.! g)
        | h <- subgroup
        ]
    | g <- [0 .. pgOrder group - 1]
    ]

orbitMultisets :: Int -> [(Int, [Int])] -> [[(Int, [Int])]]
orbitMultisets target orbits =
  choose target 0
  where
    indexed = zip [0 :: Int ..] orbits
    choose 0 _ = [[]]
    choose remaining start =
      [ orbit : rest
      | (index, orbit@(orbitSize, _)) <- drop start indexed
      , orbitSize <= remaining
      , rest <- choose (remaining - orbitSize) index
      ]

profunctorFromOrbitMultiset :: FiniteCategory -> FiniteCategory -> ProductGroup -> [(Int, [Int])] -> Int -> FiniteProfunctor
profunctorFromOrbitMultiset left right group orbitMultiset size =
  FiniteProfunctor
    { fpProfile = [size]
    , fpLeftActions =
        V.fromList
          [ actionFor (productElement group leftElement 0)
          | leftElement <- [0 .. fcMorphismCount left - 1]
          ]
    , fpRightActions =
        V.fromList
          [ actionFor (productElement group 0 rightElement)
          | rightElement <- [0 .. fcMorphismCount right - 1]
          ]
    }
  where
    orbitActions = map (cosetActionTable group . snd) orbitMultiset
    offsets = scanl (+) 0 (map (length . V.head) orbitActions)

    actionFor element =
      concat
        [ map (+ offset) (action V.! element)
        | (offset, action) <- zip offsets orbitActions
        ]

cosetActionTable :: ProductGroup -> [Int] -> V.Vector [Int]
cosetActionTable group subgroup =
  V.fromList
    [ actionFor element
    | element <- [0 .. pgOrder group - 1]
    ]
  where
    cosets = rightCosets group subgroup
    representatives = map head cosets

    actionFor element =
      [ cosetIndex (rightCoset group subgroup (productCompose group element representative))
      | representative <- representatives
      ]

    cosetIndex coset =
      case lookup coset (zip cosets [0 ..]) of
        Just index -> index
        Nothing -> error "coset action left the coset space"

rightCosets :: ProductGroup -> [Int] -> [[Int]]
rightCosets group subgroup =
  go [0 .. pgOrder group - 1] []
  where
    go [] acc = reverse acc
    go remaining acc =
      let representative = head remaining
          coset = rightCoset group subgroup representative
          remaining' = filter (`notElem` coset) remaining
      in go remaining' (coset : acc)

rightCoset :: ProductGroup -> [Int] -> Int -> [Int]
rightCoset group subgroup representative =
  sort [productCompose group representative h | h <- subgroup]

countProfunctorsForProfileCached :: FiniteCategory -> FiniteCategory -> [Int] -> IO Integer
countProfunctorsForProfileCached left right profile = do
  createDirectoryIfMissing True profunctorCacheDir
  exists <- doesFileExist path
  if exists
    then do
      cached <- readProfunctorProfileCache path leftKey rightKey profile
      case cached of
        Just count -> pure count
        Nothing -> computeAndWrite
    else computeAndWrite
  where
    leftKey = canonicalKey left
    rightKey = canonicalKey right
    path = profunctorProfileCacheFile leftKey rightKey profile
    computeAndWrite = do
      let count = countProfunctorsForProfile left right profile
      writeProfunctorProfileCache path leftKey rightKey profile count
      pure count

profunctorCacheDir :: FilePath
profunctorCacheDir =
  ".cat-enum-cache" </> "v1" </> "profunctor-counts"

profunctorProfileCacheFile :: String -> String -> [Int] -> FilePath
profunctorProfileCacheFile leftKey rightKey profile =
  profunctorCacheDir </> (show (stableHash payload) ++ ".count")
  where
    payload = leftKey ++ "\n" ++ rightKey ++ "\n" ++ csv profile

writeProfunctorProfileCache :: FilePath -> String -> String -> [Int] -> Integer -> IO ()
writeProfunctorProfileCache path leftKey rightKey profile count =
  writeFile
    path
    ( unlines
        [ "version:1"
        , "left:" ++ leftKey
        , "right:" ++ rightKey
        , "profile:" ++ csv profile
        , "count:" ++ show count
        ]
    )

readProfunctorProfileCache :: FilePath -> String -> String -> [Int] -> IO (Maybe Integer)
readProfunctorProfileCache path leftKey rightKey profile = do
  contents <- readFile path
  let fields =
        [ (name, drop 1 value)
        | line <- lines contents
        , let (name, value) = break (== ':') line
        , not (null value)
        ]
  pure $ do
    version <- lookup "version" fields
    cachedLeft <- lookup "left" fields
    cachedRight <- lookup "right" fields
    cachedProfile <- lookup "profile" fields
    cachedCount <- lookup "count" fields
    if version == "1"
      && cachedLeft == leftKey
      && cachedRight == rightKey
      && cachedProfile == csv profile
      then readMaybeInt cachedCount
      else Nothing

stableHash :: String -> Integer
stableHash =
  foldl step 14695981039346656037
  where
    modulus = 18446744073709551616
    prime = 1099511628211
    step hash char =
      ((hash `xor` fromIntegral (ord char)) * prime) `mod` modulus

csv :: [Int] -> String
csv = intercalate "," . map show

readMaybeInt :: String -> Maybe Integer
readMaybeInt raw =
  case reads raw of
    [(value, "")] -> Just value
    _ -> Nothing

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
