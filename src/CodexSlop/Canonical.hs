module CodexSlop.Canonical
  ( allEqualityKeys
  , canonicalKey
  , dualKey
  , equalityCount
  , equivalenceKey
  , RepresentativeMode(..)
  , representativeKey
  , representativeModeName
  ) where

import CodexSlop.Category

import Data.Bits (xor)
import Data.List (foldl', permutations, sort)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Data.Word (Word64)

data RepresentativeMode
  = UpToEquivalence
  | UpToIsomorphism
  | UpToEquality
  deriving (Eq, Ord, Show)

representativeModeName :: RepresentativeMode -> String
representativeModeName UpToEquivalence = "equivalence"
representativeModeName UpToIsomorphism = "isomorphism"
representativeModeName UpToEquality = "equality"

representativeKey :: RepresentativeMode -> FiniteCategory -> String
representativeKey UpToEquivalence = equivalenceKey
representativeKey UpToIsomorphism = canonicalKey
representativeKey UpToEquality = categoryKey

-- | Quotient by source-target duality: identify C with C^op.
-- The key for C is the minimum of the keys of C and its opposite.
dualKey :: RepresentativeMode -> FiniteCategory -> String
dualKey mode cat = min (representativeKey mode cat) (representativeKey mode (oppositeCategory cat))

-- | The opposite category: swap sources/targets, reverse composition order.
oppositeCategory :: FiniteCategory -> FiniteCategory
oppositeCategory cat =
  FiniteCategory
    { fcMorphismCount = n
    , fcObjectCount   = fcObjectCount cat
    , fcSources       = fcTargets cat
    , fcTargets       = fcSources cat
    , fcIdentities    = fcIdentities cat
    , fcCompose       = V.generate (n * n) (\idx ->
        let (f, g) = idx `divMod` n
        in composeAt cat g f)
    }
  where n = fcMorphismCount cat

allEqualityKeys :: FiniteCategory -> Set.Set String
allEqualityKeys cat
  | k <= 1 = Set.singleton (categoryKey cat)
  | otherwise = Set.fromList
      [ keyForMorphismOrder cat objectOrder (V.toList order)
      | objectOrder <- permutations [0 .. k - 1]
      , let order = concatBlocks blockLookup k objectOrder
      ]
  where
    k = fcObjectCount cat
    n = fcMorphismCount cat
    blockLookup =
      V.fromList
        [ V.fromList
            [ m
            | m <- [0 .. n - 1]
            , fcSources cat V.! m == s
            , fcTargets cat V.! m == t
            ]
        | s <- [0 .. k - 1]
        , t <- [0 .. k - 1]
        ]

concatBlocks :: V.Vector (V.Vector Int) -> Int -> [Int] -> V.Vector Int
concatBlocks blockLookup k oldForNew =
  V.concat
    [ blockLookup V.! (oldForNew !! i * k + oldForNew !! j)
    | i <- [0 .. k - 1]
    , j <- [0 .. k - 1]
    ]

equalityCount :: FiniteCategory -> Int
equalityCount cat
  | k <= 1 = 1
  | otherwise =
      let classes = objectClasses cat
          aut = product (map factorial classes)
      in foldl' (*) 1 [k - i | i <- [0 .. k - 1]] `div` aut
  where
    k = fcObjectCount cat
    n = fcMorphismCount cat

factorial :: Int -> Int
factorial n = foldl' (*) 1 [1 .. n]

-- | Partition objects into equivalence classes under the relation:
-- two objects are equivalent iff swapping them preserves all hom-counts.
-- Under Option A (morphisms within hom-sets indistinguishable), this is
-- exactly the automorphism group under object permutations.
objectClasses :: FiniteCategory -> [Int]
objectClasses cat =
  map length (go (Set.fromList [0 .. k - 1]) [])
  where
    k = fcObjectCount cat
    go remaining acc
      | Set.null remaining = reverse acc
      | otherwise =
          let x = Set.findMin remaining
              cls = Set.filter (sameClass x) remaining
          in go (Set.difference remaining cls) (Set.toList cls : acc)

    sameClass i j =
      hCount i i == hCount j j
      && all (\t -> t /= i && t /= j ==> hCount i t == hCount j t && hCount t i == hCount t j) [0 .. k - 1]

    hCount s t =
      length [f | f <- [0 .. fcMorphismCount cat - 1]
                , fcSources cat V.! f == s
                , fcTargets cat V.! f == t
                ]

infixr 0 ==>
(==>) :: Bool -> Bool -> Bool
True  ==> x = x
False ==> _ = True

canonicalKey :: FiniteCategory -> String
canonicalKey cat
  | isOneObjectGroup cat = canonicalGroupKey cat
  | length connectedComponents > 1 = disconnectedCanonicalKey cat connectedComponents
  | otherwise = exhaustiveCanonicalKey cat
  where
    connectedComponents = connectedObjectComponentsForCanonical cat

equivalenceKey :: FiniteCategory -> String
equivalenceKey =
  canonicalKey . skeletalSubcategory

skeletalSubcategory :: FiniteCategory -> FiniteCategory
skeletalSubcategory cat =
  componentCategoryForCanonical cat representatives
  where
    representatives = map head (objectIsomorphismClasses cat)

objectIsomorphismClasses :: FiniteCategory -> [[Int]]
objectIsomorphismClasses cat =
  go [0 .. fcObjectCount cat - 1] []
  where
    go [] acc = reverse acc
    go (x:xs) acc =
      let cls = sort [y | y <- x : xs, objectsIsomorphic x y]
          rest = [y | y <- xs, y `notElem` cls]
      in go rest (cls : acc)

    objectsIsomorphic x y =
      or
        [ composeAt cat f g == fcIdentities cat V.! x
            && composeAt cat g f == fcIdentities cat V.! y
        | f <- homMorphisms cat x y
        , g <- homMorphisms cat y x
        ]

disconnectedCanonicalKey :: FiniteCategory -> [[Int]] -> String
disconnectedCanonicalKey cat components =
  categoryKey (disjointUnionCategoryForCanonical canonicalComponents)
  where
    canonicalComponents =
      map parseCanonicalComponent $
        sort
          [ canonicalKey (componentCategoryForCanonical cat component)
          | component <- components
          ]
    parseCanonicalComponent key =
      case parseCategoryKey key of
        Right component -> component
        Left err -> error ("internal disconnected canonical parse failure: " ++ err)

exhaustiveCanonicalKey :: FiniteCategory -> String
exhaustiveCanonicalKey cat =
  minimum [keyForObjectOrder objectOrder | objectOrder <- permutations [0 .. k - 1]]
  where
    k = fcObjectCount cat

    keyForObjectOrder oldForNew =
      minimum
        [ keyForMorphismOrder cat oldForNew newToOld
        | newToOld <- morphismOrders oldForNew
        ]

    morphismOrders oldForNew =
      map concat (sequence blockChoices)
      where
        blockChoices =
          [ choicesForBlock (oldForNew !! i) (oldForNew !! j) (i == j)
          | i <- [0 .. k - 1]
          , j <- [0 .. k - 1]
          ]

    choicesForBlock oldSource oldTarget diagonal =
      let block =
            [ m
            | m <- [0 .. fcMorphismCount cat - 1]
            , fcSources cat V.! m == oldSource
            , fcTargets cat V.! m == oldTarget
            ]
      in if diagonal
           then
             let ident = fcIdentities cat V.! oldSource
                 rest = filter (/= ident) block
             in map (ident :) (permutations rest)
           else permutations block

isOneObjectGroup :: FiniteCategory -> Bool
isOneObjectGroup cat =
  fcObjectCount cat == 1
    && n >= 1
    && V.length (fcIdentities cat) == 1
    && fcIdentities cat V.! 0 == 0
    && V.length (fcSources cat) == n
    && V.length (fcTargets cat) == n
    && V.length (fcCompose cat) == n * n
    && all (== 0) (V.toList (fcSources cat))
    && all (== 0) (V.toList (fcTargets cat))
    && all identityLaw morphisms
    && all lineIsPermutation rows
    && all lineIsPermutation columns
  where
    n = fcMorphismCount cat
    morphisms = [0 .. n - 1]
    allMorphisms = Set.fromList morphisms
    identityLaw x =
      composeAt cat 0 x == x && composeAt cat x 0 == x
    rows =
      [ [composeAt cat x y | y <- morphisms]
      | x <- morphisms
      ]
    columns =
      [ [composeAt cat x y | x <- morphisms]
      | y <- morphisms
      ]
    lineIsPermutation values = Set.fromList values == allMorphisms

canonicalGroupKey :: FiniteCategory -> String
canonicalGroupKey cat =
  minimum [keyForMorphismOrder cat [0] order | order <- minimalGeneratorOrders]
  where
    n = fcMorphismCount cat
    nonIdentities = [1 .. n - 1]

    minimalGeneratorOrders =
      head
        [ orders
        | tupleSize <- [0 .. n - 1]
        , let orders =
                [ order
                | generators <- orderedChoices tupleSize nonIdentities
                , let order = generatedOrder cat generators
                , length order == n
                ]
        , not (null orders)
        ]

orderedChoices :: Int -> [Int] -> [[Int]]
orderedChoices 0 _ = [[]]
orderedChoices count values =
  [ value : rest
  | value <- values
  , rest <- orderedChoices (count - 1) (filter (/= value) values)
  ]

generatedOrder :: FiniteCategory -> [Int] -> [Int]
generatedOrder cat generators =
  close [0] (Set.singleton 0)
  where
    close order seen =
      let (order', seen') = foldl addProduct (order, seen) [(x, g) | x <- order, g <- generators]
      in if Set.size seen' == Set.size seen
           then order
           else close order' seen'

    addProduct (order, seen) (x, g) =
      let y = composeAt cat x g
      in if y `Set.member` seen
           then (order, seen)
           else (order ++ [y], Set.insert y seen)

keyForMorphismOrder :: FiniteCategory -> [Int] -> [Int] -> String
keyForMorphismOrder cat oldForNew newToOld =
  categoryKey
    FiniteCategory
      { fcMorphismCount = n
      , fcObjectCount = k
      , fcSources = V.fromList newSources
      , fcTargets = V.fromList newTargets
      , fcIdentities = V.fromList newIdentities
      , fcCompose = V.fromList newCompose
      }
  where
    n = length newToOld
    k = length oldForNew
    newToOldVec = V.fromList newToOld
    oldToNew = V.fromList (invert n newToOld)
    oldObjectToNew = V.fromList (invert k oldForNew)

    oldMorph newMorph = newToOldVec V.! newMorph

    newSources =
      [ oldObjectToNew V.! (fcSources cat V.! oldMorph m)
      | m <- [0 .. n - 1]
      ]
    newTargets =
      [ oldObjectToNew V.! (fcTargets cat V.! oldMorph m)
      | m <- [0 .. n - 1]
      ]
    newIdentities =
      [ oldToNew V.! (fcIdentities cat V.! (oldForNew !! newObject))
      | newObject <- [0 .. k - 1]
      ]
    newCompose =
      [ let result = composeAt cat (oldMorph f) (oldMorph g)
        in if result < 0 then -1 else oldToNew V.! result
      | f <- [0 .. n - 1]
      , g <- [0 .. n - 1]
      ]

invert :: Int -> [Int] -> [Int]
invert size xs =
  [ lookupValue i | i <- [0 .. size - 1] ]
  where
    pairs = zip xs [0 ..]
    lookupValue x =
      case lookup x pairs of
        Just y -> y
        Nothing -> error "invalid permutation"

connectedObjectComponentsForCanonical :: FiniteCategory -> [[Int]]
connectedObjectComponentsForCanonical cat =
  go [0 .. fcObjectCount cat - 1] []
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
      | y <- [0 .. fcObjectCount cat - 1]
      , y /= x
      , supportRelatedForCanonical x y || supportRelatedForCanonical y x
      ]

    supportRelatedForCanonical source target =
      any
        ( \m ->
            fcSources cat V.! m == source
              && fcTargets cat V.! m == target
        )
        [0 .. fcMorphismCount cat - 1]

componentCategoryForCanonical :: FiniteCategory -> [Int] -> FiniteCategory
componentCategoryForCanonical cat objects =
  FiniteCategory
    { fcMorphismCount = length morphisms
    , fcObjectCount = length objectsSorted
    , fcSources = V.fromList [objectNew (fcSources cat V.! m) | m <- morphisms]
    , fcTargets = V.fromList [objectNew (fcTargets cat V.! m) | m <- morphisms]
    , fcIdentities = V.fromList [morphismNew (fcIdentities cat V.! obj) | obj <- objectsSorted]
    , fcCompose =
        V.fromList
          [ let oldResult = composeAt cat oldF oldG
            in if oldResult < 0 then -1 else morphismNew oldResult
          | oldF <- morphisms
          , oldG <- morphisms
          ]
    }
  where
    objectsSorted = sort objects
    morphisms =
      [ m
      | m <- [0 .. fcMorphismCount cat - 1]
      , fcSources cat V.! m `elem` objectsSorted
      , fcTargets cat V.! m `elem` objectsSorted
      ]
    objectNew old =
      case lookup old (zip objectsSorted [0 ..]) of
        Just new -> new
        Nothing -> error "component object lookup failed"
    morphismNew old =
      case lookup old (zip morphisms [0 ..]) of
        Just new -> new
        Nothing -> error "component morphism lookup failed"

disjointUnionCategoryForCanonical :: [FiniteCategory] -> FiniteCategory
disjointUnionCategoryForCanonical cats =
  FiniteCategory
    { fcMorphismCount = totalMorphisms
    , fcObjectCount = totalObjects
    , fcSources =
        V.fromList
          [ objectOffsets !! componentIndex + fcSources cat V.! local
          | (componentIndex, cat) <- indexedCats
          , local <- [0 .. fcMorphismCount cat - 1]
          ]
    , fcTargets =
        V.fromList
          [ objectOffsets !! componentIndex + fcTargets cat V.! local
          | (componentIndex, cat) <- indexedCats
          , local <- [0 .. fcMorphismCount cat - 1]
          ]
    , fcIdentities =
        V.fromList
          [ morphismOffsets !! componentIndex + fcIdentities cat V.! obj
          | (componentIndex, cat) <- indexedCats
          , obj <- [0 .. fcObjectCount cat - 1]
          ]
    , fcCompose =
        V.fromList
          [ composeGlobal f g
          | f <- [0 .. totalMorphisms - 1]
          , g <- [0 .. totalMorphisms - 1]
          ]
    }
  where
    indexedCats = zip [0 ..] cats
    objectOffsets = scanl (+) 0 (map fcObjectCount cats)
    morphismOffsets = scanl (+) 0 (map fcMorphismCount cats)
    totalObjects = sum (map fcObjectCount cats)
    totalMorphisms = sum (map fcMorphismCount cats)
    morphismOwners =
      concat
        [ replicate (fcMorphismCount cat) componentIndex
        | (componentIndex, cat) <- indexedCats
        ]
    localMorphism global =
      global - morphismOffsets !! (morphismOwners !! global)
    composeGlobal f g
      | componentF /= componentG = -1
      | localResult < 0 = -1
      | otherwise = morphismOffsets !! componentF + localResult
      where
        componentF = morphismOwners !! f
        componentG = morphismOwners !! g
        cat = cats !! componentF
        localResult = composeAt cat (localMorphism f) (localMorphism g)
