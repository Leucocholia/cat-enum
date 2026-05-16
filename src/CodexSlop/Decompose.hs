module CodexSlop.Decompose
  ( SupportDecomposition(..)
  , connectedObjectComponents
  , componentCategory
  , decompositionSignature
  , disjointUnionCategory
  , disjointUnionComponents
  , isConnectedCategory
  , supportDecomposition
  ) where

import CodexSlop.Canonical (canonicalKey)
import CodexSlop.Category

import Data.List (intercalate, sort)
import qualified Data.Vector as V

data SupportDecomposition = SupportDecomposition
  { sdClassOfObject :: !(V.Vector Int)
  , sdClasses :: ![[Int]]
  , sdQuotientRelation :: !(V.Vector Bool)
  , sdComponentKeys :: ![String]
  } deriving (Eq, Show)

supportDecomposition :: FiniteCategory -> SupportDecomposition
supportDecomposition cat =
  SupportDecomposition
    { sdClassOfObject = V.fromList classOf
    , sdClasses = classes
    , sdQuotientRelation = V.fromList quotient
    , sdComponentKeys = componentKeys
    }
  where
    k = fcObjectCount cat
    classes = supportClasses cat
    classOf =
      [ classIndex obj
      | obj <- [0 .. k - 1]
      ]
    classIndex obj =
      case [i | (i, cls) <- zip [0 ..] classes, obj `elem` cls] of
        i:_ -> i
        [] -> error "object missing from support decomposition"
    quotient =
      [ any (\x -> any (\y -> supportRelated cat x y) targetClass) sourceClass
      | sourceClass <- classes
      , targetClass <- classes
      ]
    componentKeys =
      [ canonicalKey (componentCategory cat cls)
      | cls <- classes
      ]

decompositionSignature :: FiniteCategory -> String
decompositionSignature cat =
  intercalate
    "|"
    [ show (length (sdClasses decomp))
    , boolCsv (V.toList (sdQuotientRelation decomp))
    , intercalate "#" (sdComponentKeys decomp)
    ]
  where
    decomp = supportDecomposition cat

connectedObjectComponents :: FiniteCategory -> [[Int]]
connectedObjectComponents cat =
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
      , supportRelated cat x y || supportRelated cat y x
      ]

isConnectedCategory :: FiniteCategory -> Bool
isConnectedCategory cat =
  length (connectedObjectComponents cat) <= 1

disjointUnionComponents :: FiniteCategory -> [FiniteCategory]
disjointUnionComponents cat =
  [ componentCategory cat objects
  | objects <- connectedObjectComponents cat
  ]

disjointUnionCategory :: [FiniteCategory] -> FiniteCategory
disjointUnionCategory cats =
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

componentCategory :: FiniteCategory -> [Int] -> FiniteCategory
componentCategory cat objects =
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

supportClasses :: FiniteCategory -> [[Int]]
supportClasses cat =
  go [0 .. fcObjectCount cat - 1] []
  where
    go [] acc = reverse acc
    go (x:xs) acc =
      let cls = sort [y | y <- x : xs, mutuallyRelated x y]
          rest = [y | y <- xs, y `notElem` cls]
      in go rest (cls : acc)
    mutuallyRelated x y =
      supportRelated cat x y && supportRelated cat y x

supportRelated :: FiniteCategory -> Int -> Int -> Bool
supportRelated cat source target =
  not (null (homMorphisms cat source target))

boolCsv :: [Bool] -> String
boolCsv =
  intercalate "," . map (\b -> if b then "1" else "0")
