module CodexSlop.Category
  ( FiniteCategory(..)
  , composeAt
  , isComposable
  , isEndomorphism
  , isIdempotent
  , isIdentity
  , isBiconnectedCategory
  , homMorphisms
  , splitWitnesses
  , cauchyCompletenessFailures
  , isCauchyComplete
  , validateCategory
  , categoryKey
  , parseCategoryKey
  ) where

import Data.Char (isSpace)
import Data.List (intercalate)
import qualified Data.Vector as V

data FiniteCategory = FiniteCategory
  { fcMorphismCount :: !Int
  , fcObjectCount :: !Int
  , fcSources :: !(V.Vector Int)
  , fcTargets :: !(V.Vector Int)
  , fcIdentities :: !(V.Vector Int)
  , fcCompose :: !(V.Vector Int)
  } deriving (Eq, Ord, Show)

composeAt :: FiniteCategory -> Int -> Int -> Int
composeAt cat f g = fcCompose cat V.! (f * fcMorphismCount cat + g)

isComposable :: FiniteCategory -> Int -> Int -> Bool
isComposable cat f g = (fcTargets cat V.! f) == (fcSources cat V.! g)

isEndomorphism :: FiniteCategory -> Int -> Bool
isEndomorphism cat f = (fcSources cat V.! f) == (fcTargets cat V.! f)

isIdempotent :: FiniteCategory -> Int -> Bool
isIdempotent cat f = isEndomorphism cat f && composeAt cat f f == f

isIdentity :: FiniteCategory -> Int -> Bool
isIdentity cat f = f `elem` V.toList (fcIdentities cat)

isBiconnectedCategory :: FiniteCategory -> Bool
isBiconnectedCategory cat =
  and
    [ not (null (homMorphisms cat source target))
    | source <- [0 .. fcObjectCount cat - 1]
    , target <- [0 .. fcObjectCount cat - 1]
    ]

homMorphisms :: FiniteCategory -> Int -> Int -> [Int]
homMorphisms cat source target =
  [ f
  | f <- [0 .. fcMorphismCount cat - 1]
  , fcSources cat V.! f == source
  , fcTargets cat V.! f == target
  ]

splitWitnesses :: FiniteCategory -> Int -> [(Int, Int, Int)]
splitWitnesses cat e
  | not (isIdempotent cat e) = []
  | otherwise =
      [ (y, r, s)
      | y <- [0 .. fcObjectCount cat - 1]
      , r <- homMorphisms cat x y
      , s <- homMorphisms cat y x
      , composeAt cat r s == e
      , composeAt cat s r == fcIdentities cat V.! y
      ]
  where
    x = fcSources cat V.! e

cauchyCompletenessFailures :: FiniteCategory -> [String]
cauchyCompletenessFailures cat =
  [ "idempotent " ++ show e ++ " at object " ++ show (fcSources cat V.! e) ++ " has no splitting"
  | e <- [0 .. fcMorphismCount cat - 1]
  , isIdempotent cat e
  , null (splitWitnesses cat e)
  ]

isCauchyComplete :: FiniteCategory -> Bool
isCauchyComplete = null . cauchyCompletenessFailures

validateCategory :: FiniteCategory -> [String]
validateCategory cat =
  concat
    [ sizeErrors
    , identityErrors
    , compositionErrors
    , associativityErrors
    ]
  where
    n = fcMorphismCount cat
    k = fcObjectCount cat
    morphs = [0 .. n - 1]
    objects = [0 .. k - 1]
    inRange lo hi x = x >= lo && x <= hi

    sizeErrors =
      [ "source vector has wrong length" | V.length (fcSources cat) /= n ]
      ++ [ "target vector has wrong length" | V.length (fcTargets cat) /= n ]
      ++ [ "identity vector has wrong length" | V.length (fcIdentities cat) /= k ]
      ++ [ "composition table has wrong length" | V.length (fcCompose cat) /= n * n ]
      ++ [ "negative object count" | k < 0 ]
      ++ [ "negative morphism count" | n < 0 ]

    identityErrors =
      [ "identity " ++ show ident ++ " for object " ++ show obj ++ " is out of range"
      | obj <- objects
      , let ident = fcIdentities cat V.! obj
      , not (inRange 0 (n - 1) ident)
      ]
      ++
      [ "identity " ++ show ident ++ " does not have source=target=object " ++ show obj
      | obj <- objects
      , let ident = fcIdentities cat V.! obj
      , inRange 0 (n - 1) ident
      , (fcSources cat V.! ident, fcTargets cat V.! ident) /= (obj, obj)
      ]
      ++
      [ "left identity failed for morphism " ++ show f
      | f <- morphs
      , let sid = fcIdentities cat V.! (fcSources cat V.! f)
      , composeAt cat sid f /= f
      ]
      ++
      [ "right identity failed for morphism " ++ show f
      | f <- morphs
      , let tid = fcIdentities cat V.! (fcTargets cat V.! f)
      , composeAt cat f tid /= f
      ]

    compositionErrors =
      concat
        [ checkCell f g
        | f <- morphs
        , g <- morphs
        ]

    checkCell f g =
      let result = composeAt cat f g
      in if isComposable cat f g
           then
             [ "composition result out of range at " ++ show (f, g)
             | not (inRange 0 (n - 1) result)
             ]
             ++
             [ "composition result has wrong source/target at " ++ show (f, g)
             | inRange 0 (n - 1) result
             , (fcSources cat V.! result, fcTargets cat V.! result)
                 /= (fcSources cat V.! f, fcTargets cat V.! g)
             ]
           else
             [ "non-composable pair has a result at " ++ show (f, g)
             | result /= -1
             ]

    associativityErrors =
      [ "associativity failed at " ++ show (f, g, h)
      | f <- morphs
      , g <- morphs
      , h <- morphs
      , isComposable cat f g
      , isComposable cat g h
      , let fg = composeAt cat f g
      , let gh = composeAt cat g h
      , composeAt cat fg h /= composeAt cat f gh
      ]

categoryKey :: FiniteCategory -> String
categoryKey cat =
  intercalate
    ";"
    [ show (fcObjectCount cat)
    , show (fcMorphismCount cat)
    , csv (V.toList (fcSources cat))
    , csv (V.toList (fcTargets cat))
    , csv (V.toList (fcIdentities cat))
    , csv (V.toList (fcCompose cat))
    ]

parseCategoryKey :: String -> Either String FiniteCategory
parseCategoryKey raw =
  case splitOn ';' (trim raw) of
    [kTxt, nTxt, srcTxt, tgtTxt, idTxt, compTxt] -> do
      k <- readInt "object count" kTxt
      n <- readInt "morphism count" nTxt
      src <- readCsv "sources" srcTxt
      tgt <- readCsv "targets" tgtTxt
      ids <- readCsv "identities" idTxt
      comp <- readCsv "composition" compTxt
      pure
        FiniteCategory
          { fcMorphismCount = n
          , fcObjectCount = k
          , fcSources = V.fromList src
          , fcTargets = V.fromList tgt
          , fcIdentities = V.fromList ids
          , fcCompose = V.fromList comp
          }
    _ -> Left "expected six semicolon-separated fields"

csv :: [Int] -> String
csv = intercalate "," . map show

readCsv :: String -> String -> Either String [Int]
readCsv label txt
  | trim txt == "" = pure []
  | otherwise = traverse (readInt label) (splitOn ',' txt)

readInt :: String -> String -> Either String Int
readInt label txt =
  case reads (trim txt) of
    [(x, rest)] | all isSpace rest -> Right x
    _ -> Left ("could not parse " ++ label ++ ": " ++ txt)

splitOn :: Char -> String -> [String]
splitOn sep = go []
  where
    go acc [] = [reverse acc]
    go acc (c:cs)
      | c == sep = reverse acc : go [] cs
      | otherwise = go (c : acc) cs

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
