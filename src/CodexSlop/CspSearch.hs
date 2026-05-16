module CodexSlop.CspSearch
  ( enumerateShapeCSP
  , enumerateShapeCauchyCSP
  ) where

import CodexSlop.Category
import CodexSlop.Shape

import Control.Monad.CSP
import Data.List (nub)
import qualified Data.Vector as V

enumerateShapeCSP :: Shape -> [FiniteCategory]
enumerateShapeCSP = enumerateShapeWithCSP False

enumerateShapeCauchyCSP :: Shape -> [FiniteCategory]
enumerateShapeCauchyCSP = enumerateShapeWithCSP True

enumerateShapeWithCSP :: Bool -> Shape -> [FiniteCategory]
enumerateShapeWithCSP requireCauchy shape =
  [ cat
  | table <- allCSPSolutions (compositionCSP shape)
  , let cat = makeCategory table
  , null (validateCategory cat)
  , not requireCauchy || isCauchyComplete cat
  ]
  where
    makeCategory table =
      FiniteCategory
        { fcMorphismCount = shapeMorphismCount shape
        , fcObjectCount = shapeObjectCount shape
        , fcSources = shapeSources shape
        , fcTargets = shapeTargets shape
        , fcIdentities = shapeIdentities shape
        , fcCompose = V.fromList table
        }

compositionCSP :: Shape -> CSP [Int] [DV [Int] Int]
compositionCSP shape = do
  variables <- mapM mkDV cellDomains
  mapM_ (addAssociativityConstraint cellDomains variables) (composableTriples shape)
  pure variables
  where
    n = shapeMorphismCount shape
    cellDomains =
      [ domainForCell shape (pairIndex n f g)
      | f <- [0 .. n - 1]
      , g <- [0 .. n - 1]
      ]

addAssociativityConstraint :: [[Int]] -> [DV [Int] Int] -> (Int, Int, Int) -> CSP [Int] ()
addAssociativityConstraint cellDomains variables (f, g, h) =
  constraint predicate selectedVariables
  where
    n = floor (sqrt (fromIntegral (length variables) :: Double))
    fgIndex = pairIndex n f g
    ghIndex = pairIndex n g h
    fgDomain = filter (>= 0) (cellDomains !! fgIndex)
    ghDomain = filter (>= 0) (cellDomains !! ghIndex)
    leftIndices = [pairIndex n r h | r <- fgDomain]
    rightIndices = [pairIndex n f s | s <- ghDomain]
    indices = nub (fgIndex : ghIndex : leftIndices ++ rightIndices)
    selectedVariables = [variables !! idx | idx <- indices]

    predicate values =
      let assigned = zip indices values
          fg = lookupValue fgIndex assigned
          gh = lookupValue ghIndex assigned
          left = lookupValue (pairIndex n fg h) assigned
          right = lookupValue (pairIndex n f gh) assigned
      in left == right

lookupValue :: Int -> [(Int, Int)] -> Int
lookupValue idx pairs =
  case lookup idx pairs of
    Just value -> value
    Nothing -> error "CSP associativity constraint missing cell"

domainForCell :: Shape -> Int -> [Int]
domainForCell shape idx
  | targets V.! f /= sources V.! g = [-1]
  | isId V.! f = [g]
  | isId V.! g = [f]
  | otherwise = blockAt shape (sources V.! f) (targets V.! g)
  where
    n = shapeMorphismCount shape
    (f, g) = idx `divMod` n
    sources = shapeSources shape
    targets = shapeTargets shape
    isId = shapeIsIdentity shape

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

pairIndex :: Int -> Int -> Int -> Int
pairIndex n f g = f * n + g
