module Main (main) where

import CodexSlop.Canonical
import CodexSlop.Biconnected
import CodexSlop.Category
import CodexSlop.Copresheaf
import CodexSlop.CspSearch
import CodexSlop.Decompose
import CodexSlop.Generate
import CodexSlop.Group
import CodexSlop.Profunctor
import CodexSlop.Search
import CodexSlop.Shape
import CodexSlop.Thin

import qualified Data.Set as Set
import qualified Data.Text.Lazy as TL
import qualified Data.Vector as V
import qualified Nauty.Digraph6 as D
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main =
  defaultMain $
    testGroup
      "cat-enum"
      [ categoryValidationTests
      , biconnectedTests
      , canonicalTests
      , decompositionTests
      , groupTests
      , cspSearchTests
      , generationTests
      , enumerationTests
      , cauchyTests
      , copresheafTests
      , profunctorTests
      , thinTests
      ]

categoryValidationTests :: TestTree
categoryValidationTests =
  testGroup
    "validation"
    [ testCase "terminal category validates" $
        validateCategory terminalCategory @?= []
    , testCase "bad identity law is rejected" $
        assertBool "expected validation errors" (not (null (validateCategory badIdentityCategory)))
    ]

biconnectedTests :: TestTree
biconnectedTests =
  testGroup
    "biconnected"
    [ testCase "terminal category is biconnected" $
        assertBool "expected every hom-set to be nonempty" (isBiconnectedCategory terminalCategory)
    , testCase "arrow category is not biconnected" $
        assertBool "expected a missing reverse hom-set" (not (isBiconnectedCategory arrowCategory))
    , testCase "small biconnected totals" $ do
        biconnectedTotal False 1 @?= 1
        biconnectedTotal False 2 @?= 2
        biconnectedTotal False 3 @?= 7
    , testCase "small Cauchy-complete biconnected totals" $ do
        biconnectedTotal True 1 @?= 1
        biconnectedTotal True 2 @?= 1
        biconnectedTotal True 3 @?= 1
    , testCase "one-object Cauchy-complete biconnected totals are small groups" $
        map groupTotal [1 .. 8] @?= [1, 1, 1, 2, 1, 2, 1, 5]
    , testCase "larger one-object group totals use structural constructors" $
        map groupTotal [9 .. 15] @?= [2, 2, 1, 5, 1, 2, 1]
    ]
  where
    biconnectedTotal cauchyOnly n =
      sum [Set.size keys | (_, keys) <- biconnectedCanonicalKeys n Nothing cauchyOnly]
    groupTotal n =
      sum [Set.size keys | (_, keys) <- biconnectedCanonicalKeys n (Just 1) True]

canonicalTests :: TestTree
canonicalTests =
  testGroup
    "canonicalization"
    [ testCase "relabelled arrow categories have the same canonical key" $
        canonicalKey arrowCategory @?= canonicalKey swappedArrowCategory
    , testCase "relabelled one-object groups have the same canonical key" $
        canonicalKey cyclicNine @?= canonicalKey relabelledCyclicNine
    , testCase "equivalent groupoid skeletons have the same equivalence key" $
        equivalenceKey twoObjectIsoGroupoid @?= equivalenceKey terminalCategory
    , testCase "representative modes choose equivalence, isomorphism, or equality keys" $ do
        representativeKey UpToEquivalence twoObjectIsoGroupoid
          @?= representativeKey UpToEquivalence terminalCategory
        assertBool
          "strict isomorphism should keep the non-skeletal groupoid separate"
          ( representativeKey UpToIsomorphism twoObjectIsoGroupoid
              /= representativeKey UpToIsomorphism terminalCategory
          )
        representativeKey UpToEquality swappedArrowCategory @?= categoryKey swappedArrowCategory
    , testCase "canonical key parses back to a valid category" $
        case parseCategoryKey (canonicalKey arrowCategory) of
          Left err -> assertFailure err
          Right cat -> validateCategory cat @?= []
    ]

decompositionTests :: TestTree
decompositionTests =
  testGroup
    "support decomposition"
    [ testCase "arrow category decomposes into two terminal biconnected components" $ do
        let decomp = supportDecomposition arrowCategory
        length (sdClasses decomp) @?= 2
        map (validateCategory . componentCategory arrowCategory) (sdClasses decomp) @?= [[], []]
        map (fcMorphismCount . componentCategory arrowCategory) (sdClasses decomp) @?= [1, 1]
    , testCase "biconnected category has one support component" $
        length (sdClasses (supportDecomposition zeroMonoidCategory)) @?= 1
    , testCase "canonical isomorphic arrow categories have the same decomposition signature" $
        canonicalDecomp arrowCategory @?= canonicalDecomp swappedArrowCategory
    , testCase "disjoint union components split disconnected categories" $ do
        validateCategory twoPointDiscreteCategory @?= []
        connectedObjectComponents twoPointDiscreteCategory @?= [[0], [1]]
        map fcMorphismCount (disjointUnionComponents twoPointDiscreteCategory) @?= [1, 1]
    ]
  where
    canonicalDecomp cat =
      case parseCategoryKey (canonicalKey cat) of
        Left err -> error err
        Right canonical -> decompositionSignature canonical

groupTests :: TestTree
groupTests =
  testGroup
    "group construction"
    [ testCase "finite abelian group counts follow partition products" $
        map (length . abelianGroupTables) [1, 8, 12, 16, 36] @?= [1, 3, 2, 5, 4]
    , testCase "known direct group constructors cover small orders" $
        map (length . finiteGroupTables) [1 .. 15] @?= [1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 5, 1, 2, 1]
    , testCase "p cubed constructors cover the standard five groups for odd p" $
        length (finiteGroupTables 27) @?= 5
    , testCase "constructed group tables validate as one-object categories" $
        concatMap (validateCategory . groupCategoryFromTable) (finiteGroupTables 12) @?= []
    ]

generationTests :: TestTree
generationTests =
  testGroup
    "component generation"
    [ testCase "generated categories match exact small totals" $
        map (generatedTotal False) [1 .. 5] @?= map (exactTotal False) [1 .. 5]
    , testCase "generated Cauchy-complete categories match exact small totals" $
        map (generatedTotal True) [1 .. 6] @?= map (exactTotal True) [1 .. 6]
    , testCase "cached small-extra Cauchy generation matches pure generation" $ do
        cached <- componentGeneratedKeysCached 6 (Just 4) True
        cached @?= componentGeneratedKeys 6 (Just 4) True
    ]
  where
    generatedTotal cauchyOnly n =
      sum [Set.size keys | (_, keys) <- componentGeneratedKeys n Nothing cauchyOnly]
    exactTotal cauchyOnly n =
      sum [Set.size keys | (_, keys) <- enumerateCanonicalKeys n Nothing False cauchyOnly]

enumerationTests :: TestTree
enumerationTests =
  testGroup
    "enumeration"
    [ testCase "known totals for one to three morphisms" $ do
        total 1 @?= 1
        total 2 @?= 3
        total 3 @?= 11
    ]
  where
    total n = sum [Set.size keys | (_, keys) <- enumerateCanonicalKeys n Nothing False False]

cauchyTests :: TestTree
cauchyTests =
  testGroup
    "cauchy completeness"
    [ testCase "terminal category is Cauchy complete" $
        assertBool "expected split idempotents" (isCauchyComplete terminalCategory)
    , testCase "two-element zero monoid is not Cauchy complete" $
        assertBool "expected a non-splitting idempotent" (not (isCauchyComplete zeroMonoidCategory))
    , testCase "two morphisms have two Cauchy-complete categories" $
        cauchyTotal 2 @?= 2
    , testCase "Cauchy-complete totals through four morphisms" $
        map cauchyTotal [1 .. 4] @?= [1, 2, 4, 11]
    ]
  where
    cauchyTotal n = sum [Set.size keys | (_, keys) <- enumerateCanonicalKeys n Nothing False True]

copresheafTests :: TestTree
copresheafTests =
  testGroup
    "copresheaves"
    [ testCase "terminal category has one finite copresheaf per size" $
        copresheafCountsUpTo 3 terminalCategory @?= [(0, 1), (1, 1), (2, 1), (3, 1)]
    , testCase "copresheaves factor over disjoint unions" $
        copresheafCountsUpTo 4 twoPointDiscreteCategory @?= [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]
    , testCase "arrow category raw size-two copresheaves" $
        countCopresheavesOfSize arrowCategory 2 @?= 2
    ]

profunctorTests :: TestTree
profunctorTests =
  testGroup
    "profunctors"
    [ testCase "terminal-terminal profunctors have one action per size" $
        profunctorCountsUpTo 3 terminalCategory terminalCategory @?= [(0, 1), (1, 1), (2, 1), (3, 1)]
    , testCase "terminal-to-category profunctors match copresheaves" $
        countProfunctorsForProfile terminalCategory arrowCategory [2, 3]
          @?= countCopresheavesForProfile arrowCategory [2, 3]
    , testCase "arrow-to-terminal profunctors are presheaf-shaped" $
        countProfunctorsForProfile arrowCategory terminalCategory [2, 3] @?= 8
    , testCase "all singleton fibers give one profunctor" $
        countProfunctorsForProfile arrowCategory arrowCategory [1, 1, 1, 1] @?= 1
    , testCase "profunctor counts factor over disconnected sources" $
        profunctorCountsUpTo 3 twoPointDiscreteCategory terminalCategory @?= [(0, 1), (1, 2), (2, 3), (3, 4)]
    , testCase "cached profile counts match pure profile counts" $ do
        cached <- countProfunctorsForProfileCached terminalCategory arrowCategory [2, 3]
        cached @?= countProfunctorsForProfile terminalCategory arrowCategory [2, 3]
    ]

thinTests :: TestTree
thinTests =
  testGroup
    "thin digraph6"
    [ testCase "classifies a two-element chain as a poset" $
        classifyDigraph6Text chainText
          @?= [(1, Right (ThinReport 2 True True True))]
    ]
  where
    matrix = D.fromArcList 2 [(0, 0), (1, 1), (0, 1)]
    chainText = D.encode matrix

terminalCategory :: FiniteCategory
terminalCategory =
  FiniteCategory
    { fcMorphismCount = 1
    , fcObjectCount = 1
    , fcSources = V.fromList [0]
    , fcTargets = V.fromList [0]
    , fcIdentities = V.fromList [0]
    , fcCompose = V.fromList [0]
    }

twoPointDiscreteCategory :: FiniteCategory
twoPointDiscreteCategory =
  disjointUnionCategory [terminalCategory, terminalCategory]

badIdentityCategory :: FiniteCategory
badIdentityCategory =
  terminalCategory {fcCompose = V.fromList [-1]}

zeroMonoidCategory :: FiniteCategory
zeroMonoidCategory =
  FiniteCategory
    { fcMorphismCount = 2
    , fcObjectCount = 1
    , fcSources = V.fromList [0, 0]
    , fcTargets = V.fromList [0, 0]
    , fcIdentities = V.fromList [0]
    , fcCompose = V.fromList [0, 1, 1, 1]
    }

arrowCategory :: FiniteCategory
arrowCategory =
  categoryFromTypedMorphisms 2 [0, 0, 1] [0, 1, 1] [0, 2]

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

swappedArrowCategory :: FiniteCategory
swappedArrowCategory =
  categoryFromTypedMorphisms 2 [0, 1, 1] [0, 0, 1] [0, 2]

cyclicNine :: FiniteCategory
cyclicNine =
  groupCategoryFromTable (cyclicGroupTable 9)

relabelledCyclicNine :: FiniteCategory
relabelledCyclicNine =
  relabelOneObjectGroup cyclicNine [0, 3, 6, 1, 4, 7, 2, 5, 8]

groupCategoryFromTable :: V.Vector Int -> FiniteCategory
groupCategoryFromTable table =
  FiniteCategory
    { fcMorphismCount = n
    , fcObjectCount = 1
    , fcSources = V.replicate n 0
    , fcTargets = V.replicate n 0
    , fcIdentities = V.singleton 0
    , fcCompose = table
    }
  where
        n = floor (sqrt (fromIntegral (V.length table) :: Double))

cspSearchTests :: TestTree
cspSearchTests =
  testGroup
    "csp search"
    [ testCase "CSP shape solver matches custom solver on small shapes" $
        map cspCount smallShapes @?= map customCount smallShapes
    , testCase "CSP Cauchy shape solver matches custom solver on small shapes" $
        map cspCauchyCount smallShapes @?= map customCauchyCount smallShapes
    ]
  where
    smallShapes = take 5 (shapesFor 4 Nothing False)
    cspCount shape = length (enumerateShapeCSP shape)
    customCount shape = length (enumerateShape shape)
    cspCauchyCount shape = length (enumerateShapeCauchyCSP shape)
    customCauchyCount shape = length (enumerateShapeCauchy shape)

relabelOneObjectGroup :: FiniteCategory -> [Int] -> FiniteCategory
relabelOneObjectGroup cat newToOld =
  cat
    { fcCompose =
        V.fromList
          [ oldToNew V.! composeAt cat (oldMorph f) (oldMorph g)
          | f <- [0 .. n - 1]
          , g <- [0 .. n - 1]
          ]
    }
  where
    n = length newToOld
    oldToNew = V.fromList (invertList n newToOld)
    oldMorph newMorph = newToOld !! newMorph

invertList :: Int -> [Int] -> [Int]
invertList size xs =
  [ lookupValue i | i <- [0 .. size - 1] ]
  where
    pairs = zip xs [0 ..]
    lookupValue x =
      case lookup x pairs of
        Just y -> y
        Nothing -> error "invalid permutation"

categoryFromTypedMorphisms :: Int -> [Int] -> [Int] -> [Int] -> FiniteCategory
categoryFromTypedMorphisms k sources targets identities =
  FiniteCategory
    { fcMorphismCount = n
    , fcObjectCount = k
    , fcSources = V.fromList sources
    , fcTargets = V.fromList targets
    , fcIdentities = V.fromList identities
    , fcCompose = V.fromList [cell f g | f <- morphs, g <- morphs]
    }
  where
    n = length sources
    morphs = [0 .. n - 1]
    isId f = f `elem` identities
    cell f g
      | targets !! f /= sources !! g = -1
      | isId f = g
      | isId g = f
      | otherwise = error "test helper only supports free arrow categories"

_textAnchor :: TL.Text -> TL.Text
_textAnchor = id
