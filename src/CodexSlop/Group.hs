module CodexSlop.Group
  ( abelianGroupTables
  , cyclicGroupTable
  , directProductGroupTable
  , finiteGroupCategories
  , finiteGroupTables
  ) where

import CodexSlop.Category

import Control.Monad (foldM)
import Data.List (find)
import qualified Data.Set as Set
import qualified Data.Vector as V

finiteGroupCategories :: Int -> [FiniteCategory]
finiteGroupCategories order =
  [ groupCategory order table
  | table <- finiteGroupTables order
  ]

finiteGroupTables :: Int -> [V.Vector Int]
finiteGroupTables order
  | order < 1 = []
  | otherwise =
      uniqueTables $
        case completeKnownGroupTables order of
          Just tables -> tables
          Nothing -> latinSearchGroupTables order

groupCategory :: Int -> V.Vector Int -> FiniteCategory
groupCategory order table =
  FiniteCategory
    { fcMorphismCount = order
    , fcObjectCount = 1
    , fcSources = V.replicate order 0
    , fcTargets = V.replicate order 0
    , fcIdentities = V.singleton 0
    , fcCompose = table
    }

completeKnownGroupTables :: Int -> Maybe [V.Vector Int]
completeKnownGroupTables order
  | order >= 1 && order <= 15 = Just (smallOrderGroupTables order)
  | Just (_, primeExponent) <- primePower order
  , primeExponent <= 3 = Just (primePowerGroupTables order)
  | Just (p, q) <- twoPrimeOrder order = Just (twoPrimeGroupTables p q)
  | otherwise = Nothing

smallOrderGroupTables :: Int -> [V.Vector Int]
smallOrderGroupTables order =
  abelianGroupTables order ++
    case order of
      6 -> [dihedralGroupTable 3]
      8 -> [dihedralGroupTable 4, dicyclicGroupTable 2]
      10 -> [dihedralGroupTable 5]
      12 -> [dihedralGroupTable 6, dicyclicGroupTable 3, alternatingFourTable]
      14 -> [dihedralGroupTable 7]
      _ -> []

primePowerGroupTables :: Int -> [V.Vector Int]
primePowerGroupTables order =
  case primePower order of
    Just (p, 3)
      | p == 2 -> smallOrderGroupTables 8
      | otherwise ->
          abelianGroupTables order
            ++ [heisenbergP3Table p, nonabelianP3Table p]
    _ -> abelianGroupTables order

twoPrimeGroupTables :: Int -> Int -> [V.Vector Int]
twoPrimeGroupTables p q =
  abelianGroupTables (p * q) ++
    [ semidirectCyclicGroupTable (cyclicGroupTable q) q p action
    | (q - 1) `mod` p == 0
    , multiplier <- maybeToList (unitOfOrder p q)
    , let action x = (multiplier * x) `mod` q
    ]

abelianGroupTables :: Int -> [V.Vector Int]
abelianGroupTables order
  | order < 1 = []
  | otherwise =
      [ abelianGroupTable moduli
      | choices <- traverse primaryModuli (primeFactorization order)
      , let moduli = concat choices
      ]

primaryModuli :: (Int, Int) -> [[Int]]
primaryModuli (prime, primeExponent) =
  [ map (prime ^) partition
  | partition <- integerPartitions primeExponent
  ]

abelianGroupTable :: [Int] -> V.Vector Int
abelianGroupTable moduli =
  V.fromList
    [ encode (zipWith3 addMod moduli (decode x) (decode y))
    | x <- [0 .. order - 1]
    , y <- [0 .. order - 1]
    ]
  where
    order = product moduli
    decode value = decodeWith moduli value
    encode = encodeWith moduli
    addMod modulus x y = (x + y) `mod` modulus

cyclicGroupTable :: Int -> V.Vector Int
cyclicGroupTable order = abelianGroupTable [order]

directProductGroupTable :: V.Vector Int -> Int -> V.Vector Int -> Int -> V.Vector Int
directProductGroupTable left leftOrder right rightOrder =
  V.fromList
    [ pairIndex (leftMul lx ly) (rightMul rx ry)
    | lx <- [0 .. leftOrder - 1]
    , rx <- [0 .. rightOrder - 1]
    , ly <- [0 .. leftOrder - 1]
    , ry <- [0 .. rightOrder - 1]
    ]
  where
    pairIndex x y = x * rightOrder + y
    leftMul x y = left V.! groupPairIndex leftOrder x y
    rightMul x y = right V.! groupPairIndex rightOrder x y

semidirectCyclicGroupTable :: V.Vector Int -> Int -> Int -> (Int -> Int) -> V.Vector Int
semidirectCyclicGroupTable kernel kernelOrder quotientOrder action =
  V.fromList
    [ encode (kernelMul k (applyPower q l)) ((q + r) `mod` quotientOrder)
    | q <- [0 .. quotientOrder - 1]
    , k <- [0 .. kernelOrder - 1]
    , r <- [0 .. quotientOrder - 1]
    , l <- [0 .. kernelOrder - 1]
    ]
  where
    encode k q = q * kernelOrder + k
    kernelMul x y = kernel V.! groupPairIndex kernelOrder x y
    applyPower q x = iterate action x !! q

dihedralGroupTable :: Int -> V.Vector Int
dihedralGroupTable rotations =
  semidirectCyclicGroupTable (cyclicGroupTable rotations) rotations 2 invertRotation
  where
    invertRotation x = (-x) `mod` rotations

dicyclicGroupTable :: Int -> V.Vector Int
dicyclicGroupTable n =
  V.fromList
    [ multiply x y
    | x <- [0 .. order - 1]
    , y <- [0 .. order - 1]
    ]
  where
    rotationOrder = 2 * n
    order = 4 * n
    encode rotation hasX = (if hasX then rotationOrder else 0) + (rotation `mod` rotationOrder)
    decode value =
      let (hasX, rotation) = value `divMod` rotationOrder
      in (rotation, hasX == 1)
    multiply x y =
      let (i, hasX) = decode x
          (j, hasY) = decode y
          signedJ = if hasX then negate j else j
          twist = if hasX && hasY then n else 0
      in encode (i + signedJ + twist) (hasX /= hasY)

alternatingFourTable :: V.Vector Int
alternatingFourTable =
  semidirectCyclicGroupTable (abelianGroupTable [2, 2]) 4 3 action
  where
    action x =
      case decodeWith [2, 2] x of
        [a, b] -> encodeWith [2, 2] [b, (a + b) `mod` 2]
        _ -> error "invalid V4 coordinate"

heisenbergP3Table :: Int -> V.Vector Int
heisenbergP3Table p =
  V.fromList
    [ multiply x y
    | x <- [0 .. order - 1]
    , y <- [0 .. order - 1]
    ]
  where
    order = p ^ (3 :: Int)
    encode a b c = (a `mod` p) * p * p + (b `mod` p) * p + (c `mod` p)
    decode value =
      let (a, rest) = value `divMod` (p * p)
          (b, c) = rest `divMod` p
      in (a, b, c)
    multiply x y =
      let (a, b, c) = decode x
          (a', b', c') = decode y
      in encode (a + a') (b + b') (c + c' + a * b')

nonabelianP3Table :: Int -> V.Vector Int
nonabelianP3Table p =
  semidirectCyclicGroupTable (cyclicGroupTable (p * p)) (p * p) p action
  where
    action x = ((1 + p) * x) `mod` (p * p)

latinSearchGroupTables :: Int -> [V.Vector Int]
latinSearchGroupTables order =
  case propagateGroupTable order (initialGroupTable order) of
    Nothing -> []
    Just table -> search table
  where
    search table =
      case chooseGroupCell order table of
        Nothing -> [table | validGroupTable order table]
        Just idx ->
          concat
            [ maybe [] search (assignGroupCell order table idx value >>= propagateGroupTable order)
            | value <- groupDomain order table idx
            ]

initialGroupTable :: Int -> V.Vector Int
initialGroupTable order =
  V.fromList
    [ initialCell x y
    | x <- elements
    , y <- elements
    ]
  where
    elements = [0 .. order - 1]
    initialCell x y
      | x == 0 = y
      | y == 0 = x
      | otherwise = -1

chooseGroupCell :: Int -> V.Vector Int -> Maybe Int
chooseGroupCell order table =
  case candidates of
    [] -> Nothing
    _ -> Just (fst (foldl1 better candidates))
  where
    candidates =
      [ (idx, length (groupDomain order table idx))
      | idx <- [0 .. V.length table - 1]
      , table V.! idx == -1
      ]
    better a@(_, da) b@(_, db)
      | da <= db = a
      | otherwise = b

groupDomain :: Int -> V.Vector Int -> Int -> [Int]
groupDomain order table idx =
  [ value
  | value <- [0 .. order - 1]
  , value `notElem` rowValues
  , value `notElem` columnValues
  ]
  where
    (row, column) = idx `divMod` order
    rowValues =
      [ table V.! (row * order + y)
      | y <- [0 .. order - 1]
      , table V.! (row * order + y) >= 0
      ]
    columnValues =
      [ table V.! (x * order + column)
      | x <- [0 .. order - 1]
      , table V.! (x * order + column) >= 0
      ]

assignGroupCell :: Int -> V.Vector Int -> Int -> Int -> Maybe (V.Vector Int)
assignGroupCell order table idx value
  | value < 0 || value >= order = Nothing
  | old == value = Just table
  | old /= -1 = Nothing
  | value `elem` groupDomain order table idx = Just (table V.// [(idx, value)])
  | otherwise = Nothing
  where
    old = table V.! idx

propagateGroupTable :: Int -> V.Vector Int -> Maybe (V.Vector Int)
propagateGroupTable order table = do
  (table1, latinChanged) <- propagateLatin order table
  (table2, assocChanged) <- propagateGroupAssociativity order table1
  if latinChanged || assocChanged
    then propagateGroupTable order table2
    else Just table2

propagateLatin :: Int -> V.Vector Int -> Maybe (V.Vector Int, Bool)
propagateLatin order table = do
  (afterRows, rowChanged) <- foldM forceLine (table, False) rowLines
  (afterColumns, columnChanged) <- foldM forceLine (afterRows, False) columnLines
  Just (afterColumns, rowChanged || columnChanged)
  where
    rowLines =
      [ [x * order + y | y <- [0 .. order - 1]]
      | x <- [0 .. order - 1]
      ]
    columnLines =
      [ [x * order + y | x <- [0 .. order - 1]]
      | y <- [0 .. order - 1]
      ]

    forceLine (current, changed) indices =
      case (unassigned, missing) of
        ([], []) -> Just (current, changed)
        ([_], [value]) -> do
          next <- assignGroupCell order current (head unassigned) value
          Just (next, True)
        _ ->
          if length missing < length unassigned
            then Nothing
            else Just (current, changed)
      where
        values = [current V.! idx | idx <- indices]
        assigned = filter (>= 0) values
        unassigned = [idx | idx <- indices, current V.! idx == -1]
        missing =
          [value | value <- [0 .. order - 1], value `notElem` assigned]

propagateGroupAssociativity :: Int -> V.Vector Int -> Maybe (V.Vector Int, Bool)
propagateGroupAssociativity order table =
  foldM step (table, False) triples
  where
    elements = [0 .. order - 1]
    triples = [(x, y, z) | x <- elements, y <- elements, z <- elements]

    step (current, changed) (x, y, z) =
      let xy = current V.! groupPairIndex order x y
          yz = current V.! groupPairIndex order y z
      in if xy >= 0 && yz >= 0
           then
             let leftIndex = groupPairIndex order xy z
                 rightIndex = groupPairIndex order x yz
                 left = current V.! leftIndex
                 right = current V.! rightIndex
             in case (left >= 0, right >= 0) of
                  (True, True) ->
                    if left == right then Just (current, changed) else Nothing
                  (True, False) -> do
                    next <- assignGroupCell order current rightIndex left
                    Just (next, True)
                  (False, True) -> do
                    next <- assignGroupCell order current leftIndex right
                    Just (next, True)
                  (False, False) -> Just (current, changed)
           else Just (current, changed)

validGroupTable :: Int -> V.Vector Int -> Bool
validGroupTable order table =
  all (>= 0) (V.toList table)
    && all lineIsPermutation rows
    && all lineIsPermutation columns
    && associative
  where
    elements = [0 .. order - 1]
    rows =
      [ [table V.! groupPairIndex order x y | y <- elements]
      | x <- elements
      ]
    columns =
      [ [table V.! groupPairIndex order x y | x <- elements]
      | y <- elements
      ]
    lineIsPermutation values =
      Set.fromList values == Set.fromList elements
    associative =
      and
        [ table V.! groupPairIndex order (mul x y) z
            == table V.! groupPairIndex order x (mul y z)
        | x <- elements
        , y <- elements
        , z <- elements
        ]
    mul x y = table V.! groupPairIndex order x y

primeFactorization :: Int -> [(Int, Int)]
primeFactorization n =
  factor n 2
  where
    factor remaining candidate
      | remaining <= 1 = []
      | candidate * candidate > remaining = [(remaining, 1)]
      | remaining `mod` candidate == 0 =
          let (power, rest) = dividePower remaining candidate 0
          in (candidate, power) : factor rest (candidate + 1)
      | otherwise = factor remaining (candidate + 1)

dividePower :: Int -> Int -> Int -> (Int, Int)
dividePower value prime primeExponent
  | value `mod` prime == 0 = dividePower (value `div` prime) prime (primeExponent + 1)
  | otherwise = (primeExponent, value)

primePower :: Int -> Maybe (Int, Int)
primePower order =
  case primeFactorization order of
    [(prime, primeExponent)] -> Just (prime, primeExponent)
    _ -> Nothing

twoPrimeOrder :: Int -> Maybe (Int, Int)
twoPrimeOrder order =
  case primeFactorization order of
    [(p, 1), (q, 1)] -> Just (p, q)
    _ -> Nothing

unitOfOrder :: Int -> Int -> Maybe Int
unitOfOrder order modulus =
  find hasOrder [2 .. modulus - 1]
  where
    hasOrder value =
      powMod value order modulus == 1
        && all (\d -> powMod value d modulus /= 1) properDivisors
    properDivisors = [d | d <- [1 .. order - 1], order `mod` d == 0]

powMod :: Int -> Int -> Int -> Int
powMod base power modulus =
  go 1 (base `mod` modulus) power
  where
    go acc _ 0 = acc
    go acc b e
      | odd e = go ((acc * b) `mod` modulus) ((b * b) `mod` modulus) (e `div` 2)
      | otherwise = go acc ((b * b) `mod` modulus) (e `div` 2)

integerPartitions :: Int -> [[Int]]
integerPartitions total = partitionsAtMost total total

partitionsAtMost :: Int -> Int -> [[Int]]
partitionsAtMost 0 _ = [[]]
partitionsAtMost total maxPart =
  [ part : rest
  | part <- [min total maxPart, min total maxPart - 1 .. 1]
  , rest <- partitionsAtMost (total - part) part
  ]

decodeWith :: [Int] -> Int -> [Int]
decodeWith [] _ = []
decodeWith (modulus:rest) value =
  let (remaining, residue) = value `divMod` modulus
  in residue : decodeWith rest remaining

encodeWith :: [Int] -> [Int] -> Int
encodeWith moduli coordinates =
  sum (zipWith (*) coordinates strides)
  where
    strides = scanl (*) 1 moduli

maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just x) = [x]

uniqueTables :: [V.Vector Int] -> [V.Vector Int]
uniqueTables = Set.toAscList . Set.fromList

groupPairIndex :: Int -> Int -> Int -> Int
groupPairIndex order x y = x * order + y
