module CodexSlop.CLI
  ( runCLI
  ) where

import CodexSlop.Biconnected
import CodexSlop.Canonical (RepresentativeMode(..), canonicalKey, representativeModeName)
import CodexSlop.Category
import CodexSlop.Copresheaf
import CodexSlop.Decompose
import CodexSlop.Generate
import CodexSlop.Profunctor
import CodexSlop.Search
import CodexSlop.Thin

import Control.Monad (forM_, unless, when)
import Data.Char (toLower)
import Data.List (intercalate, sort)
import qualified Data.Set as Set
import qualified Data.Text.Lazy.IO as TLIO
import qualified Data.Vector as V
import Options.Applicative
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , listDirectory
  )
import System.FilePath ((</>))

data Command
  = Count CountOptions
  | Biconnected BiconnectedOptions
  | Verify VerifyOptions
  | Copresheaves CopresheafOptions
  | Decompose DecomposeOptions
  | Generate GenerateOptions
  | Profunctors ProfunctorOptions
  | Thin FilePath
  deriving (Eq, Show)

data CountOptions = CountOptions
  { optMaxMorphisms :: !Int
  , optObjects :: !(Maybe Int)
  , optConnectedOnly :: !Bool
  , optWriteReps :: !(Maybe FilePath)
  , optCauchyComplete :: !Bool
  , optRepresentativeMode :: !RepresentativeMode
  } deriving (Eq, Show)

data BiconnectedOptions = BiconnectedOptions
  { biMaxMorphisms :: !Int
  , biObjects :: !(Maybe Int)
  , biWriteReps :: !(Maybe FilePath)
  , biCauchyComplete :: !Bool
  } deriving (Eq, Show)

data VerifyOptions = VerifyOptions
  { verifyPath :: !FilePath
  , verifyCauchyComplete :: !Bool
  } deriving (Eq, Show)

data CopresheafOptions = CopresheafOptions
  { copMorphisms :: !Int
  , copMaxElements :: !Int
  , copObjects :: !(Maybe Int)
  , copConnectedOnly :: !Bool
  , copAllCategories :: !Bool
  } deriving (Eq, Show)

data DecomposeOptions = DecomposeOptions
  { decMorphisms :: !Int
  , decObjects :: !(Maybe Int)
  , decConnectedOnly :: !Bool
  , decCauchyComplete :: !Bool
  , decLimit :: !Int
  } deriving (Eq, Show)

data GenerateOptions = GenerateOptions
  { genMorphisms :: !Int
  , genObjects :: !(Maybe Int)
  , genCauchyComplete :: !Bool
  , genWriteReps :: !(Maybe FilePath)
  , genRepresentativeMode :: !RepresentativeMode
  , genDual :: !Bool
  , genVerbose :: !Bool
  } deriving (Eq, Show)

data ProfunctorOptions = ProfunctorOptions
  { profLeft :: !FilePath
  , profRight :: !FilePath
  , profMaxElements :: !Int
  , profProfile :: !(Maybe [Int])
  } deriving (Eq, Show)

runCLI :: IO ()
runCLI = do
  selected <- execParser parserInfo
  case selected of
    Count options -> runCount options
    Biconnected options -> runBiconnected options
    Verify options -> runVerify options
    Copresheaves options -> runCopresheaves options
    Decompose options -> runDecompose options
    Generate options -> runGenerate options
    Profunctors options -> runProfunctors options
    Thin path -> runThin path

parserInfo :: ParserInfo Command
parserInfo =
  info
    (commandParser <**> helper)
    ( fullDesc
        <> progDesc "Exact enumeration and classification tools for finite categories"
    )

commandParser :: Parser Command
commandParser =
  hsubparser
    ( command "count" (info (Count <$> countParser) (progDesc "Enumerate categories by morphism count"))
        <> command "biconnected" (info (Biconnected <$> biconnectedParser) (progDesc "Enumerate categories with every hom-set nonempty"))
        <> command "verify" (info (Verify <$> verifyParser) (progDesc "Validate representative keys"))
        <> command "copresheaves" (info (Copresheaves <$> copresheafParser) (progDesc "Count bounded finite Set-valued copresheaves"))
        <> command "decompose" (info (Decompose <$> decomposeParser) (progDesc "Group categories by support-poset and biconnected component signature"))
        <> command "generate" (info (Generate <$> generateParser) (progDesc "Generate categories from quotient posets and cached biconnected components"))
        <> command "profunctors" (info (Profunctors <$> profunctorParser) (progDesc "Count finite profunctors between two category representatives"))
        <> command "thin" (info (Thin <$> argument str (metavar "DIGRAPH6_FILE")) (progDesc "Classify digraph6 relations as thin categories/preorders"))
    )

countParser :: Parser CountOptions
countParser =
  CountOptions
    <$> option auto (long "max-morphisms" <> metavar "N" <> help "Maximum total morphism count")
    <*> optional (option auto (long "objects" <> metavar "K" <> help "Restrict to exactly K objects"))
    <*> switch (long "connected-only" <> help "Only enumerate connected object graphs")
    <*> optional (strOption (long "write-reps" <> metavar "DIR" <> help "Write representative keys"))
    <*> switch (long "cauchy-complete" <> help "Keep only categories whose idempotents split")
    <*> representativeModeParser

biconnectedParser :: Parser BiconnectedOptions
biconnectedParser =
  BiconnectedOptions
    <$> option auto (long "max-morphisms" <> metavar "N" <> help "Maximum total morphism count")
    <*> optional (option auto (long "objects" <> metavar "K" <> help "Restrict to exactly K objects"))
    <*> optional (strOption (long "write-reps" <> metavar "DIR" <> help "Write canonical representative keys"))
    <*> switch (long "cauchy-complete" <> help "Keep only biconnected categories whose idempotents split")

verifyParser :: Parser VerifyOptions
verifyParser =
  VerifyOptions
    <$> argument str (metavar "FILE_OR_DIR")
    <*> switch (long "cauchy-complete" <> help "Require every representative to be Cauchy complete")

copresheafParser :: Parser CopresheafOptions
copresheafParser =
  CopresheafOptions
    <$> option auto (long "morphisms" <> metavar "N" <> help "Total morphism count of base categories")
    <*> option auto (long "max-elements" <> metavar "M" <> help "Maximum total elements in the finite copresheaf")
    <*> optional (option auto (long "objects" <> metavar "K" <> help "Restrict base categories to exactly K objects"))
    <*> switch (long "connected-only" <> help "Only use connected base categories")
    <*> switch (long "all-categories" <> help "Use all categories instead of only Cauchy-complete categories")

decomposeParser :: Parser DecomposeOptions
decomposeParser =
  DecomposeOptions
    <$> option auto (long "morphisms" <> metavar "N" <> help "Total morphism count")
    <*> optional (option auto (long "objects" <> metavar "K" <> help "Restrict to exactly K objects"))
    <*> switch (long "connected-only" <> help "Only use connected categories")
    <*> switch (long "cauchy-complete" <> help "Only use Cauchy-complete categories")
    <*> option auto (long "limit" <> metavar "L" <> value 10 <> help "Maximum number of signatures to print")

generateParser :: Parser GenerateOptions
generateParser =
  GenerateOptions
    <$> option auto (long "morphisms" <> metavar "N" <> help "Total morphism count")
    <*> optional (option auto (long "objects" <> metavar "K" <> help "Restrict to exactly K objects"))
    <*> switch (long "cauchy-complete" <> help "Generate only Cauchy-complete categories")
    <*> optional (strOption (long "write-reps" <> metavar "DIR" <> help "Write representative keys"))
    <*> representativeModeParser
    <*> switch (long "dual" <> help "Identify categories with their opposites (C ≅ C^op)")
    <*> switch (long "verbose" <> short 'v' <> help "Print categories as they are generated")

representativeModeParser :: Parser RepresentativeMode
representativeModeParser =
  flag' UpToEquivalence (long "up-to-equivalence" <> help "Search up to categorical equivalence")
    <|> flag' UpToIsomorphism (long "up-to-isomorphism" <> help "Search up to strict isomorphism")
    <|> flag' UpToEquality (long "up-to-equality" <> help "Keep raw generated category keys")
    <|> option
      parseRepresentativeMode
      ( long "up-to"
          <> metavar "MODE"
          <> value UpToIsomorphism
          <> showDefaultWith representativeModeName
          <> help "Representative relation: equivalence, isomorphism, or equality"
      )

parseRepresentativeMode :: ReadM RepresentativeMode
parseRepresentativeMode =
  eitherReader $ \raw ->
    case map toLower raw of
      "equivalence" -> Right UpToEquivalence
      "equiv" -> Right UpToEquivalence
      "isomorphism" -> Right UpToIsomorphism
      "isomorphisms" -> Right UpToIsomorphism
      "iso" -> Right UpToIsomorphism
      "equality" -> Right UpToEquality
      "equal" -> Right UpToEquality
      "raw" -> Right UpToEquality
      _ -> Left "expected equivalence, isomorphism, or equality"

profunctorParser :: Parser ProfunctorOptions
profunctorParser =
  ProfunctorOptions
    <$> strOption (long "left" <> metavar "FILE_OR_KEY" <> help "Left category key or file containing one key")
    <*> strOption (long "right" <> metavar "FILE_OR_KEY" <> help "Right category key or file containing one key")
    <*> option auto (long "max-elements" <> metavar "N" <> value 6 <> help "Maximum total elements to count")
    <*> optional (option parseProfile (long "profile" <> metavar "CSV" <> help "Count one row-major fiber-size profile"))

parseProfile :: ReadM [Int]
parseProfile =
  eitherReader $ \raw ->
    traverse readIntField (splitOnComma raw)
  where
    readIntField txt =
      case reads txt of
        [(parsed, "")] -> Right parsed
        _ -> Left ("invalid integer in profile: " ++ txt)

runCount :: CountOptions -> IO ()
runCount options = do
  maybe (pure ()) (createDirectoryIfMissing True) (optWriteReps options)
  forM_ [1 .. optMaxMorphisms options] $ \n -> do
    let groups =
          enumerateRepresentativeKeys
            (optRepresentativeMode options)
            n
            (optObjects options)
            (optConnectedOnly options)
            (optCauchyComplete options)
        total = sum (map (Set.size . snd) groups)
    putStrLn (show n ++ " morphisms: " ++ show total ++ label)
    forM_ groups $ \(k, keys) -> do
      putStrLn ("  " ++ show k ++ " objects: " ++ show (Set.size keys))
      forM_ (optWriteReps options) $ \dir -> do
        let fileName =
              "morphisms-"
                ++ show n
                ++ "-objects-"
                ++ show k
                ++ "-up-to-"
                ++ representativeModeName (optRepresentativeMode options)
                ++ ".cats"
        writeFile (dir </> fileName) (unlines (Set.toAscList keys))
  where
    label =
      if optCauchyComplete options
        then " Cauchy-complete categories up to " ++ representativeModeName (optRepresentativeMode options)
        else " categories up to " ++ representativeModeName (optRepresentativeMode options)

runBiconnected :: BiconnectedOptions -> IO ()
runBiconnected options = do
  maybe (pure ()) (createDirectoryIfMissing True) (biWriteReps options)
  forM_ [1 .. biMaxMorphisms options] $ \n -> do
    groups <-
      biconnectedCanonicalKeysCached
        n
        (biObjects options)
        (biCauchyComplete options)
    let total = sum (map (Set.size . snd) groups)
    putStrLn (show n ++ " morphisms: " ++ show total ++ label)
    forM_ groups $ \(k, keys) -> do
      putStrLn ("  " ++ show k ++ " objects: " ++ show (Set.size keys))
      forM_ (biWriteReps options) $ \dir -> do
        let fileName = "biconnected-morphisms-" ++ show n ++ "-objects-" ++ show k ++ ".cats"
        writeFile (dir </> fileName) (unlines (Set.toAscList keys))
  where
    label =
      if biCauchyComplete options
        then " Cauchy-complete biconnected categories"
        else " biconnected categories"

runVerify :: VerifyOptions -> IO ()
runVerify options = do
  let path = verifyPath options
  files <- inputFiles path
  results <- concat <$> traverse (verifyFile (verifyCauchyComplete options)) files
  let failures = [msg | Left msg <- results]
      successes = length [() | Right () <- results]
  putStrLn ("valid representatives: " ++ show successes)
  unless (null failures) $ do
    putStrLn ("failures: " ++ show (length failures))
    mapM_ putStrLn failures

inputFiles :: FilePath -> IO [FilePath]
inputFiles path = do
  isDir <- doesDirectoryExist path
  isFile <- doesFileExist path
  if isDir
    then do
      names <- listDirectory path
      pure [path </> name | name <- names]
    else if isFile
      then pure [path]
      else fail ("no such file or directory: " ++ path)

verifyFile :: Bool -> FilePath -> IO [Either String ()]
verifyFile requireCauchy path = do
  contents <- readFile path
  pure
    [ verifyLine requireCauchy path lineNo line
    | (lineNo, line) <- zip [1 :: Int ..] (lines contents)
    , not (null line)
    ]

verifyLine :: Bool -> FilePath -> Int -> String -> Either String ()
verifyLine requireCauchy path lineNo line = do
  cat <- withContext (parseCategoryKey line)
  let errors = validateCategory cat
  unless (null errors) $
    Left (context ++ ": " ++ unwords errors)
  when (canonicalKey cat /= categoryKey cat) $
    Left (context ++ ": representative is valid but not canonical")
  when requireCauchy $ do
    let cauchyErrors = cauchyCompletenessFailures cat
    unless (null cauchyErrors) $
      Left (context ++ ": " ++ unwords cauchyErrors)
  pure ()
  where
    context = path ++ ":" ++ show lineNo
    withContext = either (Left . ((context ++ ": ") ++)) Right

runCopresheaves :: CopresheafOptions -> IO ()
runCopresheaves options = do
  let cauchyOnly = not (copAllCategories options)
      groups =
        enumerateCanonicalCategories
          (copMorphisms options)
          (copObjects options)
          (copConnectedOnly options)
          cauchyOnly
      categories = concatMap snd groups
      counts = aggregateCounts (copMaxElements options) categories
      baseLabel =
        if cauchyOnly
          then " Cauchy-complete base categories"
          else " base categories"
  putStrLn (show (copMorphisms options) ++ " morphisms: " ++ show (length categories) ++ baseLabel)
  forM_ groups $ \(k, cats) ->
    putStrLn ("  " ++ show k ++ " objects: " ++ show (length cats))
  putStrLn ("finite copresheaves with <= " ++ show (copMaxElements options) ++ " total elements:")
  forM_ counts $ \(size, count) ->
    putStrLn ("  " ++ show size ++ " elements: " ++ show count)

aggregateCounts :: Int -> [FiniteCategory] -> [(Int, Integer)]
aggregateCounts maxElements categories =
  [ (size, sum [count | cat <- categories, (size', count) <- copresheafCountsUpTo maxElements cat, size' == size])
  | size <- [0 .. maxElements]
  ]

runDecompose :: DecomposeOptions -> IO ()
runDecompose options = do
  let groups =
        enumerateCanonicalCategories
          (decMorphisms options)
          (decObjects options)
          (decConnectedOnly options)
          (decCauchyComplete options)
      categories = concatMap snd groups
      signatureCounts = countSignatures (map decompositionSignature categories)
  putStrLn (show (decMorphisms options) ++ " morphisms: " ++ show (length categories) ++ label)
  forM_ groups $ \(k, cats) ->
    putStrLn ("  " ++ show k ++ " objects: " ++ show (length cats))
  putStrLn ("unique decomposition signatures: " ++ show (length signatureCounts))
  forM_ (take (decLimit options) signatureCounts) $ \(signature, count) -> do
    putStrLn ("  " ++ show count ++ " x " ++ signature)
  where
    label =
      if decCauchyComplete options
        then " Cauchy-complete categories"
        else " categories"

countSignatures :: [String] -> [(String, Int)]
countSignatures signatures =
  sortByCount
    [ (sig, length matches)
    | sig <- Set.toAscList (Set.fromList signatures)
    , let matches = filter (== sig) signatures
    ]

sortByCount :: [(String, Int)] -> [(String, Int)]
sortByCount [] = []
sortByCount (x:xs) =
  sortByCount larger ++ [x] ++ sortByCount smaller
  where
    larger = [y | y <- xs, snd y > snd x || (snd y == snd x && fst y < fst x)]
    smaller = [y | y <- xs, not (snd y > snd x || (snd y == snd x && fst y < fst x))]

runGenerate :: GenerateOptions -> IO ()
runGenerate options = do
  let mode = genRepresentativeMode options
      n = genMorphisms options
      objFilter = genObjects options
      cauchyOnly = genCauchyComplete options
      writeReps = genWriteReps options
      dual = genDual options
      verbose = genVerbose options
  maybe (pure ()) (createDirectoryIfMissing True) writeReps
  case mode of
    UpToEquality -> do
      counts <- equalityGeneratedCounts dual n objFilter cauchyOnly
      let total = sum (map snd counts)
      putStrLn (show n ++ " morphisms: " ++ show total ++ label mode cauchyOnly dual)
      forM_ counts $ \(k, count) -> do
        putStrLn ("  " ++ show k ++ " objects: " ++ show count)
    _ -> do
      groups <- componentGeneratedKeysCachedWith dual mode n objFilter cauchyOnly
      let total = sum (map (Set.size . snd) groups)
      when verbose $
        forM_ groups $ \(k, keys) -> do
          putStrLn $ "[k=" ++ show k ++ "] " ++ show (Set.size keys) ++ " categories:"
          forM_ (take 5 (Set.toAscList keys)) $ \key ->
            case parseCategoryKey key of
              Right cat -> putStrLn $ "  " ++ showCategory cat
              Left _    -> putStrLn $ "  (parse error)"
          when (Set.size keys > 5) $
            putStrLn $ "  ... and " ++ show (Set.size keys - 5) ++ " more"
      putStrLn (show n ++ " morphisms: " ++ show total ++ label mode cauchyOnly dual)
      forM_ groups $ \(k, keys) -> do
        putStrLn ("  " ++ show k ++ " objects: " ++ show (Set.size keys))
        forM_ writeReps $ \dir -> do
          let fileName =
                "generated-morphisms-"
                  ++ show n
                  ++ "-objects-"
                  ++ show k
                  ++ "-up-to-"
                  ++ representativeModeName mode
                  ++ (if dual then "-dual" else "")
                  ++ ".cats"
          writeFile (dir </> fileName) (unlines (Set.toAscList keys))
  where
    label mode cauchyOnly dual =
      let base = if cauchyOnly then " Cauchy-complete" else ""
          rel = representativeModeName mode ++ (if dual then " and dual" else "")
      in base ++ " generated categories up to " ++ rel

showCategory :: FiniteCategory -> String
showCategory cat =
  let k = fcObjectCount cat
      n = fcMorphismCount cat
      src = fcSources cat
      tgt = fcTargets cat
      ids = fcIdentities cat
      homCount s t = length [f | f <- [0 .. n-1], src V.! f == s, tgt V.! f == t]
      matrix = [show [homCount i j | j <- [0..k-1]] | i <- [0..k-1]]
      outIn = [ (sum [homCount i col | col <- [0..k-1]], sum [homCount row i | row <- [0..k-1]]) | i <- [0..k-1] ]
  in "k=" ++ show k ++ " n=" ++ show n ++ " matrix=[" ++ intercalate "," matrix ++ "] out/in=" ++ show (sort outIn)
  where
    sort = Data.List.sort

runProfunctors :: ProfunctorOptions -> IO ()
runProfunctors options = do
  left <- readCategoryArgument (profLeft options)
  right <- readCategoryArgument (profRight options)
  case profProfile options of
    Just profile -> do
      count <- countProfunctorsForProfileCached left right profile
      putStrLn ("profile " ++ csvInts profile ++ ": " ++ show count ++ " profunctors")
    Nothing -> do
      counts <- profunctorCountsUpToCached (profMaxElements options) left right
      putStrLn
        ( "finite profunctors with <= "
            ++ show (profMaxElements options)
            ++ " total elements:"
        )
      forM_ counts $ \(size, count) ->
        putStrLn ("  " ++ show size ++ " elements: " ++ show count)

readCategoryArgument :: FilePath -> IO FiniteCategory
readCategoryArgument raw = do
  exists <- doesFileExist raw
  if exists
    then do
      contents <- readFile raw
      parseCategoryText raw (firstNonEmptyLine contents)
    else parseCategoryText "category key" raw

firstNonEmptyLine :: String -> String
firstNonEmptyLine =
  head . filter (not . null) . lines

parseCategoryText :: String -> String -> IO FiniteCategory
parseCategoryText label text =
  case parseCategoryKey text of
    Right cat ->
      case validateCategory cat of
        [] -> pure cat
        errors -> fail (label ++ ": " ++ unwords errors)
    Left err -> fail (label ++ ": " ++ err)

csvInts :: [Int] -> String
csvInts = concatWith "," . map show

concatWith :: String -> [String] -> String
concatWith _ [] = ""
concatWith _ [x] = x
concatWith sep (x:xs) = x ++ sep ++ concatWith sep xs

splitOnComma :: String -> [String]
splitOnComma = splitOnChar ','

splitOnChar :: Char -> String -> [String]
splitOnChar sep = go []
  where
    go acc [] = [reverse acc]
    go acc (c:cs)
      | c == sep = reverse acc : go [] cs
      | otherwise = go (c : acc) cs

runThin :: FilePath -> IO ()
runThin path = do
  input <- TLIO.readFile path
  forM_ (classifyDigraph6Text input) $ \(lineNo, result) ->
    case result of
      Left err -> putStrLn ("line " ++ show lineNo ++ ": parse error: " ++ show err)
      Right report -> putStrLn (formatThin lineNo report)

formatThin :: Int -> ThinReport -> String
formatThin lineNo report =
  "line "
    ++ show lineNo
    ++ ": vertices="
    ++ show (thinVertices report)
    ++ " reflexive="
    ++ show (thinReflexive report)
    ++ " transitive="
    ++ show (thinTransitive report)
    ++ " antisymmetric="
    ++ show (thinAntisymmetric report)
    ++ " preorder="
    ++ show (thinReflexive report && thinTransitive report)
    ++ " poset="
    ++ show (thinReflexive report && thinTransitive report && thinAntisymmetric report)
