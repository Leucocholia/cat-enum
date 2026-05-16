module CodexSlop.Thin
  ( ThinReport(..)
  , classifyDigraph6Text
  ) where

import Data.Word (Word64)
import qualified Data.Text.Lazy as TL
import qualified Nauty.Digraph6 as D

data ThinReport = ThinReport
  { thinVertices :: !Int
  , thinReflexive :: !Bool
  , thinTransitive :: !Bool
  , thinAntisymmetric :: !Bool
  } deriving (Eq, Show)

classifyDigraph6Text :: TL.Text -> [(Int, Either TL.Text ThinReport)]
classifyDigraph6Text input =
  [ (lineNo, fmap classify (D.digraph line))
  | (lineNo, line) <- zip [1 ..] (TL.lines input)
  , keepLine line
  ]

classify :: D.AdjacencyMatrix -> ThinReport
classify matrix =
  ThinReport
    { thinVertices = fromIntegral n
    , thinReflexive = reflexive
    , thinTransitive = transitive
    , thinAntisymmetric = antisymmetric
    }
  where
    n = D.numberOfVertices matrix
    vertices = [0 .. n - 1]
    edge = D.arcExists matrix
    reflexive = all (\x -> edge x x) vertices
    transitive =
      and
        [ not (edge x y && edge y z) || edge x z
        | x <- vertices
        , y <- vertices
        , z <- vertices
        ]
    antisymmetric =
      and
        [ x == y || not (edge x y && edge y x)
        | x <- vertices
        , y <- vertices
        ]

keepLine :: TL.Text -> Bool
keepLine line =
  let stripped = TL.strip line
  in not (TL.null stripped) && stripped /= TL.pack ">>digraph6<<"

_word64Anchor :: Word64 -> Word64
_word64Anchor = id
