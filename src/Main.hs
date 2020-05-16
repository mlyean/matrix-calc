{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad (replicateM)
import Control.Monad.Trans.State.Strict
import System.IO

import Data.Bifunctor (bimap)
import Data.List (intersperse)
import Data.Matrix hiding (luDecomp, rref)
import Data.Ratio
import qualified Data.Vector as V

import Text.LaTeX
import Text.LaTeX.Packages.AMSMath

-- Utility functions
blend :: [a] -> [a] -> [a]
blend (x:xs) ys = x : blend ys xs
blend _ _ = []

-- Elementary row operations
data ElemOp a
  = MulBy Int a
  | AddMultTo Int a Int
  | Swap Int Int
  deriving (Show)

-- Apply an elementary row operation to a matrix
doOp :: Num a => ElemOp a -> Matrix a -> Matrix a
doOp (MulBy n c) mat = scaleRow c n mat
doOp (AddMultTo m c n) mat = combineRows n c m mat
doOp (Swap m n) mat = switchRows m n mat

doOps :: Num a => [ElemOp a] -> Matrix a -> Matrix a
doOps l m = foldr doOp m l

invOp :: Fractional a => ElemOp a -> ElemOp a
invOp (MulBy n c) = MulBy n (1 / c)
invOp (AddMultTo m c n) = AddMultTo m (-c) n
invOp (Swap m n) = Swap m n

-- Simplification rules
simplifyOps :: (Num a, Eq a) => [ElemOp a] -> [ElemOp a]
simplifyOps (MulBy m c:MulBy n d:xs) =
  if m == n
    then simplifyOps (MulBy m (c * d) : xs)
    else simplifyOps (MulBy n d : xs)
simplifyOps (MulBy m c:xs) =
  if c == 1
    then simplifyOps xs
    else MulBy m c : simplifyOps xs
simplifyOps (AddMultTo m c n:xs) =
  if c == 0
    then simplifyOps xs
    else AddMultTo m c n : simplifyOps xs
simplifyOps (Swap m n:xs) =
  if m == n
    then simplifyOps xs
    else Swap m n : simplifyOps xs
simplifyOps [] = []

type OpState a = State [ElemOp a] (Matrix a)

doOpState :: Num a => ElemOp a -> OpState a -> OpState a
doOpState op = mapState (bimap (doOp op) ((:) op))

doOpsState :: Num a => [ElemOp a] -> OpState a -> OpState a
doOpsState ops s = foldr doOpState s ops

-- Use (row, col) as a pivot to eliminate rows below the given row
-- Assumes mat ! (row, col) == 1
elimDownWithPivot :: Num a => Int -> Int -> OpState a -> OpState a
elimDownWithPivot row col = helper (succ row)
  where
    helper crow s
      | crow > nrows mat = s
      | otherwise =
        helper
          (succ crow)
          (doOpState (AddMultTo row (-(mat ! (crow, col))) crow) s)
      where
        mat = evalState s []

findNonZeroBelow :: (Num a, Eq a) => Int -> Int -> Matrix a -> Maybe Int
findNonZeroBelow row col mat =
  succ . fst <$>
  V.find ((/= 0) . snd) (V.drop (pred row) $ V.indexed $ getCol col mat)

-- Gaussian elimination
gaussianElim :: (Fractional a, Eq a) => OpState a -> OpState a
gaussianElim = helper 1 1
  where
    helper row col s
      | row > nrows mat = s
      | col > ncols mat = s
      | otherwise =
        case findNonZeroBelow row col mat of
          Just r ->
            helper
              (succ row)
              (succ col)
              (elimDownWithPivot
                 row
                 col
                 (doOpsState [MulBy row (1 / (mat ! (r, col))), Swap row r] s))
          Nothing -> helper row (succ col) s
      where
        mat = evalState s []

-- LU Decomposition
luDecomp :: (Fractional a, Eq a) => Matrix a -> (Matrix a, Matrix a)
luDecomp mat = (doOps (reverse (map invOp lops)) (identity (nrows mat)), u)
  where
    (u, lops) = runState (gaussianElim (return mat)) []

-- Rank of a matrix
rank :: (Fractional a, Eq a) => Matrix a -> Int
rank mat = sum $ map (fromEnum . any (/= 0)) $ toLists $ snd $ luDecomp mat

-- Nullity of a matrix
nullity :: (Fractional a, Eq a) => Matrix a -> Int
nullity mat = sum $ map (fromEnum . all (== 0)) $ toLists $ snd $ luDecomp mat

-- Use (row, col) as a pivot to eliminate rows above the given row
-- Assumes mat ! (row, col) == 1
elimUpWithPivot :: Num a => Int -> Int -> OpState a -> OpState a
elimUpWithPivot row col = helper 1
  where
    helper crow s
      | crow >= row = s
      | otherwise =
        helper
          (succ crow)
          (doOpState (AddMultTo row (-(mat ! (crow, col))) crow) s)
      where
        mat = evalState s []

-- Given a row, find the first column with a nonzero entry on that row
findNonZeroRight :: (Num a, Eq a) => Int -> Matrix a -> Maybe Int
findNonZeroRight row mat =
  succ . fst <$> V.find ((/= 0) . snd) (V.indexed (getRow row mat))

-- Row reduced echelon form
rref :: (Fractional a, Eq a) => OpState a -> OpState a
rref = helper 0 . gaussianElim
  where
    helper r s
      | row < 1 = s
      | otherwise =
        case findNonZeroRight row mat of
          Just c -> helper (succ r) (elimUpWithPivot row c s)
          Nothing -> helper (succ r) s
      where
        row = nrows mat - r
        mat = evalState s []

-- Matrix inverse
invert :: (Fractional a, Eq a) => Matrix a -> Matrix a
invert mat = doOps (execState (rref (return mat)) []) (identity (nrows mat))

-- Pretty printing
newtype Rat =
  Rat Rational

instance Texy Rat where
  texy (Rat r)
    | denominator r == 1 = texy (numerator r)
    | r >= 0 = frac (texy (numerator r)) (texy (denominator r))
    | otherwise = "-" <> frac (texy (-numerator r)) (texy (denominator r))

pprintOp :: Monad m => ElemOp Rational -> LaTeXT_ m
pprintOp (MulBy n c) =
  "Multiply row " <> math (texy n) <> " by " <> math (texy (Rat c))
pprintOp (AddMultTo m c n)
  | c == 1 = "Add row " <> math (texy m) <> " to row " <> math (texy n)
  | c == -1 = "Subtract row " <> math (texy m) <> " from row " <> math (texy n)
  | c >= 0 =
    "Add " <>
    math (texy (Rat c)) <>
    " times row " <> math (texy m) <> " to row " <> math (texy n)
  | otherwise =
    "Subtract " <>
    math (texy (Rat (-c))) <>
    " times row " <> math (texy m) <> " from row " <> math (texy n)
pprintOp (Swap m n) = "Swap rows " <> math (texy m) <> " and " <> math (texy n)

rrefStepByStep :: Monad m => Matrix Rational -> LaTeXT_ m
rrefStepByStep mat =
  mconcat $
  intersperse lnbk $
  blend
    (map (equation_ . pmatrix Nothing . mapPos (\_ x -> Rat x)) res)
    (map pprintOp steps)
  where
    steps = reverse $ simplifyOps $ execState (rref (return mat)) []
    res = scanl (flip doOp) mat steps

-- IO
readMatrix :: IO (Matrix Rational)
readMatrix = do
  putStr "Number of rows: "
  n <- readLn :: IO Int
  putStrLn "Input matrix: "
  l <-
    replicateM n (map (fromIntegral . read) . words <$> getLine) :: IO [[Rational]]
  return $ fromLists l

-- LaTeX
solve :: Monad m => Matrix Rational -> LaTeXT_ m
solve mat = do
  thePreamble
  document (theBody mat)

thePreamble :: Monad m => LaTeXT_ m
thePreamble = do
  documentclass [] article
  usepackage [] amsmath
  title "Calculating the RREF of a Matrix"
  date ""

theBody :: Monad m => Matrix Rational -> LaTeXT_ m
theBody mat = do
  maketitle
  rrefStepByStep mat

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  mat <- readMatrix
  execLaTeXT (solve mat) >>= renderFile "steps.tex"
