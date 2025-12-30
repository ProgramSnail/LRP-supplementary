-- Supplementary materials for the course of logic and relational programming, 2021
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- Unification.

module Unify where

import Control.Monad
import Data.List
import qualified Term as T
import qualified Test.QuickCheck as QC
import qualified Data.Map

-- Occurs-check for terms: return true, if
-- a variable occurs in the term
occurs :: T.Var -> T.T -> Bool
occurs = T.occurs'

-- Unification generic function. Takes an optional
-- substitution and two unifiable structures and
-- returns an MGU if exists
class Unifiable a where
  unify :: Maybe T.Subst -> a -> a -> Maybe T.Subst

  unifyUnc :: Maybe T.Subst -> (a, a) -> Maybe T.Subst
  unifyUnc s = uncurry $ unify s

instance Unifiable T.T where
  unify :: Maybe T.Subst -> T.T -> T.T -> Maybe T.Subst
  unify Nothing t u = Nothing
  unify (Just subst) t u = let t' = T.walk subst t in
                           let u' = T.walk subst u in
                           case (t', u') of
                             (T.V x, T.V y) | x == y -> Just subst
                             (T.V x, term) | not $ occurs x term ->
                               Just $ T.put subst x term
                             (term, T.V y) | not $ occurs y term ->
                               Just $ T.put subst y term
                             (T.C xCst xs, T.C yCst ys) | xCst == yCst &&
                                                          length xs == length ys ->
                               foldl unifyUnc (Just subst) $ zip xs ys
                             _ -> Nothing

-- An infix version of unification
-- with empty substitution
infix 4 ===

(===) :: T.T -> T.T -> Maybe T.Subst
(===) = unify (Just T.empty)

-- A quickcheck property
checkUnify :: (T.T, T.T) -> Bool
checkUnify (t, t') =
  case t === t' of
    Nothing -> True
    Just s  -> T.apply s t == T.apply s t'

-- This check should pass:
qcEntry = QC.quickCheck $ QC.withMaxSuccess 1000 $ (\ x -> QC.within 100000000 $ checkUnify x)

