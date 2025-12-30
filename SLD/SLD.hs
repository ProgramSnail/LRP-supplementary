-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- SLD-resolution.

module SLD where

import Term
import Unify
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Control.Monad.State as St
import Debug.Trace
import GHC.Stack (HasCallStack)

-- Predicate names
type Pred = Int

-- Atomic formula
type A = (Pred, [T])

-- A class type to convert data structures to/from
-- atomic formulas
class Atomic a where
  toAtomic   :: a -> A
  fromAtomic :: A -> a

-- Horn clause
data H = A :- [A] deriving Show

-- Program
type P = [H]

-- Unification for atomic formulas -- ??
instance Unifiable A where
  unify subst (aP, as) (bP, bs) | aP == bP = foldl unifyUnc subst $ zip as bs
                                | otherwise = Nothing

-- Substitution application to atomic formulas
instance Substitutable A where
  apply subst (aP, as) = (aP, fmap (apply subst) as)

-- State
--   1. A triple
--      1. a tail of a program to match against
--      2. current goal
--      3. current substitution
--   2. A stack of triplets as in the previous item
--   3. An index of first fresh variable
type Triplet = (P, [A], Subst)
type State   = (Triplet, [Triplet], Var)

-- Makes an initial state from a program and list of goals
-- 1000 is a hardcoded maximal number of variables in a goal
initState :: P -> [A] -> State
initState p g = ((p, g, empty), [], 1000)

-- Refresh all variables in a term
refresh :: T -> St.State (Var, Map.Map Var Var) T
refresh (V x) = do
  (i, m) <- St.get
  case Map.lookup x m of
    Nothing ->
      do St.put (i+1, Map.insert x i m)
         return (V i)
    Just j -> return (V j)
refresh (C c ts) = Monad.liftM (C c) $ mapM refresh ts

-- Refresh all variables in atomic formula
refreshA :: A -> St.State (Var, Map.Map Var Var) A
refreshA (p, ts) = Monad.liftM (p,) $ mapM refresh ts

-- Refresh all variables in a horn clause
refreshH :: H -> St.State (Var, Map.Map Var Var) H
refreshH (a :- as) = Monad.liftM (\ (a:as) -> (a :- as)) $ mapM refreshA (a:as)

-- Rename a clause
rename :: H -> Var -> (H, Var)
rename h v =
  let (h', (v', _)) = St.runState (refreshH h) (v, Map.empty) in
  (h', v')

-- Top-level evaluator: takes
--   1. a program
--   2. a query
--   3. returns a list of substitutions
eval :: P -> [A] -> [Subst]
eval p g = evalRec p $ initState p g

-- Recursive evalutor
evalRec' :: P -> State -> [Subst]
-- -- StopResult
evalRec' p (([], [], subst), [], fresh) = [subst]
-- -- Stop
evalRec' p (([], _, subst), [], fresh) = []
-- -- BacktrackResult
evalRec' p (([], [], subst), t : ts, fresh) = subst : evalRec p (t, ts, fresh)
-- -- Backtrack
evalRec' p (([], _, subst), t : ts, fresh) = evalRec p (t, ts, fresh)

evalRec' p ((h@(hd :- tl) : hs, g : gs, subst), stack, fresh) =
  let (h'@(hd' :- tl'), fresh') = rename h fresh in
  let stack' = (hs, g : gs, subst) : stack in
  case unify (Just subst) hd' g of
-- -- MatchResult
    Just subst' | null tl -> evalRec p ((p, tl' ++ gs, subst'), stack', fresh')
-- -- NextGoal
                | otherwise -> evalRec p ((p, gs, subst'), stack', fresh')
-- -- MatchFailure
    Nothing -> evalRec p ((hs, g : gs, subst), stack, fresh)

-- evalRec p ((hs, g, subst), stack, fresh) = undefined

-- Recursive evalutor: another semantics
evalRec :: HasCallStack => P -> State -> [Subst]
-- -- StopResult
evalRec p ((_, [], subst), [], fresh) = trace "stop result" $
                                        [subst]
-- -- Stop
evalRec p (([], _, subst), [], fresh) = trace "stop" $
                                        []
-- -- BacktrackResult
evalRec p ((_, [], subst), t : ts, fresh) = trace "backtrack result" $
                                            subst : evalRec p (t, ts, fresh)
-- -- Backtrack
evalRec p (([], _, subst), t : ts, fresh) = trace "backtrack" $
                                            evalRec p (t, ts, fresh)

evalRec p ((h@(hd :- tl) : hs, g : gs, subst), stack, fresh) =
  let (h'@(hd' :- tl'), fresh') = rename h fresh in
  let stack' = (hs, g : gs, subst) : stack in
  trace ("evalRec: h' = " ++ show h' ++ "\n         g =  " ++ show g ++
         "\n subst_before=" ++ show subst ++
         "\n goals_before=" ++ show (g : gs)) $
  case unify (Just subst) hd' g of
-- -- MatchResult
    Just subst' | not $ null tl -> trace ("-> match result" ++
                                          "\n subst_after=" ++ show subst') $
                                   evalRec p ((p, tl' ++ gs, subst'), stack', fresh')
-- -- NextGoal
                | otherwise -> trace ("-> next goal" ++
                                      "\n subst_after=" ++ show subst') $
                               evalRec p ((p, gs, subst'), stack', fresh')
-- -- MatchFailure
    Nothing -> trace "-> match failure" $
               evalRec p ((hs, g : gs, subst), stack, fresh)

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = V 0
y = V 1
z = V 2
w = V 3
xs = V 4
ys = V 5
zs = V 6
x' = V 7
y' = V 8
ys' = V 9

--- Terms
o        = C 0 []
s t      = C 1 [t]
nil      = C 2 []
cons h t = C 3 [h, t]

--- Predicates
add (x, y, z) = (0, [x, y, z])
mul (x, y, z) = (1, [x, y, z])
lt  (x, y)    = (2, [x, y])
le  (x, y)    = (3, [x, y])
sort (x, y)   = (4, [x, y])
sort' (x, y, z)   = (5, [x, y, z])
insert (x, y, z)   = (6, [x, y, z])

--- Specifications
peano = [
  add (o, x, x) :- [],
  add (s x, y, s z) :- [add (x, y, z)]]

mult = peano ++ [
  mul (o, x, o) :- [],
  mul (s o, x, x) :- [],
  mul (s x, y, z) :- [add(w, y, z), mul (x, y, w)]]

ltSpec = [
  lt (o, s x) :- [],
  lt (s x, s y) :- [lt (x, y)]]

leSpec = [
  le (o, x) :- [],
  le (s x, s y) :- [le (x, y)]]

sortSpec = ltSpec ++ leSpec ++ [
 insert (x, nil, cons x nil) :- [],
 insert (x, cons y xs, cons y ys) :- [lt (y, x), insert (x, xs, ys)],
 insert (x, cons y xs, cons x $ cons y ys) :- [le (x, y)],

 sort' (nil, xs, xs) :- [],
 sort' (cons x xs, ys, zs) :- [insert(x, ys, ys'), sort' (xs, ys', zs)],
 sort (xs, ys) :- [sort' (xs, nil, ys)]]

--- Samples
s_add0 = case eval peano [add (s o, s o, x)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ (show $ apply h x)

s_add1 = case eval peano [add (x, s o, s $ s o)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ (show $ apply h x)

s_add2 = case eval peano [add (x, y, s $ s o)] of
          []               -> "error: should find a soultion"
          h1 : h2 : h3 : _ -> "solutions: x = " ++ (show $ apply h1 x) ++ ", y = " ++ (show $ apply h1 y) ++ "\n" ++
                              "           x = " ++ (show $ apply h2 x) ++ ", y = " ++ (show $ apply h2 y) ++ "\n" ++
                              "           x = " ++ (show $ apply h3 x) ++ ", y = " ++ (show $ apply h3 y) ++ "\n"
          hs -> show (length hs) ++ " solutions found"

s_add3 = case eval peano [add (x, y, s $ s $ s $ s o)] of
          []               -> "error: should find a soultion"
          h1 : h2 : h3 : h4 : h5 : _ -> "solutions: x = " ++ (show $ apply h1 x) ++ ", y = " ++ (show $ apply h1 y) ++ "\n" ++
                              "           x = " ++ (show $ apply h2 x) ++ ", y = " ++ (show $ apply h2 y) ++ "\n" ++
                              "           x = " ++ (show $ apply h3 x) ++ ", y = " ++ (show $ apply h3 y) ++ "\n"
          hs -> show (length hs) ++ " solutions found"

s_mul0 = case eval mult [mul (s $ s o, s $ s o, x)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ (show $ apply h x)

s_mul1 = case eval mult [mul (x, s $ s $ o, s $ s $ s $ s o)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ (show $ apply h x)

s_mul2 = case eval mult [mul (s $ s $ o, x, s $ s $ s $ s o)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ (show $ apply h x)

s_mul3 = case take 3 $ eval mult [mul (x, y, s $ s $ s $ s $ s $ s $ s $ s $ s $ s o)] of
            []    -> "error: should find a soultion"
            h1 : h2 :  h3 : h4 : _ -> "solutions: x = " ++ (show $ apply h1 x) ++ ", y = " ++ (show $ apply h1 y) ++ "\n" ++
                                "           x = " ++ (show $ apply h2 x) ++ ", y = " ++ (show $ apply h2 y) ++ "\n"
            hs -> show (length hs) ++ " solutions found"

s_sort0 = case eval sortSpec [sort (cons (s o) $ cons (s $ s $ s o) $ cons (s $ s o) nil, x)] of
            []    -> "error: should find a solution"
            h : _ -> "solution: " ++ (show $ apply h x)

-- TODO: wrong
s_sort0' = case eval sortSpec [sort (cons (s $ s o) $ cons (s $ s $ s o) $ cons (s o) nil, x)] of
             []    -> "error: should find a solution"
             h : _ -> "solution: " ++ (show $ apply h x)

s_sort1 = case eval sortSpec [sort (x, cons (s o) $ cons (s $ s $ s o) $ cons (s $ s o) nil)] of
            []    -> "no solutions as expected"
            _ -> "error: solutions found"

s_sort2 = case eval sortSpec [sort (x, cons (s o) $ cons (s $ s o) $ cons (s $ s $ s o) nil)] of
            []    -> "error: should find a solution"
            hs -> show (length hs) ++ " solutions found"

