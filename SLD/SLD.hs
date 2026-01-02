-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- SLD-resolution.

module SLD where

import Term
import Unify
import qualified Data.Map as Map
import qualified Control.Monad as Monad
import qualified Control.Monad.State as St
-- import Debug.Trace
import GHC.Stack (HasCallStack)
import Unify (walkRec)

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
  apply subst (aP, as) = (aP, map (apply subst) as)

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

walkRecA :: Subst -> A -> A
walkRecA subst (p, ts) = (p, map (walkRec subst) ts)

-- evalRec p ((hs, g, subst), stack, fresh) = undefined
-- Recursive evalutor: another semantics
evalRec :: HasCallStack => P -> State -> [Subst]
-- -- StopResult
evalRec p ((_, [], subst), [], fresh) = -- trace ("stop result: " ++ show subst) $
                                        [subst]
-- -- Stop
evalRec p (([], _, subst), [], fresh) = -- trace "stop" $
                                        []
-- -- BacktrackResult
evalRec p ((_, [], subst), t : ts, fresh) = -- trace ("backtrack result: " ++ show subst ++ " next st.sz=" ++ show (length ts)) $
                                            subst : evalRec p (t, ts, fresh)
-- -- Backtrack
evalRec p (([], _, subst), t : ts, fresh) = -- trace "backtrack" $
                                            evalRec p (t, ts, fresh)

evalRec p ((h@(hd :- tl) : hs, g : gs, subst), stack, fresh) =
  let (h'@(hd' :- tl'), fresh') = rename h fresh in
  let stack' = (hs, g : gs, subst) : stack in
  -- (if fst hd == fst g
  -- then trace ("evalRec: h' = " ++ show (hToValue h') ++ "\n         g =  " ++ show (map (aToValue . walkRecA subst) $ g : gs) ++ " st.sz = " ++ show (length stack))
  -- -- trace ("evalRec: h' = " ++ show h' ++ "\n         g =  " ++ show g ++
  -- --        "\n subst_before=" ++ show subst ++
  -- --        "\n goals_before=" ++ show (g : gs)) $ -- (map (walkRecA subst) $ g : gs)) $
  -- else id) $
  case unify (Just subst) hd' g of -- TODO: use walk rec at the end instead ??
-- -- MatchResult
    Just subst' | not $ null tl -> -- trace ("-> match result") $
                                       -- ++ "\n subst_after=" ++ show subst') $
                                   evalRec p ((p, map (apply subst') (tl' ++ gs), subst <+> subst'), stack', fresh' + 1)
-- -- NextGoal
                | otherwise -> -- trace ("-> next goal") $
                                  -- ++ "\n subst_after=" ++ show subst') $
                               evalRec p ((p, map (apply subst') gs, subst <+> subst'), stack', fresh' + 1)
-- -- MatchFailure
    Nothing -> -- trace "-> match failure" $
               evalRec p ((hs, g : gs, subst), stack, fresh' + 1)

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------


--- Debug construcitons
data Value = I Int
           | L [Value]
           | Va Int
           | Undef String
           | Value :+: Int
  deriving Show

termToValue :: T -> Value
termToValue (V v) = Va v
termToValue (C 0 _) = I 0
termToValue (C 1 [t]) | I n <- termToValue t = I $ n + 1
                      | v :+: n <- termToValue t = v :+: (n + 1)
                      | v <- termToValue t = v :+: 1
termToValue (C 2 _) = L []
termToValue (C 3 [h, t]) | x <- termToValue h, L xs <- termToValue t = L $ x : xs
termToValue t = Undef $ show t

aToValue :: A -> (Int, [Value])
aToValue (x, t) = (x, map termToValue t)

hToValue :: H -> [(Int, [Value])]
hToValue (hd :- tl) = aToValue hd : map aToValue tl

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
  -- mul (s o, x, x) :- [],
  mul (s x, y, z) :- [add (w, y, z), mul (x, y, w)]]

ltSpec = [
  lt (o, s x) :- [],
  lt (s x, s y) :- [lt (x, y)]]

leSpec = [
  le (o, x) :- [],
  le (s x, s y) :- [le (x, y)]]

sortSpec = ltSpec ++ leSpec ++ [
 insert (x, nil, cons x nil) :- [],
 insert (x, cons y xs, cons x $ cons y xs) :- [lt (x, y)],
 insert (x, cons y xs, cons y ys) :- [lt (y, x), insert (x, xs, ys)],

 sort' (nil, xs, xs) :- [],
 sort' (cons x xs, ys, zs) :- [insert (x, ys, ys'), sort' (xs, ys', zs)],

 sort (xs, ys) :- [sort' (xs, nil, ys)]]

--- Samples

s_add0 = case eval peano [add (s o, s o, x)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ show (apply h x)

s_add1 = case eval peano [add (x, s o, s $ s o)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ show (apply h x)

s_add2 = case eval peano [add (x, y, s $ s o)] of
          []               -> "error: should find a soultion"
          hs | length hs == 3 -> (++) "solutions: " $ concatMap (\h -> "x = " ++ show (apply h x) ++ "y = " ++ show (apply h y)++ "\n           ") hs
             | otherwise -> show (length hs) ++ " solutions found"

s_mul0 = case eval mult [mul (s $ s o, s $ s o, x)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ show (apply h x)

s_mul1 = case eval mult [mul (x, s $ s o, s $ s $ s $ s o)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ show (apply h x)

s_mul2 = case eval mult [mul (s $ s o, x, s $ s $ s $ s o)] of
          []    -> "error: should find a solution"
          h : _ -> "solution: " ++ show (apply h x)

s_mul3 = case take 3 $ eval mult [mul (x, y, s $ s $ s $ s o)] of
            []                  -> "error: should find a soultion"
            hs | length hs == 3 -> (++) "solutions: " $ concatMap (\h -> "x = " ++ show (apply h x) ++ "y = " ++ show (apply h y)++ "\n           ") hs
               | otherwise      -> "error: " ++ show (length hs) ++ " solutions found"

s_sort0 = case  eval sortSpec [sort (cons (s o) $ cons (s $ s $ s o) $ cons (s $ s o) nil, x)] of
            []    -> "error: should find a solution"
            h : _ -> "solution: " ++ show (apply h x)

s_sort1 = case eval sortSpec [sort (cons (s $ s o) $ cons (s $ s $ s o) $ cons (s o) nil, x)] of
             []    -> "error: should find a solution"
             h : _ -> "solution: " ++ show (apply h x)

-- NOTE: inf, incompl problem
-- s_sort2 = case take 6 $ eval sortSpec [sort (x, cons (s o) $ cons (s $ s o) $ cons (s $ s $ s o) nil)] of
--             []                  -> "error: should find a soultion"
--             hs | length hs == 6 -> (++) "solutions: " $ concatMap (\h -> "x = " ++ show (apply h x) ++ "\n           ") hs
--                | otherwise      -> "error: " ++ show (length hs) ++ " solutions found"

-- NOTE: inf
-- s_sort3 = case eval sortSpec [sort (x, cons (s o) $ cons (s $ s $ s o) $ cons (s $ s o) nil)] of
--             []    -> "no solutions as expected"
--             _     -> "error: solutions found"

