-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- MicroKanren.

module MK where

import Data.Maybe
import Control.Monad
import Control.Applicative
import qualified Term as T
import qualified Unify as U
import Term ((<+>))
-- import Debug.Trace (trace)

data Stream a =
  Nil                 |
  Mature a (Stream a) |
  Immature (Stream a) deriving Functor

pick n s =
  case n of
    0 -> []
    _ -> case s of
           Nil           -> []
           Mature   h tl -> h : pick (n-1) tl
           Immature fs   -> pick n fs

instance Applicative Stream where
  pure  = flip Mature Nil
  (<*>) = ap

instance Alternative Stream where
  empty = mzero
  (<|>) = mplus
 
instance Monad Stream where
  Nil >>= f = Nil
  Mature x xs >>= f = f x <|> (xs >>= f)
  Immature xs >>= f = Immature $ xs >>= f 

instance MonadPlus Stream where
  mzero = Nil
  Nil `mplus` ys = ys
  Mature x xs `mplus` ys = Mature x $ ys `mplus` xs
  Immature xs `mplus` ys = Immature $ ys `mplus` xs

 -- subst & first fresh
type State = (T.Subst, Int)
type Goal  = State -> Stream State

infix 4 ===

(===) :: T.T -> T.T -> Goal
(===) t1 t2 (subst, x) =
  case U.unify (Just subst) t1 t2 of
    Just subst' -> return (subst <+> subst', x)
    Nothing -> Nil

infixr 3 &&&

(&&&) :: Goal -> Goal -> Goal
(&&&) g1 g2 s = do s' <- g1 s
                   g2 s'

infixr 2 |||

(|||) :: Goal -> Goal -> Goal
(|||) g1 g2 s = g1 s <|> g2 s

callFresh :: (T.T -> Goal) -> Goal
callFresh f (subst, x) = f (T.V x) (subst, succ x)

delay :: Goal -> Goal
delay f s = Immature $ f s

--- Initial state & run
initial = (T.empty, 1000)
peep x (s, _) = map (T.apply s) x
runN n peeper goal = map peeper $ pick n $ goal initial
run = runN (-1)

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = T.V 0
y = T.V 1
z = T.V 2

--- Terms
o        = T.C 0 []
s t      = T.C 1 [t]
nil      = T.C 2 []
cons h t = T.C 3 [h, t]

add x y z = delay $
  -- trace ("add: " ++ show x ++ " " ++ show y ++ " " ++ show z) $
  x === o &&& y === z |||
  callFresh (\ x' ->
  callFresh (\ z' ->
    x === s x' &&&
    z === s z' &&&
    add x' y z'
  ))

mul x y z = delay $
  -- trace ("mul: " ++ show x ++ " " ++ show y ++ " " ++ show z) $
  x === o &&& z === o |||
  callFresh(\ x' ->
  callFresh(\ w  ->
    x === s x' &&&
    mul x' y w &&&
    add w y z
  ))

lt x y = delay $
  -- trace ("lt: " ++ show x ++ " " ++ show y) $
  callFresh(\ y' ->
    x === o &&& y === s y') |||
  callFresh(\ x' ->
  callFresh(\ y' ->
    x === s x' &&&
    y === s y' &&&
    lt x' y'
  ))

le x y = delay $
  -- trace ("le: " ++ show x ++ " " ++ show y) $
  x === o |||
  callFresh(\ x' ->
  callFresh(\ y' ->
    x === s x' &&&
    y === s y' &&&
    le x' y'
  ))

insert x xs ys = delay $
  -- trace ("insert: " ++ show x ++ " " ++ show xs ++ " " ++ show ys) $
  xs === nil &&& ys === cons x nil |||
  callFresh(\ y ->
  callFresh(\ zs ->
    xs === cons y zs &&&
    ys === cons x (cons y zs) &&&
    lt x y
  )) |||
  callFresh(\ y ->
  callFresh(\ xs' ->
  callFresh(\ ys' ->
    xs === cons y xs' &&&
    ys === cons y ys' &&&
    lt y x &&&
    insert x xs' ys'
  )))

sort' xs ys zs = delay $
  -- trace ("sort': " ++ show xs ++ " " ++ show ys ++ " " ++ show zs) $
  xs === nil &&& ys === zs |||
  callFresh(\ x ->
  callFresh(\ xs' ->
  callFresh(\ ys' ->
    xs === cons x xs' &&&
    insert x ys ys' &&&
    sort' xs' ys' zs
  )))

sort xs ys =
  -- trace ("sort: " ++ show xs ++ " " ++ show ys) $
  sort' xs nil ys

s_add0 = run (peep [x])    $ add (s o) (s o) x
s_add1 = run (peep [x])    $ add x (s o) (s (s o))
s_add2 = run (peep [x, y]) $ add x y (s (s o))
-- NOTE: inf
-- s_add3 = run (peep [x, y]) $ add x (s (s o)) y

s_mul0 = run (peep [x])       $ mul (s $ s o) (s $ s o) x
s_mul1 = runN 1 (peep [x])    $ mul x (s $ s o) (s $ s $ s $ s o)
s_mul2 = run (peep [x])       $ mul (s $ s o) x (s $ s $ s $ s o)
s_mul3 = runN 3 (peep [x, y]) $   mul x y (s $ s $ s $ s o) -- all results found due to compl

s_sort0 = run (peep [x]) $ sort (cons (s o) $ cons (s $ s $ s o) $ cons (s $ s o) nil) x
s_sort1 = run (peep [x]) $ sort (cons (s $ s o) $ cons (s $ s $ s o) $ cons (s o) nil) x
s_sort2 = runN 6 (peep [x]) $ sort x (cons (s o) $ cons (s $ s o) $ cons (s $ s $ s o) nil)
-- NOTE: inf
-- s_sort3 = run (peep [x]) $ sort x (cons (s o) $ cons (s $ s $ s o) $ cons (s $ s o) nil)
