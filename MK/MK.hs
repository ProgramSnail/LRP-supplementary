-- Supplementary materials for the course of logic and relational programming, 2025
-- (C) Dmitry Boulytchev, dboulytchev@gmail.com
-- MicroKanren.

module MK where

import Data.Maybe
import Control.Monad
import Control.Applicative
import qualified Term as T
import qualified Unify as U

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

instance MonadPlus Stream where
  mzero = Nil
  Nil `mplus` ys = ys
  Mature x xs `mplus` ys = Mature x $ ys `mplus` xs
  Immature xs `mplus` ys = ys `mplus` xs

 -- subst & first fresh
type State = (T.Subst, Int)
type Goal  = State -> Stream State

infix 4 ===

(===) :: T.T -> T.T -> Goal
(===) t1 t2 (subst, x) =
  case U.unify (Just subst) t1 t2 of
    Just subst' -> return (subst', x)
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
run peeper goal = map peeper $ pick (-1) $ goal initial

------------------------------------------
--- Some relations for natural numbers ---
------------------------------------------

--- Some predefined variables
x = T.V 0
y = T.V 1
z = T.V 2

--- Terms
o   = T.C 0 []
s t = T.C 1 [t]

add x y z = delay $
  x === o &&& y === z |||
  callFresh (\ x' ->
  callFresh (\ z' ->
    x === s x' &&&
    z === s z' &&&
    add x' y z'
  ))

s0 = run (peep [x])    (add (s o) (s o) x)
s1 = run (peep [x])    (add x (s o) (s (s o)))
s2 = run (peep [x, y]) (add x y (s (s o)))
