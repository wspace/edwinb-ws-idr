module Interp

import Data.Vect

import Lang
import RawLang
import CheckLang
import Bounded

ErrMsg : Type
ErrMsg = String

doCheck : Stack k -> (i : Nat) -> Maybe (Stack i)
doCheck [] Z = Just []
doCheck [] (S k) = Nothing
doCheck (x :: xs) (S k) with (doCheck xs k)
   | Nothing = Nothing
   | Just stk = Just (x :: stk)
doCheck (x :: xs) Z = Just (Unchecked (x :: xs))
doCheck (Unchecked stk) n = doCheck stk n

drop : Stack (i + k) -> Stack k
drop {i = Z}   stk        = stk
drop {i = S k} (x :: stk) = drop stk

getHeap : Integer -> List Integer -> Integer
getHeap 0 (x :: xs) = x
getHeap n (x :: xs) = getHeap (n - 1) xs
getHeap n []        = 0

setHeap : Integer -> Integer -> List Integer -> List Integer
setHeap val 0 (x :: xs) = val :: xs
setHeap val n (x :: xs) = x :: setHeap val (n - 1) xs
setHeap val 0 [] = [val]
setHeap val n [] = if n > 0 then 0 :: setHeap val (n - 1) [] else []

interpStk : StackInst stkIn stkOut l -> Stack stkIn ->
            IO (Stack stkOut)
interpStk (PUSH n)  stk        = pure (n :: stk)
interpStk DUP       (x :: stk) = pure (x :: x :: stk)
interpStk (COPY n)  stk        = let val = lookup (mkBounded n) stk in
                                     pure (val :: stk)
interpStk SWAP      (x :: y :: stk) = pure (y :: x :: stk)
interpStk DISCARD   (x :: stk) = pure stk
interpStk (SLIDE n) (x :: stk) = pure (x :: drop stk)

interpArith : ArithInst stkIn stkOut l -> Stack stkIn ->
              IO (Stack stkOut)
interpArith ADD (x :: y :: stk) = pure (y + x :: stk)
interpArith SUB (x :: y :: stk) = pure (y - x :: stk)
interpArith MUL (x :: y :: stk) = pure (y * x :: stk)
interpArith DIV (x :: y :: stk) = pure ((y `div` x) :: stk)
interpArith MOD (x :: y :: stk) = pure ((y `mod` x) :: stk)

interpHeap : HeapInst stkIn stkOut l -> Stack stkIn -> List Integer ->
             IO (Stack stkOut, List Integer)
interpHeap STORE (val :: addr :: stk) hp
    = pure (stk, setHeap val addr hp)
interpHeap RETRIEVE (addr :: stk) hp
    = pure (getHeap addr hp :: stk, hp)

interpFlow : FlowInst stkIn stkOut l ->
             Prog stkOut stkOut' l ->
             LabelCache l ->
             Stack stkIn ->
             List Integer ->
             List (CallStackEntry l) ->
             IO (Maybe (Machine l))
interpFlow (LABEL x) next lblcache stk hp cs
    = pure (Just (MkMachine next lblcache (Unchecked stk) hp cs))
interpFlow (CALL x) ret lblcache stk hp cs
    = pure (Just (MkMachine (snd (lookup x lblcache)) lblcache
                              (Unchecked stk) hp (CSE ret :: cs)))
interpFlow (JUMP x) ret lblcache stk hp cs
    = pure (Just (MkMachine (snd (lookup x lblcache)) lblcache
                              (Unchecked stk) hp cs))
interpFlow (JZ x) next lblcache (0 :: stk) hp cs
    = pure (Just (MkMachine (snd (lookup x lblcache)) lblcache
                              (Unchecked stk) hp cs))
interpFlow (JZ x) next lblcache (_ :: stk) hp cs
    = pure (Just (MkMachine next lblcache stk hp cs))
interpFlow (JNEG x) next lblcache (val :: stk) hp cs
    = if (val < 0)
         then pure (Just (MkMachine (snd (lookup x lblcache)) lblcache
                           (Unchecked stk) hp cs))
         else pure (Just (MkMachine next lblcache stk hp cs))
interpFlow RETURN _ lblcache stk hp (CSE c :: cs)
    = pure (Just (MkMachine c lblcache (Unchecked stk) hp cs))
interpFlow RETURN _ lblcache stk hp []
    = do putStrLn "Call stack empty"
         pure Nothing
interpFlow END _ lblcache stk hp cs
    = pure Nothing -- TODO!

interpIO : IOInst stkIn stkOut l -> Stack stkIn -> List Integer ->
           IO (Stack stkOut, List Integer)
interpIO OUTPUT (x :: stk) hp
     = do let c : Char = cast (prim__truncBigInt_Int x)
          putChar c
          pure (stk, hp)
interpIO OUTPUTNUM (x :: stk) hp
     = do putStr (show x)
          pure (stk, hp)
interpIO READCHAR (addr :: stk) hp
     = do c <- getChar
          let x : Int = cast c
          pure (stk, setHeap (cast x) addr hp)
interpIO READNUM (addr :: stk) hp
     = do n <- getLine
          let x : Int = cast n
          pure (stk, setHeap (cast x) addr hp)

interpInst : Machine l -> IO (Maybe (Machine l))
interpInst (MkMachine (Lang.Nil) l s h c)
     = do putStrLn "Finished"
          pure Nothing
interpInst (MkMachine (Fl END :: prog) l s h c)
     = do putStrLn "Finished"
          pure Nothing
interpInst (MkMachine (Check x' i :: prog) l s h c)
    with (doCheck s x')
         | Just stk' = interpInst (MkMachine (i :: prog) l stk' h c)
         | Nothing   = do putStrLn ("Stack empty, need " ++ show x')
                          pure Nothing
interpInst (MkMachine (Stk i :: prog) l s h c)
     = do stk' <- interpStk i s
          pure (Just (MkMachine prog l stk' h c))
interpInst (MkMachine (Ar i :: prog) l s h c)
     = do stk' <- interpArith i s
          pure (Just (MkMachine prog l stk' h c))
interpInst (MkMachine (Hp i :: prog) l s h c)
     = do (stk', hp') <- interpHeap i s h
          pure (Just (MkMachine prog l stk' hp' c))
interpInst (MkMachine (Fl i :: prog) l s h c)
     = interpFlow i prog l s h c
interpInst (MkMachine (IOi i :: prog) l s h c)
     = do (stk', hp') <- interpIO i s h
          pure (Just (MkMachine prog l stk' hp' c))

export
loop : Machine l -> IO ()
loop m = do x' <- interpInst m
            case x' of
                 Just m' => loop m'
                 _ => pure ()
