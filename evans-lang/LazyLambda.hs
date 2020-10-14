module LazyLambda
(
LambdaTerm,
smallstep
) where

import qualified Data.Stream as Stream
import Control.Monad.ST
import Control.Monad.State
import qualified Data.Set as S
import Data.List
import Data.STRef

{-- The idea is that the input will be with strings but to avoid complications in
substitution we can use integers when substituting --}
type VarName = Either String Int

type FreshNames = Stream.Stream VarName

newtype EvalState = EvalState {freshnames :: FreshNames}
data LambdaTerm = Lambda VarName LambdaTerm | Application LambdaTerm LambdaTerm | Var VarName
data InternalLambda = Orig LambdaTerm | LazyRef (STRef _ LambdaTerm)

eval :: LambdaTerm -> LambdaTerm
eval x = runST $ evalHelp x
  where
    evalHelp :: LambdaTerm -> ST s LambdaTerm
    evalHelp _ = undefined
      where


        getFresh :: State EvalState VarName
        getFresh state = (Stream.head $ freshnames state, state {freshnames = Stream.tail $ freshnames state})

        --fv e gives a list of all free variables in e
        fv :: InternalLambda -> S.Set VarName
        fv (Lambda x e) = S.delete x $ fv_help e
        fv (Application e1 e2) = S.union (fv_help e1) (fv_help e2)
        fv (Var x) = S.singleton x
        fv (LazyRef _) = undefined

        --sub e1 var e2 state = (e1[e2/var], newState)
        --sub :: LambdaTerm -> VarName -> LambdaTerm -> State EvalState (ST s LambdaTerm)
        sub e1 var e2 = if S.notMember var (fv e1) then return $ return e1
                                  else return $ do
                                    e2Ref <- newSTRef e2
                                    subHelp var e2Ref e1
          where
            --subHelp :: VarName -> STRef LambdaTerm -> LambdaTerm -> State EvalState (ST s LambdaTerm)
            subHelp var e2Ref e  =
              case e of Lambda x e1 -> lambdaCase x e1
                        Application e1 e2 -> return $ Application (subInto e1) (subInto e2)
                        Var x -> if var == x then newTerm else return $ Var x
                        LazyRef otherID -> undefined
              where
                newTerm = LazyRef refID
                subInto = subHelp var refID
                lambdaCase :: VarName -> LambdaTerm -> State (ST s LambdaTerm)
                lambdaCase x e1 state = if var == x then return $ Lambda x e1
                                  else
                                    if S.member x fv (Lambda x (subInto e1)) then
                                      do --here is where we change out x for a new name and substitute this into e1
                                        newName <- getFresh
                                        let newE1 = (Lambda newName (sub e1 x newName)) in
                                          return $ subInto newE1
                                    else
                                      return $ return (Lambda x (subInto e1))
