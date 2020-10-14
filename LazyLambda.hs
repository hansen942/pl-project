module LazyLambda
(
LambdaTerm,
FreshNames,
smallstep
) where

import Data.Stream as Stream

type VarName = Either String Integer

data LambdaTerm = Lambda VarName LambdaTerm | App LambdaTerm LambdaTerm | Var VarName | Int Integer

freshnames :: Stream.Stream VarName
freshnames = Streams.unfold (\x -> (Left (x+1), x+1)) (-1)

--sub e1 var e2 = Just e1[e2/var]
sub :: LambdaTerm -> LambdaTerm -> FreshNames -> Maybe LambdaTerm
sub e1 (Var name) e2 = undefined
sub _ _ _ = None



smallstep :: LambdaTerm -> LambdaTerm
smallstep _ = undefined
