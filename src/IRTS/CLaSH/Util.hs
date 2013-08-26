{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module IRTS.CLaSH.Util where

import           Unbound.LocallyNameless      (Rep,makeName,string2Name)
import qualified Unbound.LocallyNameless.Name as U
import           Unbound.LocallyNameless.Ops  (unsafeUnbind)

import qualified CLaSH.Core.Type              as C

import Core.TT
import Core.Evaluate

isCon :: Def -> Bool
isCon (TyDecl _ _) = True
isCon _ = False

defToTyDataCon :: (Name,Def)
               -> (Name,NameType,Type)
defToTyDataCon (n,TyDecl nt ty) = (n,nt,ty)
defToTyDataCon nd = error $ "Not a TyDec" ++ show nd

isTyConDef :: (Name,NameType,Type)
           -> Bool
isTyConDef (_,TCon _ _,_) = True
isTyConDef _              = False

isDConDef :: (Name,NameType,Type)
          -> Bool
isDConDef (_,DCon _ _,_) = True
isDConDef _              = False

toCoreName :: Rep a => Name -> U.Name a
toCoreName (UN s)   = string2Name s
toCoreName (NS n s) = prefixName (showSep "." (reverse s) ++ ".") (toCoreName n)
toCoreName (MN i s) = makeName s (toInteger i)
toCoreName NErased  = string2Name "___ERASED___"

prefixName :: String -> U.Name a -> U.Name a
prefixName p (U.Nm r (s,i)) = U.Nm r (p++s,i)
prefixName _ n              = n

replaceNameIndex :: Integer -> U.Name a -> U.Name a
replaceNameIndex i (U.Nm r (s,_)) = U.Nm r (s,i)
replaceNameIndex _ n              = n

splitFunTy :: C.Type -> ([C.Type],C.Type)
splitFunTy = go []
  where
    go args (C.tyView -> C.FunTy arg res) = go (arg:args) res
    go args ty                            = (reverse args,ty)

splitForallTy :: C.Type -> ([C.TyVar],C.Type)
splitForallTy = go []
  where
    go args (C.ForAllTy b) = let (tv,ty) = unsafeUnbind b
                             in  go (tv:args) ty
    go args ty             = (reverse args,ty)

splitFunForallTy :: C.Type -> ([Either C.TyVar C.Type],C.Type)
splitFunForallTy = go []
  where
    go args (C.ForAllTy b) = let (tv,ty) = unsafeUnbind b
                             in  go (Left tv:args) ty
    go args (C.tyView -> C.FunTy arg res) = go (Right arg:args) res
    go args ty                            = (reverse args,ty)

collectArgs :: Term -> ([Term],Term)
collectArgs = go []
  where
    go args (App e1 e2) = go (e2:args) e1
    go args e           = (args,e)

collectBndrs :: Term -> ([Binder Term],Term)
collectBndrs = go []
 where
    go bndrs (Bind _ bndr tm) = go (bndr:bndrs) tm
    go bndrs e                = (reverse bndrs, e)

safeIndex :: [a] -> Int -> Maybe a
safeIndex []     _ = Nothing
safeIndex (x:_)  0 = Just x
safeIndex (_:xs) n = safeIndex xs (n-1)

