{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module IRTS.CLaSH.NetlistTypes where

import Control.Applicative       ((<$>))
import Control.Monad.Trans.Error (ErrorT(..))
import Unbound.LocallyNameless   (name2String)

import CLaSH.Core.TyCon          (tyConName)
import CLaSH.Core.Type           (LitTy(..),Type(..),TypeView(..),tyView)
import CLaSH.Netlist.Types       (HWType(..))
import CLaSH.Netlist.Util        (coreTypeToHWType)

idrisTypeToHWType ::
  Type
  -> Maybe (Either String HWType)
idrisTypeToHWType (tyView -> TyConApp tc args) = runErrorT $
  case (name2String $ tyConName tc) of
    "__INT__"             -> return Integer
    "CLaSH.Signal.Signal" -> ErrorT $ return $ coreTypeToHWType idrisTypeToHWType (head args)
    "Prelude.Vect.Vect"   -> do
      let [szTy,elTy] = args
      sz     <- tyNatSize szTy
      elHWTy <- ErrorT $ return $ coreTypeToHWType idrisTypeToHWType elTy
      return $ Vector sz elHWTy
    _ -> ErrorT $ Nothing

idrisTypeToHWType _ = Nothing

tyNatSize ::
  Type
  -> ErrorT String Maybe Int
tyNatSize (LitTy (NumTy i)) = return i
tyNatSize t@(tyView -> TyConApp tc args) = case name2String (tyConName tc) of
  "Prelude.Nat.Z" -> return 0
  "Prelude.Nat.S" -> succ <$> tyNatSize (head args)
  "Builtins.fromInteger"                                         -> tyNatSize (last args)
  "@Builtins.Num$[Nat].0.Builtins.#!fromInteger"                 -> tyNatSize (last args)
  "@Builtins.Num$[Nat].0.Builtins.#!fromInteger.0.#fromInteger'" -> tyNatSize (last args)
  _ -> error $ "Can't convert tyNat: " ++ show t
tyNatSize t = error $ "Can't convert tyNat: " ++ show t
