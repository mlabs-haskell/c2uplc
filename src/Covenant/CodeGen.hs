module Covenant.CodeGen (
    oneArgFuncToPlutus,
)
where

import Covenant.Prim (OneArgFunc)
import PlutusCore.Default.Builtins ()

oneArgFuncToPlutus :: OneArgFunc -> DefaultFun
oneArgFuncToPlutus = _
