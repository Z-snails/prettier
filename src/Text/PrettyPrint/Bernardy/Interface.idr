module Text.PrettyPrint.Bernardy.Interface

import Data.List1
import Data.Vect
import Data.SortedMap
import Data.SortedSet
import Text.PrettyPrint.Bernardy.Combinators
import Text.PrettyPrint.Bernardy.Core

%default total

public export
interface Pretty a where
    constructor MkPretty
    prettyPrec : {opts : _} -> Prec -> a -> Doc opts

||| Alias for `prettyPrec Open`
public export %inline
pretty : Pretty a => {opts : _} -> a -> Doc opts
pretty = prettyPrec Open

||| Alias for `prettyPrec App`
public export %inline
prettyArg : Pretty a => {opts : _} -> a -> Doc opts
prettyArg = prettyPrec App

onLineAfter : {opts : _} -> Doc opts -> Doc opts -> Doc opts
onLineAfter l d = vappend d (indent 2 l)

-- multilineCon :
--      {opts : _}
--   -> (con, firstArg : Doc opts)
--   -> (args : List (Doc opts))
--   -> Doc opts
-- multilineCon con fa as = foldl vcat fa as `onLineAfter` con

||| Utility for pretty printing Idris data types.
|||
||| Constructor name and arguments are layed out on a single line
||| if and only if they fit the page width
||| and all pretty printed arguments use only a single line. If
||| one of these conditions does not hold, the list of arguments is
||| indented by two spaces and layed out vertically after the constructor
||| name.
|||
||| ```idris example
||| prettyCon "Just" [prettyArg v]
||| ```
export
prettyCon : {opts : _} -> Prec -> String -> List (Doc opts) -> Doc opts
prettyCon p c []   = line c
prettyCon p c args =
  let con := line c
   in parenthesise (p >= App) $
        ifMultiline (hsep $ con :: args) (vsep args `onLineAfter` con)


||| Utility for pretty printing Idris record fields.
|||
||| Field name and value are separated by an equals sign (`=`) and
||| layed out on a single line if and only if they fit the page width
||| and the pretty printed values is itself on a single line. If
||| one of these conditions does not hold, the value is placed on
||| the next line and indented by two spaces.
export
prettyField : Pretty a => {opts : _} -> String -> a -> Doc opts
prettyField s v =
  let name := line s <++> equals
      val  := pretty v
   in ifMultiline (name <++> val) (val `onLineAfter` name)

||| Utility for pretty printing Idris data types with named arguments.
|||
||| This uses record syntax for printing the argument list, but is not
||| limited to single-constructor data types.
|||
||| Constructor name and arguments are layed out on a single line
||| if and only if they fit the page width
||| and all pretty printed arguments use only a single line. If
||| one of these conditions does not hold, the list of arguments is
||| indented by two spaces and layed out vertically after the constructor
||| name.
|||
||| ```idris example
||| prettyCon "Just" [prettyArg v]
||| ```
|||
||| Note: Use `prettyField` to pair an argument with its field name.
export
prettyRecord : {opts : _} -> Prec -> String -> List (Doc opts) -> Doc opts
prettyRecord p c []   = line c
prettyRecord p c args =
  let con  := line c
      flds := fields args
   in parenthesise (p >= App) $
        ifMultiline (con <++> flds) (flds `onLineAfter` con)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export %inline
Pretty Char where
  prettyPrec _ = line . show

public export %inline
Pretty String where
  prettyPrec _ = text . show

public export %inline
Pretty Bits8 where
  prettyPrec _ = line . show

public export %inline
Pretty Bits16 where
  prettyPrec _ = line . show

public export %inline
Pretty Bits32 where
  prettyPrec _ = line . show

public export %inline
Pretty Bits64 where
  prettyPrec _ = line . show

public export %inline
Pretty Int8 where
  prettyPrec _ = line . show

public export %inline
Pretty Int16 where
  prettyPrec _ = line . show

public export %inline
Pretty Int32 where
  prettyPrec _ = line . show

public export %inline
Pretty Int64 where
  prettyPrec _ = line . show

public export %inline
Pretty Integer where
  prettyPrec _ = line . show

public export %inline
Pretty Double where
  prettyPrec _ = line . show

public export %inline
Pretty () where
  prettyPrec _ () = line "()"

public export %inline
Pretty Bool where
  prettyPrec _ True  = "True"
  prettyPrec _ False = "False"

public export %inline
Pretty Ordering where
  prettyPrec _ LT = "LT"
  prettyPrec _ EQ = "EQ"
  prettyPrec _ GT = "GT"

public export %inline
Pretty Nat where
  prettyPrec _ = line . show

public export %inline
Pretty Int where
  prettyPrec _ = line . show

public export
Pretty a => Pretty (Maybe a) where
  prettyPrec p Nothing  = line "Nothing"
  prettyPrec p (Just x) = prettyCon p "Just" [prettyArg x]

public export
Pretty a => Pretty b => Pretty (Either a b) where
  prettyPrec p (Left x)  = prettyCon p "Left" [prettyArg x]
  prettyPrec p (Right x) = prettyCon p "Right" [prettyArg x]

public export %inline
Pretty a => Pretty (List a) where
  prettyPrec _ = list . map pretty

public export %inline
Pretty a => Pretty (List1 a) where
  prettyPrec p vs = prettyPrec p (toList vs)

public export %inline
Pretty a => Pretty (SnocList a) where
  prettyPrec _ = snocList . map pretty . (<>> [])

public export
Pretty a => Pretty b => Pretty (a,b) where
  prettyPrec _ (x,y) = tuple [pretty x, pretty y]

public export
Pretty a => Pretty (Vect n a) where
  prettyPrec p vs = prettyPrec p (toList vs)

public export
Pretty k => Pretty v => Pretty (SortedMap k v) where
  prettyPrec p m = prettyCon p "fromList" [prettyArg $ SortedMap.toList m]

public export
Pretty k => Pretty (SortedSet k) where
  prettyPrec p m = prettyCon p "fromList" [prettyArg $ Prelude.toList m]
