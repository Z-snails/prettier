module Text.PrettyPrint.Bernardy.Interface

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

||| Utility for pretty printing Idris data types.
|||
||| ```idris example
||| prettyCon "Just" [prettyArg v]
||| ```
public export
prettyCon : {opts : _} -> Prec -> String -> List (Doc opts) -> Doc opts
prettyCon p s [] = line s
prettyCon p s ds = parenthesise (p >= App) (hangSep 2 (line s) (sep ds))

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
Pretty a => Pretty (SnocList a) where
  prettyPrec _ = snocList . map pretty . (<>> [])

public export
Pretty a => Pretty b => Pretty (a,b) where
  prettyPrec _ (x,y) = tuple [pretty x, pretty y]
