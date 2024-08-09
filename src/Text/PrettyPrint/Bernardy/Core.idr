module Text.PrettyPrint.Bernardy.Core

import Data.DPair
import Data.List
import Data.String

%default total

--------------------------------------------------------------------------------
--          NonEmpty SnocList
--------------------------------------------------------------------------------

public export
data NonEmptySnoc : SnocList a -> Type where
  IsNonEmptySnoc : NonEmptySnoc (sx :< x)

0 nonEmptyChips : {auto p : NonEmptySnoc sx} -> NonEmpty (sx <>> xs)
nonEmptyChips {sx = Lin :< _}        = %search
nonEmptyChips {sx = h@(_ :< _) :< _} = nonEmptyChips {sx = h}

%inline
kcap : SnocList Char -> String
kcap = pack . (<>> [])

allLines :
     (inp : List Char)
  -> (sc : SnocList Char)
  -> SnocList String
  -> SnocList String
allLines []                   sc sl = sl :< kcap sc
allLines ('\n' :: '\r' :: xs) sc sl = allLines xs Lin (sl :< kcap sc)
allLines ('\n' :: xs)         sc sl = allLines xs Lin (sl :< kcap sc)
allLines ('\r' :: xs)         sc sl = allLines xs Lin (sl :< kcap sc)
allLines (x :: xs)            sc sl = allLines xs (sc :< x) sl

--------------------------------------------------------------------------------
--          Stats
--------------------------------------------------------------------------------

public export
record LayoutOpts where
    [noHints]
    constructor Opts
    lineLength : Nat

record Stats where
    constructor MkStats
    maxLine  : Nat
    lastLine : Nat
    height   : Nat

-- stats for a string without line breaks
lstats : String -> Stats
lstats s = let n := length s in MkStats n n 0

-- updates the stats after appending a string without line break
addStats : String -> Stats -> Stats
addStats s (MkStats ml ll h) = MkStats (max ml $ length s) ll (S h)

-- Compare two stats in the presence of a maximal page width.
-- We consider a layout `x` to be superior than layout `y`
-- if
--   a) the two layouts do not overflow the page and
--      all stats of `x` are smaller or equal than the stats of `y`,
-- or
--   b) `y` overflows the page and the width of `x` is smaller than the
--      one of `y`
-- If neither a) nor b) hold for one the arguments, this function
-- returns `EQ`.
compStats : LayoutOpts -> Stats -> Stats -> Ordering
compStats (Opts ll) (MkStats mll lll hl) (MkStats mlr llr hr) =
  -- if one layout overflows, keep only the narrower
  if      mll < mlr && ll < mlr then LT
  else if mlr < mll && ll < mll then GT
  -- if one layout dominates the other, keep only the
  -- dominating one.
  else if mll <= mlr && lll <= llr && hl <= hr then LT
  else if mlr <= mll && llr <= lll && hr <= hl then GT
  else    EQ

--------------------------------------------------------------------------------
--          Layout
--------------------------------------------------------------------------------

export
record Layout where
    constructor MkLayout
    -- It is essential that we are lazy here: When deciding on the best
    -- layout, we only need the stats but not the actual list of lines.
    -- We need those only when rendering the preferred layout.
    --
    -- We use a `SnocList` because we often concatenate layouts
    -- by using left folds over lists of layouts. A `SnocList` is a
    -- natural and efficient accumulator in a left fold.
    content : Lazy (SnocList String)
    stats   : Stats
    {auto 0 prfNonEmptyContent : NonEmptySnoc content}

layout : Lazy (Subset (SnocList String) NonEmptySnoc) -> Stats -> Layout
layout ss st = MkLayout (fst ss) st @{snd ss}

namespace Layout

    ||| Returns the number of lines in a `Layout`.
    export %inline
    height : Layout -> Nat
    height = S . height . stats

    ||| Returns the number of lines in a `Layout`.
    export %inline
    isMultiline : Layout -> Bool
    isMultiline = (> 1) . height

    ||| Returns the width of the longest line in a `Layout`
    export %inline
    width : Layout -> Nat
    width = maxLine . stats

    export %inline
    isEmpty : Layout -> Bool
    isEmpty l = height l == 0 && width l == 0

    ||| The empty layout, consisting of a single empty line.
    export
    empty : Layout
    empty = MkLayout [<""] (MkStats 0 0 0)

    ||| Render the given layout
    export
    render : Layout -> String
    render (MkLayout sl _) = unlines (sl <>> [])

    ||| Convert a single line of text to a layout.
    |||
    ||| @ str this must be single line of text.
    export
    line : (str : String) -> Layout
    line s = MkLayout [<s] (lstats s)

    ||| Convert a string to a layout.
    ||| This preserves any manual formatting
    |||
    ||| @ str the String to pretty print
    export
    text : (str : String) -> Layout
    text str = case allLines (unpack str) Lin Lin of
      Lin          => empty
      ls@(sx :< x) => MkLayout ls (foldr addStats (lstats x) sx)

    indentOnto :
         (sx : SnocList String)
      -> (xs : List String)
      -> {auto 0 p1 : NonEmptySnoc sx}
      -> Nat
      -> Subset (SnocList String) NonEmptySnoc
    indentOnto sx []        _ = Element sx p1
    indentOnto sx (x :: xs) n = indentOnto (sx :< indent n x) xs n

    appendOnto :
         (sx : SnocList String)
      -> (xs : List String)
      -> {auto 0 p1 : NonEmptySnoc sx}
      -> {auto 0 p2 : NonEmpty xs}
      -> Nat
      -> Subset (SnocList String) NonEmptySnoc
    appendOnto (sx :< x) (y :: ys) n = indentOnto (sx :< (x ++ y)) ys n


    ||| Concatenate to Layouts horizontally
    export
    Semigroup Layout where
      MkLayout c s <+> MkLayout d t =
        let -- this is needed for the call to `appendOnto` below
            0 prf        := nonEmptyChips {xs = []} {sx = d}

            newStats     :=
              MkStats {
                maxLine  = max s.maxLine $ s.lastLine + t.maxLine
              , lastLine = s.lastLine + t.maxLine
              , height   = s.height + t.height
              }

         in layout (appendOnto c (d <>> []) s.lastLine) newStats

    export %inline
    Monoid Layout where
      neutral = empty

    export %inline
    FromString Layout where
      fromString = text

    export
    flush : Layout -> Layout
    flush (MkLayout sl $ MkStats ml _ h) =
      MkLayout (sl :< "") (MkStats ml 0 $ S h)

    export
    indent : Nat -> Layout -> Layout
    -- We make sure to not force the string of empty chars and make use
    -- of our knowledge about its stats.
    indent k x = MkLayout [< replicate k ' '] (MkStats k k 0) <+> x

    shortest : Layout -> List Layout -> Layout
    shortest x xs =
      foldl (\x,y => if x.stats.height <= y.stats.height then x else y) x xs

--------------------------------------------------------------------------------
--          Doc
--------------------------------------------------------------------------------

||| A non-empty selection of possible layouts.
export
record Doc (opts : LayoutOpts) where
    constructor MkDoc
    head : Layout
    tail : List Layout

export %inline
pure : Layout -> Doc opts
pure l = MkDoc l []

%inline
layouts : Doc opts -> List Layout
layouts (MkDoc h t) = h :: t

namespace Doc
    ||| Render the best candidate from the given set of layouts
    export
    render : (opts : _) -> Doc opts -> String
    render opts (MkDoc x xs) = render $ shortest x xs

    -- prepend layouts in a SnocList to a list of layouts.
    chips1 : SnocList Layout -> Layout -> List Layout -> Doc opts
    chips1 (sx :< y) x xs = chips1 sx y (x :: xs)
    chips1 [<]       x xs = MkDoc x xs

    insert :
         {opts : _}
      -> SnocList Layout
      -> List Layout
      -> Layout
      -> Doc opts
    insert sl []       x = chips1 sl x []
    insert sl (h :: t) x = case compStats opts x.stats h.stats of
      LT => insert sl t x
      EQ => insert (sl :< h) t x
      GT => chips1 sl h t

    combine : {opts : _} -> Doc opts -> List Layout -> Doc opts
    combine d (y :: ys) = combine (insert Lin (layouts d) y) ys
    combine d []        = d

    ||| Choose the better of two different documents.
    export %inline
    (<|>) : {opts : _} -> Doc opts -> Doc opts -> Doc opts
    x <|> y = combine x $ layouts y

    ||| Concatenate two documents horizontally.
    |||
    ||| The first line of the second document will be appended
    ||| to the last line of the first, and the remaining lines
    ||| of the second will be indented accordingly.
    |||
    ||| For instance, for documents `x` and `y` of the following
    ||| shapes
    |||
    ||| ```
    ||| xxxxxxxxxxx
    ||| xxxxxxxxxxxxxx
    ||| xxx
    ||| ```
    ||| and
    |||
    ||| ```
    ||| yyyyy
    ||| yy
    ||| yyyy
    ||| ```
    ||| the result will be aligned as follows:
    |||
    ||| ```
    ||| xxxxxxxxxxx
    ||| xxxxxxxxxxxxxx
    ||| xxxyyyyy
    |||    yy
    |||    yyyy
    ||| ```
    export
    (<+>) : {opts : _} -> Doc opts -> Doc opts -> Doc opts
    MkDoc x xs <+> MkDoc y ys =
      let appYs := \v => MkDoc (v <+> y) (map (v <+>) ys)
          ini   := appYs x
       in foldl (\acc,x => combine {opts} (appYs x) $ layouts acc) ini xs

    export %inline
    FromString (Doc opts) where
        fromString str = pure $ fromString str

    ||| The empty document, consisting of a single emtpy line.
    export %inline
    empty : Doc opts
    empty = pure neutral

    export
    (>>=) : {opts : _} -> Doc opts -> (Layout -> Doc opts) -> Doc opts
    (>>=) (MkDoc x xs) f = foldl (\d,l => d <|> f l) (f x) xs

    ||| Creates a single-line document from the given string.
    |||
    ||| @str A string without line breaks
    export %inline
    line : (str : String) -> Doc opts
    line = pure . line

    ||| Flushes the last line of the given document, so that an appended
    ||| document starts on a new line.
    export
    flush : {opts : _} -> Doc opts -> Doc opts
    flush (MkDoc x xs) = MkDoc (flush x) $ map flush xs

    ||| Indents the given document by a number of spaces.
    export
    indent : {opts : _} -> Nat -> Doc opts -> Doc opts
    indent k (MkDoc  x xs) = combine (pure $ indent k x) (indent k <$> xs)

    ||| Indents the given document by a number of spaces, if it's not empty.
    export
    indent' : {opts : _} -> Nat -> Doc opts -> Doc opts
    indent' k x = do
      l <- x
      pure $ if isEmpty l then l else indent k l

    ||| Displays a single string, preserving any manual formatting.
    export %inline
    text : String -> (Doc opts)
    text = pure . text
