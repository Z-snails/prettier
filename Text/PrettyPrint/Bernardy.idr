module Text.PrettyPrint.Bernardy

import Data.String
import Data.List
import Data.List1
import public Control.Monad.Reader
import public Control.Monad.Identity

%default total

public export
record LayoutOpts where
    constructor Opts
    lineLength : Int

export
record Layout where
    constructor MkLayout
    content : List1 String
    maxLine : Int
    lastLine : Int
    height : Int

namespace Layout
    ||| Render the given layout
    export
    render : Layout -> String
    render (MkLayout (l ::: ls) _ _ _) = unlines (l :: ls)

    ||| Convert a single line of text to a layout.
    |||
    ||| @ str this must be single line of text.
    export
    line : (str : String) -> Layout
    line str =
        let len = prim__strLength str
        in MkLayout
            { content = str ::: []
            , maxLine = len
            , lastLine = len
            , height = 0
            }

    allLines : (inp : List Char) -> (acc : List Char) -> List String
    allLines [] acc = [pack $ reverse acc]
    allLines ('\n' :: '\r' :: xs) acc = pack (reverse acc) :: allLines xs []
    allLines ('\n' :: xs) acc = pack (reverse acc) :: allLines xs []
    allLines ('\r' :: xs) acc = pack (reverse acc) :: allLines xs []
    allLines (x :: xs) acc = allLines xs (x :: acc)

    ||| Convert a string to a layout.
    ||| This preserves any manual formatting
    |||
    ||| @ str the String to pretty print
    export
    text : (str : String) -> Layout
    text str =
        let ls@(h :: t) = allLines (unpack str) []
            | [] => line ""
            (MkStats maxLine lastLine height) =
                foldl
                    (\(MkStats maxLine lastLine height), line =>
                        let len = prim__strLength line
                         in MkStats (max maxLine len) len (height + 1))
                    (MkStats 0 0 (-1))
                    ls
        in MkLayout
            { content = h ::: t
            , maxLine
            , lastLine
            , height
            }
    where
        data Stats : Type where
            MkStats : (maxLine, lastLine, height : Int) -> Stats

    concatContent' : String -> List String -> List1 String -> Nat -> List String
    concatContent' x [] (y ::: ys) k = (x ++ y) :: map (indent k) ys
    concatContent' x (x' :: xs) ys k = x :: concatContent' x' xs ys k

    concatContent : List1 String -> List1 String -> Nat -> List1 String
    concatContent (x ::: []) (y ::: ys) k = (x ++ y) ::: map (indent k) ys
    concatContent (x ::: (x' :: xs)) ys k = x ::: concatContent' x' xs ys k

    ||| Concatenate to Layouts horizontally
    export
    Semigroup Layout where
        left <+> right = MkLayout
            { content =
                concatContent
                    left.content
                    right.content
                    (cast left.lastLine)
            , maxLine = max left.maxLine $ left.lastLine + right.maxLine
            , lastLine = left.lastLine + right.lastLine
            , height = left.height + right.height
            }

    export
    Monoid Layout where
        neutral = MkLayout
            { content = "" ::: []
            , maxLine = 0
            , lastLine = 0
            , height = 0
            }

    export %inline
    FromString Layout where
        fromString = text

    export
    flush : Layout -> Layout
    flush x = MkLayout
        { content = addNL x.content.head x.content.tail
        , maxLine = x.maxLine
        , lastLine = 0
        , height = x.height + 1
        }
    where
        addNL : String -> List String -> List1 String
        addNL x [] = x ::: [""]
        addNL x (y :: xs) = x ::: forget (addNL y xs)

    export
    indent : Nat -> Layout -> Layout
    indent k x = fromString (replicate k ' ') <+> x

export
record Doc where
    constructor MkDoc
    layouts : List Layout

parameters (opts : LayoutOpts)
    visible : Layout -> Bool
    visible x = x.maxLine <= opts.lineLength

    shortest : List Layout -> Maybe Layout
    shortest [] = Nothing
    shortest (x :: xs) = Just $ foldl (\x, y => if x.height <= y.height then x else y) x xs

    ||| Render the best candidate from the given set of layouts
    export
    render : Doc -> Maybe String
    render (MkDoc xs) = map render $ shortest $ filter visible xs

namespace Doc
    insert : Layout -> List Layout -> List Layout -> List Layout
    insert x [] acc = x :: acc
    insert x (y :: ys) acc = case keep x y of
        KLeft => insert x ys acc
        KBoth => insert x ys (y :: acc)
        KRight => reverseOnto (y :: acc) ys
      where
        data Keep = KLeft | KBoth | KRight

        keep : Layout -> Layout -> Keep
        keep x y = case compare x.maxLine y.maxLine of
            LT => if x.lastLine <= y.lastLine
                    && x.height <= y.height
                    then KLeft
                    else KBoth
            EQ => KBoth
            GT => if x.lastLine >= y.lastLine
                    && x.height >= y.height
                    then KRight
                    else KBoth

    combine : List Layout -> List Layout -> List Layout
    combine [] ys = ys
    combine (x :: xs) ys = combine xs (insert x ys [])

    export %inline
    (<|>) : Doc -> Doc -> Doc
    MkDoc xs <|> MkDoc ys = MkDoc $ combine xs ys

    export %inline
    (<+>) : MonadReader LayoutOpts m => Doc -> Doc -> m Doc
    MkDoc xs <+> MkDoc ys = do
        opts <- ask
        pure $ MkDoc $ combine
            [ z
            | x <- xs
            , y <- ys
            , let z = x <+> y
            , visible opts z
            ]
            []

    export
    FromString Doc where
        fromString str = MkDoc [fromString str]

    export
    MonadReader LayoutOpts m => FromString (m Doc) where
        fromString str = pure $ fromString str

    export
    empty : Doc
    empty = MkDoc [neutral]

    export
    hcat : MonadReader LayoutOpts m => List Doc -> m Doc
    hcat xs = foldlM (<+>) empty xs

    export
    hsep : MonadReader LayoutOpts m => Doc -> Doc -> m Doc
    hsep x y = hcat [x, " ", y]

    export
    flush : Doc -> Doc
    flush (MkDoc xs) = MkDoc $ map flush xs

    export
    vcat : MonadReader LayoutOpts m => Doc -> Doc -> m Doc
    vcat x y = flush x <+> y

    export
    indent : MonadReader LayoutOpts m => Nat -> Doc -> m Doc
    indent k (MkDoc xs) = do
        opts <- ask
        pure $ MkDoc
            [ y
            | x <- xs
            , let y = indent k x
            , visible opts y
            ]

    export
    hang : MonadReader LayoutOpts m => Nat -> Doc -> Doc -> m Doc
    hang k x y = pure $ !(x <+> y) <|> !(vcat x !(indent k y))

    export
    text : String -> Doc
    text str = MkDoc [text str]

    export
    sep : MonadReader LayoutOpts m => List Doc -> m Doc
    sep [] = pure empty
    sep (x :: xs) = pure $ !(foldl1M hsep (x ::: xs)) <|> !(foldl1M vcat (x ::: xs))
      where
        foldl1M : Monad m => (elem -> elem -> m elem) -> List1 elem -> m elem
        foldl1M f (head ::: tail) = foldlM f head tail

public export
interface Pretty a where
    pretty : MonadReader LayoutOpts m => a -> m Doc

