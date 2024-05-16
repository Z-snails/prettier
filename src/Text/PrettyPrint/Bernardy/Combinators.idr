module Text.PrettyPrint.Bernardy.Combinators

import Data.String
import Text.PrettyPrint.Bernardy.Core

%default total

--------------------------------------------------------------------------------
--          Symbols
--------------------------------------------------------------------------------

||| Creates a single-line document from the given character.
|||
||| @c A printable non-control character.
export %inline
symbol : (c : Char) -> Doc opts
symbol = line . singleton

||| A single space character.
export
space : Doc opts
space = symbol ' '

export
squote : Doc opts
squote = symbol '\''

export
dquote : Doc opts
dquote = symbol '"'

export
lparen : Doc opts
lparen = symbol '('

export
rparen : Doc opts
rparen = symbol ')'

export
langle : Doc opts
langle = symbol '<'

export
rangle : Doc opts
rangle = symbol '>'

export
lbracket : Doc opts
lbracket = symbol '['

export
rbracket : Doc opts
rbracket = symbol ']'

export
lbrace : Doc opts
lbrace = symbol '{'

export
rbrace : Doc opts
rbrace = symbol '}'

export
semi : Doc opts
semi = symbol ';'

export
colon : Doc opts
colon = symbol ':'

export
comma : Doc opts
comma = symbol ','

export
dot : Doc opts
dot = symbol '.'

export
slash : Doc opts
slash = symbol '/'

export
backslash : Doc opts
backslash = symbol '\\'

export
equals : Doc opts
equals = symbol '='

export
pipe : Doc opts
pipe = symbol '|'

--------------------------------------------------------------------------------
--          Enclosing Documents
--------------------------------------------------------------------------------

||| Encloses the document between two other documents using `(<+>)`.
export
enclose : {opts : _} -> Doc opts -> Doc opts -> Doc opts -> Doc opts
enclose l r x = l <+> x <+> r

||| Encolses a document in single quotes.
export
squotes : {opts : _} -> Doc opts -> Doc opts
squotes = enclose squote squote

||| Encolses a document in double quotes.
export
dquotes : {opts : _} -> Doc opts -> Doc opts
dquotes = enclose dquote dquote

||| Encolses a document in parentheses.
export
parens : {opts : _} -> Doc opts -> Doc opts
parens = enclose lparen rparen

||| Encolses a document in parentheses if `b` equals `True`.
export
parenthesise : {opts : _} -> (b : Bool) -> Doc opts -> Doc opts
parenthesise b = if b then parens else id

||| Encolses a document in angles (`<` and `>`).
export
angles : {opts : _} -> Doc opts -> Doc opts
angles = enclose langle rangle

||| Encolses a document in curly braces.
export
braces : {opts : _} -> Doc opts -> Doc opts
braces = enclose lbrace rbrace

||| Encolses a document in brackets.
export
brackets : {opts : _} -> Doc opts -> Doc opts
brackets = enclose lbracket rbracket

--------------------------------------------------------------------------------
--          Combining Documents
--------------------------------------------------------------------------------

||| Tries to layout the first document on a single line, replacing
||| it with the alternative if a) it does not fit the page with or b)
||| it inherently is placed on several lines.
|||
||| This combinator is very useful for pretty printing Idris values
||| (data constructors, lists, records), because we typically try to
||| place them on a single line if and only if they fit the page width
||| and none of their arguments is placed on several lines.
export
ifMultiline : {opts : _} -> (doc, alt : Doc opts) -> Doc opts
ifMultiline doc alt = do
  l <- doc
  if isMultiline l then alt else pure l <|> alt

export infixl 8 <++>

||| Concatenates two documents horizontally with a single space between them.
export %inline
(<++>) : {opts : _} -> Doc opts -> Doc opts -> Doc opts
x <++> y = x <+> space <+> y

export infixl 8 <+?+>

||| Concatenates two documents horizontally with a space between them, if both
||| documents are not empty.
export %inline
(<+?+>) : {opts : _} -> Doc opts -> Doc opts -> Doc opts
x <+?+> y = do
  l <- x
  if isEmpty l then y else do
    r <- y
    if isEmpty r then pure l else
      pure l <+> space <+> pure r

export
vappend : {opts : _} -> Doc opts -> Doc opts -> Doc opts
vappend x y = flush x <+> y

||| Concatenate a sequence of documents horizontally using `(<+>)`.
export
hcat : {opts : _} -> List (Doc opts) -> Doc opts
hcat []       = empty
hcat (h :: t) = foldl (<+>) h t

||| Concatenate a sequence of documents horizontally using `(<++>)`.
export
hsep : {opts : _} -> List (Doc opts) -> Doc opts
hsep []       = empty
hsep (h :: t) = foldl (<++>) h t

||| Concatenate a list of documents vertically.
export
vsep : {opts : _} -> List (Doc opts) -> Doc opts
vsep []       = empty
vsep (h :: t) = foldl vappend h t

||| Tries to layout the two documents horizontally, but appends
||| the second indented by the given number of spaces below the
||| first if the horizontal version exceeds the width limit.
export
hang : {opts : _} -> Nat -> Doc opts -> Doc opts -> Doc opts
hang k x y = (x <+> y) <|> vappend x (indent k y)

||| Like `hang` but separates the two documents by a space in case of
||| a horizontal alignment.
export
hangSep : {opts : _} -> Nat -> Doc opts -> Doc opts -> Doc opts
hangSep k x y = (x <++> y) <|> vappend x (indent k y)

||| Tries to layout the two documents horizontally, but appends
||| the second indented by the given number of spaces below the
||| first if the horizontal version exceeds the width limit, or
||| if needs several lines.
export
hang' : {opts : _} -> Nat -> Doc opts -> Doc opts -> Doc opts
hang' k x y = ifMultiline (x <+> y) (vappend x $ indent k y)

||| Like `hang'` but separates the two documents by a space in case of
||| a horizontal alignment.
export
hangSep' : {opts : _} -> Nat -> Doc opts -> Doc opts -> Doc opts
hangSep' k x y = ifMultiline (x <++> y) (vappend x $ indent k y)

||| Tries to separate the given documents horizontally, but
||| concatenates them vertically if the horizontal layout exceeds the
||| width limit.
export
sep : {opts : _} -> List (Doc opts) -> Doc opts
sep xs = hsep xs <|> vsep xs

||| Tries to separate the given documents horizontally, but
||| concatenates them vertically if the horizontal layout exceeds the
||| width limit, or horizontal layout leads to a multiline document.
export
sep' : {opts : _} -> List (Doc opts) -> Doc opts
sep' xs = ifMultiline (hsep xs) (vsep xs)

||| Add the given document only when conditions is true
export
when : Bool -> Doc opts -> Doc opts
when True  = id
when False = const empty

--------------------------------------------------------------------------------
--          Lists of Documents
--------------------------------------------------------------------------------

||| Pretty prints a list of documents separated by the given delimiter
||| and wrapping them in opening and closing symbols.
|||
||| If it fits the page width, the document is layed out horizontally,
||| otherwise it's layed out vertically with  leading commas.
|||
||| Horizontal layout for `generalList "[" "]" "," [1,2,3]:
|||
||| ```
||| [1, 2, 3]
||| ```
|||
||| Vertical layout:
|||
||| ```
||| [ 1
||| , 2
||| , 3
||| ]
||| ```
export
generalList : {opts : _} -> (o,c,sep : Doc opts) -> List (Doc opts) -> Doc opts
generalList o c sep []        = o <+> c
generalList o c sep (x :: xs) =
  let xs' := map (sep <++>) xs ++ [c]
   in ifMultiline (hcat $ o :: x :: xs') (vsep $ (o <++> x) :: xs')

||| Pretty prints a list of documents separated by commas
||| and wrapping them in brackets.
|||
||| If it fits the page width, the document is layed out horizontally,
||| otherwise it's layed out vertically with leading delimiters.
|||
||| Horizontal layout:
|||
||| ```
||| [1, 2, 3]
||| ```
|||
||| Vertical layout:
|||
||| ```
||| [ 1
||| , 2
||| , 3
||| ]
||| ```
export %inline
list : {opts : _} -> List (Doc opts) -> Doc opts
list = generalList lbracket rbracket comma

||| Pretty prints a `SnocList` of documents separated by commas
||| and wrapping them in brackets.
|||
||| If it fits the page width, the document is layed out horizontally,
||| otherwise it's layed out vertically with  leading commas.
|||
||| Horizontal layout:
|||
||| ```
||| [<1, 2, 3]
||| ```
|||
||| Vertical layout:
|||
||| ```
||| [<1
||| , 2
||| , 3
||| ]
||| ```
export
snocList : {opts : _} -> List (Doc opts) -> Doc opts
snocList = generalList (line "[<") rbracket comma

||| Pretty prints a list of documents separated by commas
||| and wrapping them in parentheses.
|||
||| Horizontal layout:
|||
||| ```
||| (x, y, z)
||| ```
|||
||| Vertical layout:
|||
||| ```
||| ( x
||| , y
||| , z
||| )
||| ]
export
tuple : {opts : _} -> List (Doc opts) -> Doc opts
tuple = generalList lparen rparen comma

||| Pretty prints a list of documents separated by commas
||| and wrapping them in curly braces.
|||
||| Horizontal layout:
|||
||| ```
||| {x, y, z}
||| ```
|||
||| Vertical layout:
|||
||| ```
||| { x
||| , y
||| , z
||| }
||| ]
export
fields : {opts : _} -> List (Doc opts) -> Doc opts
fields = generalList lbrace rbrace comma
