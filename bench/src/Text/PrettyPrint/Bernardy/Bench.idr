module Text.PrettyPrint.Bernardy.Bench

import Text.PrettyPrint.Bernardy
import Profile
import Data.List
import Data.SnocList

printList : {opts : _} -> List String -> Doc opts
printList [] = empty
printList (x :: xs) = sep [line x, printList xs]

printSnoc : {opts : _} -> SnocList String -> Doc opts
printSnoc [<] = empty
printSnoc (xs :< x) = sep [printSnoc xs, line x]

data Tree a
    = Tip a
    | Bin (Tree a) (Tree a)

printTree : {opts : _} -> Tree String -> Doc opts
printTree (Tip x) = line x
printTree (Bin l r) = sep [printTree l, printTree r]

||| Generates a tree of depth k, ie length 2 ** k
makeTree : Nat -> a -> Tree a
makeTree Z x = Tip x
makeTree (S k) x =
    let t = makeTree k x
     in Bin t t

defaultOpts : LayoutOpts
defaultOpts = Opts 80

namespace SnocList
    public export
    replicate : Nat -> a -> SnocList a
    replicate Z x = [<]
    replicate (S k) x = replicate k x :< x

export
bench : Benchmark Void
bench = Group "sep"
    [ Group "1024"
        [ Single "list" (basic (render defaultOpts . printList) (replicate 1024 "foo"))
        , Single "snoc" (basic (render defaultOpts . printSnoc) (replicate 1024 "foo"))
        , Single "tree" (basic (render defaultOpts . printTree) (makeTree 10 "foo"))
        ]
    ]

{-
On my PC:
sep/1024/list                                        25.42 ms   25.45 ms 0.998
sep/1024/snoc                                        1.893  s   1.805  s 0.998
sep/1024/tree                                        9.212 ms   10.85 ms 1.045
-}
