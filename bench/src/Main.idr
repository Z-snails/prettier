module Main

import Text.PrettyPrint.Bernardy.Bench
import Profile

main : IO ()
main = runDefault (const True) Table absurd bench
