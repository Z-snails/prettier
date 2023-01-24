# prettier

A pretty printing library for Idris 2

# performance

Performance depends largely on how combinators are associated (see `./bench`) but if used correctly, this can be very fast.
`src/Example.idr` includes an example that prints a 6562 line s-expression, which on my PC, takes about 300ms.
