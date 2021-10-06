# GAP-LEAN

A GAP parser, pretty printer, interpreter, and formal semantics. 

- Can parse `grp/basic.gd`
- Can parse `grp/basicprm.gi`. to handle permutation notation etc.
- `lib/stbc.gd` and `lib/stbc.gi` for stabilizer chains for Schrier tree.
- `lib/stbcrand.gi` : random construction of stabilizer chains.
- How best to parse `lib/stbc.gi` with things like `options.base` ?
- `scanner.c` and `read.c` are the main files here.
