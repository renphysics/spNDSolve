# spNDSolve (Spectral NDSolve)
A Mathematica package for solving PDEs by the pseudospectral method (v0.1, Jie Ren)

Put the `spNDSolve.m` in the directory

```
SystemOpen@FileNameJoin[{$UserBaseDirectory, "Applications"}]
```

Load the package by

```
<< spNDSolve.m
```

The documentation is in the notebook `spNDSolve Manual.nb` (to be completed).

1. At the first (symbolic) stage, expressions are automatically generated in `HoldForm`. 
2. At the second (numerical) stage, `spNDSolve` will assemble these expressions and execute them by `ReleaseHold`.

The folder PDW contains a nontrivial example as the background solution in 1612.04385 and 1705.05390.
