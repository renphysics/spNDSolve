# spNDSolve (Spectral NDSolve)
A Mathematica package for solving PDEs by the pseudospectral method (v0.1, Jie Ren)

Put the spNDSolve.m in the directory

Load the package by

1. Define the unkown functions and independ variables and equations to be solved

```
flist = {psi[z], phi[z]};

eqlist = {(-z + z^4 + phi[z]^2) psi[z] + (-1 + z^3) (3 z^2 psi'[z] + (-1 + z^3) psi''[z]), 
   2 phi[z] psi[z]^2 + (-1 + z^3) (phi^\[Prime]\[Prime])[
      z]}; (*Equations of motion*)
```

3. Calculate the Jacobian of equations

eqLinearize[{flist}, {eqlist, "eqlist", "mat"}];

4. Boundary conditions

brylist1 = {3 z^2 psi'[z] - 2 psi[z], phi[z]}; (*Boundary conditions at z=0*)

brylist2 = {psi'[z], phi[z] - mu}; (*Boundary conditions at z=1*)

5. Indeces of the boundaries

calcbryind := ({bryind1, bryind2} = bryIndex[{1, 2}]);

6. Calculate the Jacobian of boundary conditions and 

```
bryLinearize[{flist}, {{bryind1, brylist1}, {bryind2, brylist2}}]; (*Jacobian of boundary conditions*)
```

7. Initial guess (seed) of the unknown function for iteration

```
calcfref := (psi = one; phi = one);  (*Initial guess of the solution*)
```

8. Call the function spNDSolve

```
spNDSolve[z, linearMap[{0, 1}], 20, {mu, 2}]
```

The folder PDW includes a nontrivial example of this package.
