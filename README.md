# Automorphisms

This is magma code for finding automorphism groups of axial algebras.  It implements the algorithms described in the following paper and also includes the computatons for the examples in the paper

[I. Gorshkov, J. McInroy, T. Mudziiri Shumba and S. Shpectorov, Automorphisms of axial algebras, _J. Algebra_, to appear, _arXiv_:2311.18538, 49 pages.](https://arxiv.org/abs/2311.18538))

Note that the code is built on top of the [DecompAlgs](https://github.com/SimonMaths/DecompAlgs) package for decomposition and axial algebras by J. McInroy and S.F. Peacock.  So this package is required.

## Getting started
<details>
  <summary>To clone the DecompAlgs package</summary>
  
  ```
  git clone --recurse-submodules https://github.com/SimonMaths/DecompAlgs
  ```
  or
  ```
  git clone --recurse-submodules git@github.com:SimonMaths/DecompAlgs.git
  ```
  This should also pull the submodules which are required here (FusionLaws which includes MagmaJson - this requires python v2.7 or above to load and save algebras.)
</details>

<details>
  <summary>Runing the example files</summary>

  For this, the [AxialTools](https://github.com/JustMaths/AxialTools) package is also needed
  ```
  git clone --recurse-submodules https://github.com/JustMaths/AxialTools
  ```
  or 
   ```
  git clone --recurse-submodules git@github.com:JustMaths/AxialTools.git
  ```
</details>

### Cloning this repository
```
git clone https://github.com/tendshumba/Automorphisms
```
or
```
git clone git@github.com:tendshumba/Automorphisms.git
```

Now, when you are in the Automorphisms directory start magma and attach the spec file and code file in order
```
AttachSpec("../DecompAlgs/DecompAlgs.spec");
Attach("Automorphisms.m");
```

## Code functions
Given an axial algebra `A`, we can find all axes
```
FindAllAxes(A);
```
if the dimension of the algebra is small enough.  If not, then we can search for idempotents in a given subspace `U` by using `FindAllIdempotents(A, U)`.

Given an axis `a`, we can find its twins
```
FindMultiples(a);
```
We can also find the Jordan axes in `A`, using
```
JordanAxes(A);
```
Given an indexed set `L` of decompositions of the algebra, we can find the joint part decomposition
```
JointPartDecomposition(L);
```
If we have found an idempotent `u`, then we can check if it satisfies a fusion law
```
HasMonsterFusionLaw(u);
HasJordanFusionLaw(u);
```
Suppose we have a map `phi` defined on a subspace of the algebra.  We can try to extend this to an automorphism of the algebra
```
ExtendMapToAlgebraAutomorphism(A, phi);
```
If we have a map `phi` of the whole algebra, we can test whether it is an automorphism
```
IsAutomorphism(phi);
```
if it is, then we can ask if it is induced as the Miyamoto involution of an axis
```
IsInducedFromAxis(phi);
```
