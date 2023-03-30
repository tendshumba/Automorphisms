177,0
S,JointEigenspaceDecomposition,"Given an indexed set of axes L = { a_1, ..., a_n}, decompose the algebra into joint eigenspaces for these axes. Returns an associative array where the element A_lm_1(a_1) cap ... cap A_lm_n(a_n) has keys give by the set of eigenvalues { lm_1, ..., lm_n }",0,1,0,0,0,0,0,0,0,151,,457,-38,-38,-38,-38,-38
S,AdMat,"Given an axial algebra element a, find its ad_a matrix",0,1,0,0,0,0,0,0,0,ParAxlAlgElt,,177,-38,-38,-38,-38,-38
S,HasIdentityAlg,"Given an axial algebra A, determine if it has identity. Returns true if and only if it has one. 	If true, the identity is returned as a second element",0,1,0,0,0,0,0,0,0,ParAxlAlg,,36,ParAxlAlgElt,-38,-38,-38,-38
S,FindAllIdempotents,"Given an algebra A and a subspace (not necessarily a subalgebra) U, find all the idempotents of A contained in U. Optional arguments: length - requires the length of the idempotents to be as given form - the Frobenius form one- the identity of A. extra_rels - require the idempotent to satisfy extra relation(s). These are given by multivariate polynomials in dim(U) variables corresponding to the basis of U",0,2,0,0,0,0,0,0,0,159,,0,0,ParAxlAlg,,151,-38,-38,-38,-38,-38
S,FrobFormAtElements,"Given an axial algebra A with a form U, compute the number (u,v) for given elements u,v in A",0,3,0,0,0,0,0,0,0,177,,0,0,ParAxlAlgElt,,0,0,ParAxlAlgElt,,267,-38,-38,-38,-38,-38
S,LengthOfElement,"Given an element u of an axial algebra A which admits a Frobenius form ""form"", find the length of u wrt to the form, i.e., (u,u)",0,2,0,0,0,0,0,0,0,177,,0,0,ParAxlAlgElt,,267,-38,-38,-38,-38,-38
S,Pow,"Given an axial algebra element u and a non-negative integer n, find u^n=u*u*...*u n times. If the parent algebra of u has an identity, then u^0 is the identity",0,2,0,0,0,0,0,0,0,148,,0,0,ParAxlAlgElt,,ParAxlAlgElt,-38,-38,-38,-38,-38
S,AdPowerAtElement,"Function to evaluate ad_a^n(v), i.e., the nth power of ad_a evaluated at v",0,3,0,0,0,0,0,0,0,ParAxlAlgElt,,0,0,148,,0,0,ParAxlAlgElt,,ParAxlAlgElt,-38,-38,-38,-38,-38
S,PolynomialAtAdAtElement,Function to evaluate a polynomial f at ad_a and then applied to an alegbra element v,0,3,0,0,0,0,0,0,0,ParAxlAlgElt,,0,0,ParAxlAlgElt,,0,0,63,,ParAxlAlgElt,-38,-38,-38,-38,-38
S,HasMonsterFusion,"Check if the axial algebra element u satisfies the Monster M(1/4,1/32) fusion law",0,1,0,0,0,0,0,0,0,ParAxlAlgElt,,36,-38,-38,-38,-38,-38
S,IsJordanAxis,Check if a given idempotent is an axis of Jordan type 1/4,0,1,0,0,0,0,0,0,0,ParAxlAlgElt,,36,-38,-38,-38,-38,-38
S,TauMapMonster,Find the Tau map of an axis,0,1,0,0,0,0,0,0,0,ParAxlAlgElt,,177,-38,-38,-38,-38,-38
S,ProjMat,"Given an axis a and an eigenvalue ev of ad_a, find the projection matrix to A_{ev}(a)",0,2,0,0,0,0,0,0,0,267,,0,0,ParAxlAlgElt,,177,-38,-38,-38,-38,-38
S,SigmaMapMonster,"Given an axis a which is known to be J(1/4), find the sigma map which negates the 1/4-space",0,1,0,0,0,0,0,0,0,ParAxlAlgElt,,177,-38,-38,-38,-38,-38
S,FindAllAxesNuanced,"We perform the nuanced algorithm for finding all axes in an axial algebra of modest dimension. (Works for up to ~40 on an old laptop running linux.) This version only takes an axial algebra as input and attempts to find all axes in A. Additional (optional) inputs are : -one, the algebra identity if it exists. The program will attempt to find this if the default is left as is, increasing run time, -form, the Frobenius form of A. Same as above",0,1,0,0,0,0,0,0,0,ParAxlAlg,,151,-38,-38,-38,-38,-38
S,Axes,"Given an axial algebra A (partial or complete), return the list of orbits of axes that generate A",0,1,0,0,0,0,0,0,0,ParAxlAlg,,151,-38,-38,-38,-38,-38
S,AdMatInSubAlg,Suppose that V is a subalgebra of an axial algebra A of known multiplication. Determine the ad_a matrix of a in V,0,3,0,0,0,0,0,0,0,ParAxlAlgElt,,0,0,159,,0,0,ParAxlAlg,,177,-38,-38,-38,-38,-38
S,AnnihilatorOfSpace,"Given an algebra A and a subspace U of A, return the subspace (not a subalgebra) of A which annihilates U",0,2,0,0,0,0,0,0,0,159,,0,0,ParAxlAlg,,159,-38,-38,-38,-38,-38
S,FindMultiples,"Given an axis, find the set of all other axes which have the same Miyamoto automorphism as a. Does the same for a sigma automorphism if Jordan 1/4. We have optional arguments: 1. one, the algebra identity/unit. 2. 1/32-eigenspace (repsectively 1/4-eigenspace if Jordan), 3. form, the Frobenius form of the parent algebra",0,1,0,0,0,0,0,0,0,ParAxlAlgElt,,151,-38,-38,-38,-38,-38
S,VecToMat,Turn a vector to a row matrix,0,1,0,0,0,0,0,0,0,160,,177,-38,-38,-38,-38,-38
S,VecToMat,Turn a vector to a row matrix,0,1,0,0,0,0,0,0,0,ParAxlAlgElt,,177,-38,-38,-38,-38,-38
S,ExtendMapToAlgebra,"Given two indexed sets of axial algebra elements, the first with preimages and the second containing the corresponding images, 	extend the map as far as possible. If the map extends to the whole algebra, return true and a matrix that gives a multiplicative map A->A 	where A is the axial algebra in question. If not, return false and the maximum subalgebra (as a vector space) to which the map extends",0,2,0,0,0,0,0,0,0,82,,0,0,82,,36,177,-38,-38,-38,-38
