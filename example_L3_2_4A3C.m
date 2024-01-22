
/*

The example for L_3(2) 4A3C

*/
AttachSpec("DecompAlgs.spec");
AttachSpec("/home/tendai/AxialTools/AxialTools.spec");
Attach("AxialTools.m");
Attach("/home/tendai/Downloads/Automorphisms.m");

// Alter this to the path of where your algebra is stored
//path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

SetSeed(1);
/*Preliminary data.*/
A := LoadDecompositionAlgebra("Monster_1,4_1,32/RationalField()/4A3C_1.json");
F := BaseRing(A);
n := Dimension(A);
G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "PSL(2,7)";
/*The perumtation below is a permutation of the axes of A which preserves shape.*/
phi :=Sym(21)!(1, 16, 10, 11)(2, 4, 12, 14, 20, 21, 8, 7)(3, 5, 18, 13, 15, 9, 6, 17);
assert IsCoercible(G0,phi) eq false;/*hence this is an outer automorphism*/
axis_reps := AxisOrbitRepresentatives(A);
f :=MiyamotoActionMap(A);
axes :=Axes(A);

//Computation 12.18 (a) We show that A has no Jordan axes.

assert #JordanAxes(A) eq 0;

//Computation 12.18 (b) We show all the axes are in one orbit, and that there are no twins
axes_reps :=AxisOrbitRepresentatives(A);
assert #axes_reps eq 1;
assert #(FindMultiples(axes_reps[1])) eq 1;

// Computation 12.18 (c)
Vaxes :=sub<VectorSpace(Algebra(A))|[Vector(x):x in axes]>;
psi :=hom<Vaxes->VectorSpace(A)|[<Vector(axes[i]), Vector(axes[i^phi])>:i in [1..21]]>;/*Fails incorrectly.*/
bool,psi_map :=ExtendMapToAlgebraAutomorphism(A,psi);
assert bool;
assert IsAutomorphism(A,psi_map:generators:=axes);

/*We've checked that indeed we have constructed an algebra automorphism not induced by an axis.*/
G :=PermutationGroup<21|G0,phi>;
assert GroupName(G) eq "SO(3,7)";
invs :=[x:x in ConjugacyClasses(G)|x[1] eq 2];
rep_28 :=[x[3]:x in invs|x[2] eq 28][1];/*representative of the class of involutions outside PSL(2,7) */
psi_28 :=hom<Vaxes->VectorSpace(A)|[<Vector(axes[i]), Vector(axes[i^rep_28])>:i in [1..21]]>;
bool,psi_28_map :=ExtendMapToAlgebraAutomorphism(A,psi_28);
assert IsInducedFromAxis(A,Matrix([Eltseq(Vector(A.i)@psi_28_map):i in [1..57]])) eq false; 
/*We've checked that indeed we have constructed an algebra automorphism not induced by an axis.*/

/*we indeed have the correct manifestations of the group in both permutation and matrix form. Recall that SO(3,7) is isomorphic to PGL(2,7).*/

/*We now set up a decomposition with respect to a set of axes generating a 2B algebras pairwise and whose tau involutions generate an elementary abelian group 2^2.*/

a :=axes[1];
two_Bs :=[x:x in axes[[2..21]]| x*a eq A!0 ];
assert #two_Bs gt 2;
b :=two_Bs[1];
c :=[x:x in two_Bs[[2..#two_Bs]]| a*x eq A!0 and b*x eq A!0][1];
Y :={@a,b,c@};
assert Dimension(Subalgebra(A,Y)) eq 3;
E :=sub<G0_mat|[MiyamotoInvolution(x):x in Y]>;
assert GroupName(E) eq "C2^2";
Miy_map :=MiyamotoActionMap(A);
E_perm :=sub<G0|[E.i@@Miy_map:i in [1..NumberOfGenerators(E)]]>;
assert IsIsomorphic(E, E_perm);
assert Centraliser(G, E_perm) eq E_perm;
N :=Normaliser(G, E_perm);
assert GroupName(N) eq "S4";

// Computation 12.19 Details of the decomposition. Here a_1=a, a_2=b and a_3=c.
YD :={@Decomposition(x): x in Y@};
decomp :=JointPartDecomposition(YD);
/*note here that the keys of the decomposition are indexed by the tuples <i,j,k> where
  1\le i,j,k\le 4 with 1:->1,0:->2, 1/4:->3 and 1/32:->4.*/

//Part (a) U_{(0,0,0)}(Y) is indexed by <2,2,2>;

U :=decomp[<2, 2, 2>];
assert Dimension(U) eq 9;

//Part (b) The rest of the componets are as follows:

// Part (b) (i) U_{(1,0,0)}(Y)=<a>, U_{(0,1,0)}(Y)=<b> and U_{(0,0,1)(Y)=<c>
// by the map above, these will be indexed <1,2,2>, <2,1,2> and <2,2,1> respectively.

assert forall{x:x in [<1, 2, 2>, <2, 1, 2>, <2, 2, 1>] |Dimension(decomp[x]) eq 1};

/* Part (b) (ii) U_{(0,1/4,1/4)}(Y), U{(1/4,0,1/4)}(Y) and U_{(1/4,1/4,0)}(Y). These are indexed by
   <2,3,3>, <3,2,3> and <3,3,2>, respectively.*/
assert forall{x:x in [<2, 3, 3>, <3, 2, 3>, <3, 3, 2>]|Dimension(decomp[x]) eq 1};

/* Part (b) (iii) U_{(1/4,0,0)}(Y), U{(0,1/4,0)}(Y) and U_{(0,0, 1/4)}(Y). These are indexed by
   <3,2,2>, <2,3,2> and <2,2,3>, respectively.*/
assert forall{x:x in [<3, 2, 2>, <2, 3, 2> ,<2, 2, 3>]|Dimension(decomp[x]) eq 2};

/*Part (b) (iv) U_{(1/4,1/32,1/32)}(Y),U_{(1/32,1/4,1/32)}(Y) and U_{(1/32,1/32,1/4)(Y),
  which are indexed by <3,4,4>,<4,3,4> and <4,4,3>, respectively.*/
assert forall{x:x in [<3, 4, 4>,<4, 3, 4>, <4, 4, 3>]|Dimension(decomp[x]) eq 2};

/*Part (b) (v) U_{(0,1/32,1/32)}(Y),U_{(1/32,0,1/32)}(Y) and U_{(1/32,1/32,0)(Y),
  which are indexed by <2,4,4>,<4,2,4> and <4,4,2>, respectively.*/

assert forall{x:x in  [<2, 4, 4>,<4, 2, 4>, <4, 4, 2>]|Dimension(decomp[x]) eq 10};

/* We turn to determining Aut(U). Note that N_{G}(E) is ismorphic to S_4, and that clearly this induces S_3 on U, since E acts trivially on U, and N/E is a non-abelian group of order 6.*/


UAlg, U_inc :=Subalgebra(A,Basis(U));

//Computation 12.20


/*Note FixedSubalgebra takes DecAlg input. We want the fixed subalgebra of H in U, which is equivalent to the intersection of U with the fixed subalgebra of N in A.*/
FixA_N, F_inc :=FixedSubalgebra(A,N);
FF :=sub<VectorSpace(A)|[Vector(FixA_N.i@F_inc):i in [1..Dimension(FixA_N)]]> meet U;
assert Dimension(FF) eq 3;
idemps_F :=FindAllIdempotents(A, FF:extend_field:=true);
assert #idemps_F eq 8;
assert {Frobenius(x,x):x in idemps_F} eq {0, 15, 135/16, 105/16, 75/8, 45/8, 360/37, 195/37};


// Computation 12.21
d :=[x:x in idemps_F|Frobenius(x,x) eq 45/8][1];
AA :=Algebra(A);
dd :=UAlg!(AA!Eltseq(d));

// Part (a)
forty_5_eights :=FindAllIdempotents(A, U: length:=45/8, extend_field:=true);
assert #forty_5_eights eq 4;
assert d in forty_5_eights;
u_s :=[x:x in forty_5_eights|x ne d];
u_sUAlg :=[UAlg!(AA!Eltseq(x)):x in u_s];
// Part (b)
assert Eigenvalues(AdjointMatrix(dd)) eq { <5/16, 3>, <1, 3>, <0, 1>, <3/32, 2> };
assert forall{x:x in u_sUAlg|Dimension(Eigenspace(AdjointMatrix(x), 1)) eq 2};

// Computation 12.22

assert Subalgebra(UAlg, u_sUAlg) eq UAlg;

// Computation 12.23 
Ws :=[decomp[x]:x in [ <3, 4, 4>, <4, 3, 4>, <4, 4, 3>]];

// Part (a) the Ws generate A.
assert Subalgebra(A, &cat[ Basis(W):W in Ws]) eq Algebra(A);

// Part (b)
id_U :=hom<UAlg->UAlg|[<UAlg.i, UAlg.i>:i in [1..Dimension(U)]]>;
extensions :={@ @};
for i:=1 to 3 do
	 bool,exten:=HasInducedMap(A, Ws[i],id_U);
         assert bool;
         extensions join:={@exten @};
end for;
assert #extensions eq 1;/*so that all the extensions are equal.*/
assert Dimension(extensions[1]) eq 1;
assert IsIdentity(Matrix(F, 2, 2,Eltseq(extensions[1].1)));

// Part (c)
w_1 :=A!Ws[1].(Random({1..2}));
w_2 :=A!Ws[2].(Random({1..2}));
w_3 :=A!Ws[3].(Random({1..2}));
u :=A!U.(Random({1..Dimension(U)}));
assert u ne A!0;
// Part (c) (i)
assert forall{v:v in [w_1,w_2,w_3]|Frobenius(v*v,u) ne 0};

// Part (c) (ii)
assert Frobenius((w_1*w_2)*(w_1*w_3), w_1) ne 0;

// Computation 12.26
I_57 :=IdentityMatrix(F, 57);
ad_ais :=[AdjointMatrix(x): x in Y];
/* We set up the projection to the joint 0-eigenspace/subalgebra U. Since the decomposition (joint) is complete, the joint projections to a space are simply the compositions of the projections of the respective axes a_i for the required eigenvalue combinations.*/
Proj_000_mat :=&*[&*[1/(0-lm)*(ad-lm*I_57):lm in [1, 0, 1/4, 1/32]|lm ne 0]:ad in ad_ais];
assert forall{i:i in [1..57] |Vector(A.i)*Proj_000_mat in U};

W1_prods :={(A!Ws[1].i)*(A!Ws[1].j):i in [1..2],j in [1..2]};
W2_prods :={(A!Ws[2].i)*(A!Ws[2].j):i in [1..2],j in [1..2]};
W3_prods :={(A!Ws[3].i)*(A!Ws[3].j):i in [1..2],j in [1..2]};

T1 :=sub<U|[Vector(x)*Proj_000_mat:x in W1_prods]>;
T2 :=sub<U|[Vector(x)*Proj_000_mat:x in W2_prods]>;
T3 :=sub<U|[Vector(x)*Proj_000_mat:x in W3_prods]>;
Ts:={@T1, T2, T3@};
assert forall{T:T in Ts|Dimension(T) eq 3};
assert forall{i:i in [1..2]|forall{j:j in [i+1..3] |Dimension(Ts[i] meet Ts[j]) eq 0}};


