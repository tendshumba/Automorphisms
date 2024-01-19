
/*

The example for L_3(2) 4B3A

*/
AttachSpec("DecompAlgs.spec");
AttachSpec("/home/tendai/AxialTools/AxialTools.spec");
Attach("AxialTools.m");
Attach("/home/tendai/Downloads/Automorphisms.m");

// Alter this to the path of where your algebra is stored
//path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

SetSeed(1);
/*Preliminary data.*/
A := LoadDecompositionAlgebra("Monster_1,4_1,32/RationalField()/4B3A_1.json");
F := BaseRing(A);
n := Dimension(A);
G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "PSL(2,7)";
/*The perumtation below is a permutation of the axes of A which preserves shape.*/
phi:=Sym(21)!(1, 7)(3, 10)(4, 11)(5, 15)(6, 8)(9, 16)(12, 17)(14, 21)(19, 20);
assert IsCoercible(G0,phi) eq false;/*hence this is an outer automorphism*/
axis_reps := AxisOrbitRepresentatives(A);
f:=MiyamotoActionMap(A);
G0_mat:=G0@f;
axes:=Axes(A);

//Computation 12.1 (a) We show that A has no Jordan axes.

assert #JordanAxes(A) eq 0;

//Computation 12.1 (b) We show all the axes are in one orbit, and that there are no twins
axes_reps:=AxisOrbitRepresentatives(A);
assert #axes_reps eq 1;
assert #(FindMultiples(axes_reps[1])) eq 1;

// Computation 12.1 (c)
Vaxes:=sub<VectorSpace(Algebra(A))|[Vector(x):x in axes]>;
psi:=hom<Vaxes->VectorSpace(A)|[<Vector(axes[i]), Vector(axes[i^phi])>:i in [1..21]]>;
bool,psi_map:=ExtendMapToAlgebraAutomorphism(A,psi);
assert bool;
assert IsAutomorphism(A,psi_map:generators:=axes);
psi_mat:=Matrix(F,[Eltseq(Vector(A.i)@psi_map):i in [1..49]]);

assert IsInducedFromAxis(A,psi_mat) eq false;
/*We've checked that indeed we have constructed an algebra automorphism not induced by an axis.*/
G:=PermutationGroup<21|G0,phi>;
assert GroupName(G) eq "SO(3,7)";
G_mat:=MatrixGroup<49,F|G0_mat,psi_mat>;
assert GroupName(G_mat) eq "SO(3,7)";
/*potentially remove if not used further. The above is proof enough.*/
bool,g_isom:=IsIsomorphic(G,G_mat);
assert bool;/* same as above.*/
/*we indeed have the correct manifestations of the group in both permutation and matrix form. Recall that SO(3,7) is isomorphic to PGL(2,7).*/

/*We now set up a decomposition with respect to a set of axes generating a 2A algebra and whose tau involutions generate an elementary abelian group 2^2.*/

a:=axes[1];
two_As:=[x:x in axes[[2..21]]| y*y eq y where y is -8*a*x+x+a];
assert #two_As gt 2;
b:=two_As[1];
c:=-8*a*b+a+b;
Y:={@a,b,c@};
assert Dimension(Subalgebra(A,Y)) eq 3;
E:=sub<G0_mat|[MiyamotoInvolution(x):x in Y]>;
assert GroupName(E) eq "C2^2";

// Computation 12.2 Details of the decomposition
YD:={@Decomposition(x): x in Y@};
decomp:=JointPartDecomposition(YD);
/*note here that the keys of the decomposition are indexed by the tuples <i,j,k> where
  1\le i,j,k\le 4 with 1:->1,0:->2, 1/4:->3 and 1/32:->4.*/

//Part (a) U_{(0,0,0)}(Y) is indexed by <2,2,2>;

U:=decomp[<2,2,2>];
assert Dimension(U) eq 10;

//Part (b) The rest of the componets are as follows:

// Part (b) (i) U_{(1/4,1/32,1/32)}(Y), U_{(1/32,1/4,1/32)}(Y) and U_{(1/32,1/32,1/4)(Y)
// by the map above, these will be indexed <3,4,4>, <4,3,4> and <4,4,3> respectively.

assert forall{x:x in [<3,4,4>, <4,3,4>, <4,4,3>] |Dimension(decomp[x]) eq 4};

/*Part (b) (ii) U_{(0,1/32,1/32)}(Y),U_{(1/32,0,1/32)}(Y) and U_{(1/32,1/32,0)(Y),
  which are indexed by <2,4,4>,<4,2,4> and <4,4,2>, respectively.*/

assert forall{x:x in  [<2,4,4>,<4,2,4>, <4,4,2>]|Dimension(decomp[x]) eq 6};

/* We turn to determining Aut(U). Note that N_{G0}(E) is ismorphic to S_4, and that clearly this induces S_3 on U, since E acts trivially on U, and N/E is a non-abelian group of order 6.*/

N:=Normaliser(G0_mat,E);
assert GroupName(N) eq "S4";
/*form the group of the automorphisms in N restricted to U.*/
N_bar:=MatrixGroup<Dimension(U),F|{Matrix([Coordinates(U,U.i*Matrix(y)) :i in [1..Dimension(U)]]):y in Generators(N)}>;
assert GroupName(N_bar) eq "S3";/*hence N induces S_3 on U.*/

UAlg,U_inc:=Subalgebra(A,Basis(U));

//Computation 12.4

// Part (a)
/*Note FixedSubalgebra takes DecAlg input. We want the fixed subalgebra of H in U, which is equivalent to the intersection of U with the fixed subalgebra of N in A.*/
FixA_N,F_inc:=FixedSubalgebra(A,N);
FF:=sub<VectorSpace(A)|[Vector(FixA_N.i@F_inc):i in [1..Dimension(FixA_N)]]> meet U;
assert Dimension(FF) eq 4;
/*idemps_F:=FindAllIdempotents(UAlg,sub<VectorSpace(UAlg)|[Vector(FF.i@@U_inc):i in [1..4]]>:extend_field:=true);*/
idemps_F:=FindAllIdempotents(A,FF:extend_field:=true);
assert #idemps_F eq 12;
/*These idempotents are over the algebraic closure, so we need to change field.*/

// Part (b)
thirty_four_fifths:=[A!Eltseq(x):x in idemps_F|Frobenius(x,x) eq 34/5];
assert #thirty_four_fifths eq 1;

//Part (c)
/*we want the idempotent of length 34/5 in U*/
AA:=Codomain(U_inc);
d:=thirty_four_fifths[1];
dd:=AA!Eltseq(d);
d_U:=UAlg!Eltseq(dd@@U_inc);
ad_d:=AdjointMatrix(d_U);
eigs_d:=Eigenvalues(ad_d);
assert eigs_d eq {<0,4>, <1,1>,<1/2,3>, <9/10,2>};
assert &+{x[2]:x in eigs_d} eq 10;

/* Part (d). "Almost" monster  (9/10,1/2) means that inverting the 1/2-eigenspace gives an automorphism.*/
evals,espaces, FL:=IdentifyFusionLaw(d_U: eigenvalues:={@1,0, 9/10,1/2@});
FL;
/*should be visibly graded.*/
inputs:=&cat [Basis(espaces[i]):i in [1..4]];
assert forall{i:i in [8,9,10]|x*ad_d eq 1/2*x where x is inputs[i]};
/* verify that the last three are the 1/2-eigenvectors*/
images:=inputs[[1..7]] cat [-inputs[i]:i in [8..10]];
/*could use hom but H is in matrix form, so I would rather use matrices.*/
t_d:=Matrix([Eltseq(images[i]):i in [1..10]]);
/*this is the matrix with respect to the basis "inputs' of eigenvectors. In the codomain, we are using the standard basis. We then change the basis of the domain to the standard one.*/
bas_change:=Matrix([Eltseq(inputs[i]):i in [1..10]]);
tt_d:=(bas_change^-1)*t_d;
assert IsAutomorphism(UAlg,tt_d);
HH:=MatrixGroup<10,F|N_bar,tt_d>;
assert IsIsomorphic(HH, Group("C2*S3"));/*so that tau d centralises H (N restricted to U, which is \hat(N)=N/E).*/

/* We note that the variety of idempotents of length 34/5 in U is 1-dim*/
R:=PolynomialRing(F,10);
FR:=FieldOfFractions(R);
AFR:=ChangeRing(A,FR);
u:=&+[R.i*(AFR!U.i):i in [1..10]];
I:=ideal<R|Eltseq(u*u-u),Frobenius(u,u)-34/5>;
assert Dimension(I) eq 1;

// Computation 12.5 
T:=espaces[2];
assert forall{i:i in [1..Dimension(espaces[2])]|T.i*ad_d eq 0};
idemps_T:=FindAllIdempotents(UAlg,T:extend_field:=true);
assert #idemps_T eq 16;
assert forall{x:x in idemps_T|x in UAlg};
assert #{x:x in idemps_T|Frobenius(y,y) eq 7/5 where y is A!(x@U_inc)} eq 3;
/* Thus there are three idempotents of length 7/5 in T. We show that these are all in U.*/

// Computation 12.6

/* Part (a) U has exactly three idempotents of length 7/5.*/
seven_fifths_U:=FindAllIdempotents(A,U:length:=7/5,extend_field:=true);
assert #seven_fifths_U eq 3;
seven_fifths_U_short:=[(AA!Eltseq(seven_fifths_U[i]))@@U_inc:i in [1..3]];
/* we need these for subsequent computations.*/

u_1:=seven_fifths_U_short[1];
u_2:=seven_fifths_U_short[2];
u_3:=seven_fifths_U_short[3];
// Part (b)
sub_7_5s,Seven_5Inc:= Subalgebra(UAlg, seven_fifths_U_short);
assert Dimension(sub_7_5s) eq 4;
 sub_7_5_space:=sub<VectorSpace(UAlg)|[Vector(sub_7_5s.i@Seven_5Inc):i in [1..4]]>;
assert T eq sub_7_5_space;
// Part (c)

ad_ui_s:=[AdjointMatrix(seven_fifths_U_short[i]):i in [1..3]];
assert forall{x:x in ad_ui_s|Eigenvalues(x) eq {<1,1>,<0,4>,<3/10,2>,<1/20,3>}};
/* Here the tuple <ev,mult> consists of an eigenvalue "ev", and its multiplicity, "mult".*/ 


// Part (d). We will show that for each u_i, inverting the 1/20-space gives rise to an automorphism
tau_uis:={@ @};
espaces_uis:=[[Eigenspace(ad_ui_s[i],evals_uis[j]) where evals_uis is [1,0,3/10,1/20]:j in [1..4]]:i in [1..3]];
for i:=1 to 3 do
       eigenspace_bas:=&cat [Basis(espaces_uis[i][j]):j in [1..4]];
       ims:=eigenspace_bas[[1..7]] cat [-eigenspace_bas[j]:j in [8..10]];/*invert the 1/20 space.*/
       t:=Matrix([Eltseq(ims[j]):j in [1..10]]);
       change_of_basis_mat:=Matrix([Eltseq(eigenspace_bas[j]):j in [1..10]]);
       t_u:=(change_of_basis_mat^-1)*t;
       tau_uis join:={@t_u@};
end for;
assert {*IsAutomorphism(UAlg,tau_uis[i]):i in [1..3]*} eq {*true^^3*};
/*alternatively, assert forall{t:t in tau_uis|IsAutomorphism(UAlg,t) eq true}*/

//  Part (e). The tau maps above generate an S_3.
H:=MatrixGroup<10,F|tau_uis>;
assert GroupName(H) eq "S3";
assert UAlg!(u_2*tau_uis[1]) eq u_3;/* we have the permutation (u_2,u_3).*/
assert UAlg!(u_1*tau_uis[2]) eq u_3;/*we have the permutation (u_1,u_3).*/
// Since (u_1,u_3) and (u_2,u_3) generate Sym({u_1,u_2,u_3}), action is transitive.

// Computation 12.7
TAlg,T_inc:=Subalgebra(UAlg,Basis(T));
id_T:=hom<TAlg->TAlg|[<TAlg.i,TAlg.i>:i in [1..4]]>;
U1_2_d:=espaces[4];
assert forall{i:i in [1..Dimension(U1_2_d)]|x*ad_d eq 1/2*x where x is  U1_2_d.i};
// Show that d=1_U-1_T

boolean,one_U:=HasOne(UAlg);
assert boolean;
boolean,one_T:=HasOne(TAlg);
assert boolean;
one_TU:=UAlg!Eltseq(one_T@T_inc);/*take the identity of T to U.*/
assert forall{x:x in Basis(T)|one_TU*(UAlg!x) eq UAlg!x};
assert d_U eq one_U-one_TU;
// Part (a)

bool,ext:=HasInducedMap(UAlg,U1_2_d,id_T);
assert bool;
assert Dimension(ext) eq 1;
ext_mat:=Matrix(F,m,m,Eltseq(ext.1)) where m is Dimension(U1_2_d);
assert IsIdentity(ext_mat);

// Part (b)
bas_U1_2d:=Basis(U1_2_d);
assert forall{x:x in bas_U1_2d|exists{y:y in Basis(T)|Frobenius(z*z,A!Eltseq(((UAlg!y)@U_inc))) ne 0where z is A!Eltseq(((UAlg!x)@U_inc))}};/*z*z having a non-zero projection to U_0(d) is equivalent to (z*z,z') being nonzero for some z' in U_0(d).*/

// Part (c)

assert Subalgebra(UAlg, bas_U1_2d) eq UAlg;


// Computation 12.9
Ws:=[decomp[<2,4,4>], decomp[<4,2,4>], decomp[<4,4,2>]];
assert forall{x:x in Ws|Dimension(x) eq 6};
id_U:=hom<UAlg->UAlg|[<UAlg.i,UAlg.i>:i in [1..Dimension(U)]]>;

// Part (a)
extensions:={@ @};
for i:=1 to 3 do
	 bool,exten:=HasInducedMap(A, Ws[i],id_U);
         assert bool;
         extensions join:={@exten @};
end for;
assert #extensions eq 1;/*so that all the extensions are equal.*/
assert Dimension(extensions[1]) eq 1;
assert IsIdentity(Matrix(F,6,6,Eltseq(extensions[1].1)));

// Part (b)
w_1:=A!Ws[1].(Random({1..6}));
w_2:=A!Ws[2].(Random({1..6}));
w_3:=A!Ws[3].(Random({1..6}));
u:=A!U.(Random({1..Dimension(U)}));
// Part (b) (i)
assert forall{v:v in [w_1,w_2,w_3]|Frobenius(v*v,u) ne 0};

// Part (b) (ii)
assert Frobenius(w_1*w_2,w_3) ne 0;

//Part (c)
assert Subalgebra(A,&cat[ Basis(W):W in Ws]) eq Algebra(A);

//Part (d)
/*It suffices to check on generators. Thus, take the central element and two involutions.*/
gensHH:=Generators(HH);
assert forall{g:g in gensHH|exists{W:W in Ws|boolean eq false where boolean is HasInducedMap(A,W,hom<UAlg->UAlg|[<UAlg.i,UAlg.i*g>:i in [1..10]]>)}};




