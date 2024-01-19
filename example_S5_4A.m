/*

The example for S5 4A

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored
path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";


SetSeed(1);
A := LoadDecompositionAlgebra(path cat "S5/10+15/6A5A4A_1");
F := BaseRing(A);
n := Dimension(A);

G0 := MiyamotoGroup(A);

// The Miyamoto group is a permutation group on the axes
axes := Axes(A);
assert forall{ <i,g> : i in [1..#axes], g in Generators(G0) | axes[i]*g eq axes[Image(g,GSet(G0),i)]};

// Computation 10.19 (a)
jordan_axis := JordanAxes(A);
assert #jordan_axis eq 1;
d := jordan_axis[1];

evals, espaces, FL := IdentifyFusionLaw(d);
assert #FL eq 3; // Jordan type fusion law
S := espaces cat [sub<VectorSpace(A)|>];
Dd := AxialDecomposition(A, S, d);

// Computation 10.19 (b)
axis_reps := AxisOrbitRepresentatives(A);
f:=MiyamotoActionMap(A);
G0_mat:=G0@f;
fifteen_index:=[i:i in [1..#axis_reps]|#((Vector(axis_reps[i]))^G0_mat) eq 15][1];
ten_index:=[i:i in [1..#axis_reps]|i ne fifteen_index][1];
fifteen_orbit:=[A!x:x in Vector(axis_reps[fifteen_index])^G0_mat];
assert #fifteen_orbit eq 15;
mults := FindMultiples(axis_reps[ten_index]);
assert #mults eq 2;
assert #FindMultiples(axis_reps[fifteen_index]) eq 1;
// the orbit of length 10 has multiples and the orbit of length 15 does not.

assert exists(a){ m : m in mults | m ne axis_reps[ten_index]};
evals, espaces, FL := IdentifyFusionLaw(a: eigenvalues:={@1,0,1/4,1/32@});
assert #FL eq 4;
Da := AxialDecomposition(A, espaces, a);

AddDecompositions(~A, [Dd, Da]);
A := MiyamotoClosure(A);

G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "S5";

// Computation 10.19 (a) second part
// The sigma involution of the jordan axes switches the two orbits of twins and fixes the orbit of length 15.

sg := SigmaElement(A, 1);
assert mults[1]*sg eq mults[2];
assert axis_reps[fifteen_index]*sg eq axis_reps[fifteen_index];

// Computation 10.19 (c)
G:=MatrixGroup<61,F|G0_mat,sg>;
assert GroupName(G) eq "C2*S5";
invs_G:=[x:x in ConjugacyClasses(G)|x[1] eq  2];
assert #invs_G eq 5;
assert [x[2]:x in invs_G] eq [1, 10, 10, 15, 15];
fifteen_inds:=[i:i in [1..5]|invs_G[i][2] eq 15];
assert #fifteen_inds eq 2;
g:=MiyamotoInvolution(fifteen_orbit[1]);
outside_fifteen:=[invs_G[i][3]:i in fifteen_inds|g notin invs_G[i][3]^G];
assert #outside_fifteen eq 1;
assert IsInducedFromAxis(A,Matrix(outside_fifteen[1])) eq false;
/* This shows that the one class of involutions of class size 15 is not induced from axes.*/
// Computation 10.20 (a) & (b)
Dd := Decompositions(A)[1];
FL := FusionLaw(A);
one_space_d:=Part(Dd,FL!1);
zero_space_d:=Part(Dd,FL!2);
quarter_space_d:=Part(Dd,FL!3);
assert Dimension(one_space_d) eq 1;
assert Dimension(zero_space_d) eq 46;
assert Dimension(quarter_space_d) eq 14;
V_long:=zero_space_d;
fifteen_orbit:=[A!Eltseq(x):x in fifteen_orbit];
V, V_inc:=Subalgebra(A,fifteen_orbit);
assert Dimension(V) eq 46;
H0:=sub<G0_mat|[MiyamotoInvolution(x):x in fifteen_orbit]>;
assert GroupName(H0) eq "A5";
assert sub<VectorSpace(A)|[Vector(V.i@V_inc):i in [1..46]]> eq V_long;
/*It's obvious from the fusion law that A_0(d) is a 46-dim subalgebra. The above shows that this is the axial algebra on an axet of 15 axes for A_5.*/

//Computation 10.21 (a)
 id_V:=hom<V->V|[<V.i,V.i>:i in [1..46]]>;
/*W:=quarter_space_d in the paper.*/
W:=quarter_space_d;
boolean,phi_vec:=HasInducedMap(A,W,id_V);
assert boolean;
assert Dimension(phi_vec) eq 1;
assert IsIdentity(Matrix(F,m,m,Eltseq(phi_vec.1))) where m is Dimension(W);
/*Thus the identity map on V extends as a scalar to A_{1/4}(d).*/

// Computation 10.21 (b)
w:=A!(W.(Random({1..14})));
assert w*w ne A!0;




