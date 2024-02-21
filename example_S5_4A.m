/*

The example for S5 4A

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored
path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";


A := LoadDecompositionAlgebra(path cat "S5/10+15/6A5A4A_1");
F := BaseRing(A);
n := Dimension(A);

G0 := MiyamotoGroup(A);

// If the algebra is Miyamoto closed, then the Miyamoto group is a permutation group on the axes
axes := Axes(A);
assert forall{ <i,g> : i in [1..#axes], g in Generators(G0) | axes[i]*g eq axes[Image(g,GSet(G0),i)]};

// Computation 10.19 (a)
jordan_axis := JordanAxes(A);
assert #jordan_axis eq 1;
d := jordan_axis[1];

S := [Eigenspace(d,lm) : lm in [1,0,1/4]] cat [sub<VectorSpace(A)|>];
Dd := AxialDecomposition(A, S, d);

// Computation 10.19 (b)
axis_reps := AxisOrbitRepresentatives(A);
mults := FindMultiples(axis_reps[1]);
assert #mults eq 2;
assert #FindMultiples(axis_reps[2]) eq 1;
// the orbit of length 10 has multiples and the orbit of length 15 does not.

assert exists(a){ m : m in mults | m ne axis_reps[1]};
evals, espaces, FL := IdentifyFusionLaw(a: eigenvalues:={@1,0,1/4,1/32@});
assert #FL eq 4;
Da := AxialDecomposition(A, espaces, a);

AddDecompositions(~A, [Dd, Da]);
A := MiyamotoClosure(A);

G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "S5";

// Computation 10.19 (a) second part
// The sigma involution of the jordan axes switches the two orbits of twins and fixes the orbit of length 15.

sg_mat := SigmaElement(A, 1);
assert mults[1]*sg_mat eq mults[2];
assert axis_reps[2]*sg_mat eq axis_reps[2];

axes := Axes(A);
sg := Sym(36)![Position(axes, a*sg_mat) : a in axes];

// Computation 10.19 (c)
G := sub<Sym(36) | G0, sg>;
assert GroupName(G) eq "C2*S5";

f := MiyamotoActionMap(A);
G0_mat := G0@f;
G_mat := MatrixGroup<61, F | G0_mat, sg_mat>;
perm_to_mat := hom<G -> G_mat | [<g,g@f> : g in Generators(G0)] cat [<sg,sg_mat>]>;

invs_G := [x : x in ConjugacyClasses(G) | x[1] eq 2];
assert #invs_G eq 5;
assert [ x[2] : x in invs_G] eq [1, 10, 10, 15, 15];

// find the index in the new algebra
a15_index := Position(axes, A!Vector(axis_reps[2]));
g15 := MiyamotoElement(A, a15_index);

exists(outside15){ x[3] : x in invs_G | x[2] eq 15 and g15 notin Class(G, x[3])};
assert not IsInducedFromAxis(A, Matrix(outside15@perm_to_mat));

a10_index := Position(axes, A!Vector(axis_reps[1]));
g10 := MiyamotoElement(A, a10_index);

exists(outside10){ x[3] : x in invs_G | x[2] eq 10 and g10 notin Class(G, x[3])};
assert not IsInducedFromAxis(A, Matrix(outside10@perm_to_mat));

// So there are axes corresponding to one conjugacy class of length 10, but not the other
// and one conjugacy class of length 15, but not the other

// Computation 10.20 (a) & (b)
Dd := Decompositions(A)[1];
FL := FusionLaw(A);
one_space_d := Part(Dd, FL!1);
zero_space_d := Part(Dd, FL!2);
quarter_space_d := Part(Dd, FL!3);

assert Dimension(one_space_d) eq 1;
assert Dimension(zero_space_d) eq 46;
assert Dimension(quarter_space_d) eq 14;

U := zero_space_d;
o15 := axes[Setseq(Orbit(G0, a15_index))];
assert forall{ a : a in o15 | Vector(a) in U};
Ualg := Subalgebra(A, o15);
assert Dimension(Ualg) eq 46;

// All the axes in the orbit of length 15 lie in U, which has dimension 46 and then generate U
// So, U = A_0(d) is the 46-dim algebra for A5 on 15 axes of shape 3A2B

// Computation 10.21 (a)
id_U := IdentityHomomorphism(Ualg);
W := quarter_space_d;
so, ext := HasInducedMap(A, W, id_U);
assert so;
assert Dimension(ext) eq 1;
assert IsIdentity(ext.1);

// Computation 10.21 (b)
// We check for all the basis vectors
assert forall{ w : w in Basis(W) | A!w*A!w ne A!0};
