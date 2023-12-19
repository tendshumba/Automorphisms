/*

The example for A5 3A2B

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored
path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

// A5 3A2B example in the paper
A := LoadDecompositionAlgebra(path cat "A5/15/5A5A3A2B_1");
F := BaseRing(A);
n := Dimension(A);

// Computation 10.1 (a), (b)
assert IsEmpty(JordanAxes(A));
axis_reps := AxisOrbitRepresentatives(A);
assert #FindMultiples(axis_reps[1]) eq 1;
// ie there are no multiples for the axis given

axes := Axes(A);
Vaxes := sub<VectorSpace(A)|[Vector(a) : a in axes]>;
assert Dimension(Vaxes) eq #axes;

// define a map by switching the first two axes.
assert forall{i : i in [1..#axes] | Vaxes.i eq Vector(axes[i])};

pi := Eltseq(Sym(15)!(1, 3)(2, 14)(5, 9)(6, 15)(8, 11)(10, 13));
G0 := MiyamotoGroup(A);
G := sub<Sym(15) | G0, pi>;
assert IsIsomorphic(G, Sym(5));
// So pi is an involution outside of A5.

// Now find the automorphism psi corresponding to pi
phi := hom<Vaxes -> VectorSpace(A) | [Vaxes.i : i in pi]>;
so, psi := ExtendMapToAlgebraAutomorphism(A, phi);
assert so;

// Computation 10.1 (c)
// Check that psi is not induced from a (possible new) axis
psi_mat := Matrix([Vector(A.i)@psi : i in [1..n]]);
so := IsInducedFromAxis(A, psi_mat: automorphism_check:=false);
assert not so;

Miy_map := MiyamotoActionMap(A);
GMat := MatrixGroup<n, F | Image(Miy_map), psi_mat>;
G_map := hom<G->GMat | [<g, g@Miy_map> : g in Generators(G0)] cat [<G!pi,psi_mat>] >;


E := SylowSubgroup(G0, 2);
K := Centraliser(G, E);
N := Normaliser(G,E);
assert IsIsomorphic(N/E, Sym(3));

CG := CharacterGroup(A);
Y := {@ axes[i] : i in [1..#axes] | MiyamotoElement(A,i, CG.1) in E@};
YD := {@ Decomposition(a) : a in Y@};

joint := JointPartDecomposition(YD);

// Computation 10.2
// The 0 eigenspace is the 2nd element of the fusion law
U := joint[<2,2,2>];
assert Dimension(U) eq 7;
assert Dimension(joint[<2,3,3>]) eq 1;
assert Dimension(joint[<2,2,3>]) eq 2;
assert Dimension(joint[<3,4,4>]) eq 3;
assert Dimension(joint[<2,4,4>]) eq 6;

// Computation 10.3 (a)
idems2 := FindAllIdempotents(A, U:length:=2);
assert #idems2 eq 3;
Ualg, inc := Subalgebra(A, Basis(U));
Aalg := Algebra(A);

Ualg_idems2 := {@ Ualg!Aalg!Vector(v) : v in idems2 @};

// Computation 10.3 (b)
assert forall{v : v in Ualg_idems2 | HasMonsterFusionLaw(v:fusion_values:={@4/11,1/11@})};


// Computation 10.3 (c)
V, inc := Subalgebra(A, idems2);
assert Dimension(V) eq 3;
// Should do something to show this is a 3C

Ualg_Miy := {@ MiyamotoInvolution(v) : v in Ualg_idems2 @};
H := MatrixGroup<Dimension(U), F | Ualg_Miy>;
assert IsIsomorphic(H, Sym(3));

// Computation 10.4 (a)
so, U_id := HasOne(Ualg);
assert so;
AU_id := A!Aalg!U_id;
assert Frobenius(AU_id, AU_id) eq 11;

// Computation 10.4 (b)
so, V_id := HasOne(V);
assert so;
AV_id := A!Aalg!V_id;
assert Frobenius(AV_id, AV_id) eq 11/2;

// Computation 10.4 (c)
idems_11_2 := FindAllIdempotents(A, U:length:=11/2);
assert #idems_11_2 eq 8;
assert AU_id - AV_id in idems_11_2;

// Computation 10.4 (d)
values := {@ [ Frobenius(idems_11_2[i], a) : a in idems2 ] : i in [1..8] @};
assert #values eq 8;
// so they are unique determined by their inner products with idems2;

// Computation 10.4 (e)
assert Dimension(Subalgebra(A, idems_11_2)) eq 7;

W1 := joint[<3,4,4>];
W2 := joint[<4,3,4>];
W3 := joint[<4,4,3>];
Ws := [W1, W2, W3];

// Computation 10.5 (n)
assert Dimension(Subalgebra(A, [ VectorSpace(A)!v : v in Basis(W), W in Ws])) eq n;

id_U := hom< Ualg-> Ualg | [ Ualg.i : i in [1..Dimension(Ualg)]]>;

// Computation 10.5 (b)
// Similar for the other Wi
so, W1_ext := HasInducedMap(A, W1, id_U);
assert so;
assert Dimension(W1_ext) eq 1;

// Computation 10.5 (c)
assert forall{ <w,u> : w in Basis(W1), u in Basis(Ualg) | Frobenius((A!w)*(A!w), A!u) ne 0};
assert forall{ <w1,w2,w3> : w1 in Basis(W1), w2 in Basis(W2), w3 in Basis(W3) | Frobenius((A!w1)*(A!w2), A!w3) ne 0};

assert IsIsomorphic(N, Sym(4));

// Computation 10.7 (a)
assert exists{ n : n in N | Y[1]*(n@G_map) eq Y[2]};
assert exists{ n : n in N | Y[1]*(n@G_map) eq Y[3]};
Nstab := sub<N|[ n : n in N | Y[1]*(n@G_map) eq Y[1]]>;
assert exists{ n : n in Nstab | Y[2]*(n@G_map) eq Y[3]};
// So N must act as S3 on the 3 elements of Y and hence induces H on U.

// Computation 10.7 (b)
assert exists(h){h : h in H | Order(h) eq 2};
phi := hom<Ualg -> Ualg | Matrix(h)>;
assert {* HasInducedMap(A, Wi, phi) : Wi in Ws*} eq {* true^^1, false^^2*};

// Computation 10.7 (c)
assert exists(h){h : h in H | Order(h) eq 3};
phi := hom<Ualg -> Ualg | Matrix(h)>;
assert forall{ Wi : Wi in Ws | not HasInducedMap(A, Wi, phi)};




