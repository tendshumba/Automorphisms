/*

The example for A5 3A2B

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
// AttachSpec("../AxialTools/AxialTools.spec");
Attach("Automorphisms.m");

types := ["2A","2B","3A","3C","4A","4B","5A","6A"];
IdentityLength := AssociativeArray([* <"2A", (2^2*3)/5>,
                                      <"2B", 2>,
                                      <"3A", (2^2*29)/(5*7)>,
                                      <"3C", (2^5/11)>,
                                      <"4A", 4>,
                                      <"4B", 19/5>,
                                      <"5A", (2^5)/7>,
                                      <"6A", (3*17)/(2*5)> *]);
                                      
path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

// A5 3A2B example in the paper
A := LoadDecompositionAlgebra(path cat "A5/15/5A5A3A2B_1");

assert IsEmpty(JordanAxes(A));
axis_reps := AxisOrbitRepresentatives(A);
assert #FindMultiples(axis_reps[1]) eq 1;
// ie there are no multiples for the axis given

axes := Axes(A);
Vaxes := sub<VectorSpace(A)|[Vector(a) : a in axes]>;
assert Dimension(Vaxes) eq #axes;

// define a map by switching the first two axes.
assert forall{i : i in [1..#axes] | Vaxes.i eq Vector(axes[i])};
phi := hom<Vaxes -> VectorSpace(A) | [Vaxes.i : i in [2,1] cat [3..15]]>;


G0 := MiyamotoGroup(A);
E := SylowSubgroup(G0, 2);
K := Centraliser(G, E);
N := Normaliser(G,E);


CG := CharacterGroup(A);
Y := {@ axes[i] : i in [1..#axes] | MiyamotoElement(A,i, CG.1) in E@};
YD := {@ Decomposition(a) : a in Y@};

joint := JointPartDecomposition(YD);

// The 0 eigenspace is the 2nd element of the fusion law
assert Dimension(joint[<2,2,2>]) eq 7;
assert Dimension(joint[<2,3,3>]) eq 1;
assert Dimension(joint[<2,2,3>]) eq 2;
assert Dimension(joint[<3,4,4>]) eq 3;
assert Dimension(joint[<2,4,4>]) eq 6;

U := joint[<2,2,2>];
idems2 := FindAllIdempotents(A, U:length:=2);
Ualg, inc := Subalgebra(A, Basis(U));
Aalg := Algebra(A);

Ualg_idems2 := {@ Ualg!Aalg!Vector(v) : v in idems2 @};
assert forall{v : v in Ualg_idems2 | HasMonsterFusionLaw(v:fusion_values:={@4/11,1/11@})};

V, inc := Subalgebra(A, idems2);
assert Dimension(V) eq 3;
// Should do something to show this is a 3C

so, U_id := HasOne(Ualg);
assert so;
AU_id := A!Aalg!U_id;
assert Frobenius(AU_id, AU_id) eq 11;

so, V_id := HasOne(V);
assert so;
AV_id := A!Aalg!V_id;
assert Frobenius(AV_id, AV_id) eq 11/2;

idems_11_2 := FindAllIdempotents(A, U:length:=11/2);
assert #idems_11_2 eq 8;
assert AU_id - AV_id in idems_11_2;
assert Dimension(Subalgebra(A, idems_11_2)) eq 7;

values := {@ [ Frobenius(idems_11_2[i], a) : a in idems2 ] : i in [1..8] @};
assert #values eq 8;
// so they are unique determined by their inner products with idems2;

W1 := joint[<3,4,4>];
W2 := joint[<4,3,4>];
W3 := joint[<4,4,3>];
Ws := [W1, W2, W3];

assert Dimension(Subalgebra(A, [ VectorSpace(A)!v : v in Basis(W), W in Ws])) eq Dimension(A);

id_U := hom< Ualg-> Ualg | [ Ualg.i : i in [1..Dimension(Ualg)]]>;

// Similar for the other Wi
so, W1_ext := HasInducedMap(A, W1, id_U);
assert so;
assert Dimension(W1_ext) eq 1;

assert forall{ <w,u> : w in Basis(W1), u in Basis(Ualg) | Frobenius((A!w)*(A!w), A!u) ne 0};
assert forall{ <w1,w2,w3> : w1 in Basis(W1), w2 in Basis(W2), w3 in Basis(W3) | Frobenius((A!w1)*(A!w2), A!w3) ne 0};

G := UniversalMiyamotoGroup(A);

K := sub<G| [ g : g in G | forall{ a : a in Y | a*g in Y}]>;
E := sub<G| [ g : g in G | forall{ a : a in Y | a*g eq a}]>;
N := Normaliser(G,E);








