/*

The example for L_3(2) 4B3A

*/
AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored
path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

// Preliminary data
A := LoadDecompositionAlgebra(path cat "PSL(2,7)/21/4B3A_1.json");
field := BaseRing(A);
n := Dimension(A);
G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "PSL(2,7)";

// If the algebra is Miyamoto closed, then the Miyamoto group is a permutation group on the axes
axes := Axes(A);
assert forall{ <i,g> : i in [1..#axes], g in Generators(G0) | axes[i]*g eq axes[Image(g,GSet(G0),i)]};


/*The perumtation below is a permutation of the axes of A which preserves shape.*/
phi := Sym(21)!(1, 7)(3, 10)(4, 11)(5, 15)(6, 8)(9, 16)(12, 17)(14, 21)(19, 20);
assert IsCoercible(G0, phi) eq false;/*hence this is an outer automorphism*/
axis_reps := AxisOrbitRepresentatives(A);
axes := Axes(A);

//Computation 12.1 (a) We show that A has no Jordan axes.

assert #JordanAxes(A) eq 0;

//Computation 12.1 (b) We show all the axes are in one orbit, and that there are no twins
axes_reps := AxisOrbitRepresentatives(A);
assert #axes_reps eq 1;
assert #(FindMultiples(axes_reps[1])) eq 1;

// Computation 12.1 (c)
Vaxes := sub<VectorSpace(A) | [Vector(x) : x in axes]>;
phi_map := hom<Vaxes -> VectorSpace(A) | [<Vector(axes[i]), Vector(axes[i^phi])> : i in [1..21]]>;
bool, phi_map := ExtendMapToAlgebraAutomorphism(A, phi_map);
assert bool;

assert IsInducedFromAxis(A, phi_map) eq false;
// So we have indeed constructed an algebra automorphism not induced by an axis

G := PermutationGroup<21 | G0, phi>;
assert GroupName(G) in {"SO(3,7)", "PGL(2,7)"}; // These are isomorphic

// We now set up a decomposition with respect to a set of axes generating a 2A algebra and whose tau involutions generate an elementary abelian group 2^2.

a := axes[1];
two_As := [x : x in axes[[2..21]] | y*y eq y where y is -8*a*x+x+a];
assert #two_As gt 2;
b := two_As[1];
c := -8*a*b+a+b;
Y := {@ a, b, c @};
assert Dimension(Subalgebra(A, Y)) eq 3;

E := sub<G0 | [MiyamotoElement(A, Position(axes, y)) : y in Y]>;
assert GroupName(E) eq "C2^2";

// Computation 12.2 Details of the decomposition

YD := {@ Decomposition(x): x in Y @};
decomp := JointPartDecomposition(YD);
// Note here that the keys of the decomposition are indexed by the tuples <i,j,k> where
// 1\le i,j,k\le 4 with 1:->1,0:->2, 1/4:->3 and 1/32:->4.

// Part (a) U_{(0,0,0)}(Y) is indexed by <2,2,2>;

U := decomp[<2,2,2>];
assert Dimension(U) eq 10;

// Part (b) The rest of the components are as follows:

// Part (b) (i) U_{(1/4,1/32,1/32)}(Y), U_{(1/32,1/4,1/32)}(Y) and U_{(1/32,1/32,1/4)(Y)
// by the map above, these will be indexed <3,4,4>, <4,3,4> and <4,4,3> respectively.

assert forall{x : x in [<3,4,4>, <4,3,4>, <4,4,3>] | Dimension(decomp[x]) eq 4};

// Part (b) (ii) U_{(0,1/32,1/32)}(Y),U_{(1/32,0,1/32)}(Y) and U_{(1/32,1/32,0)}(Y)
// These are indexed by <2,4,4>,<4,2,4> and <4,4,2>, respectively.

assert forall{x : x in  [<2,4,4>,<4,2,4>, <4,4,2>] | Dimension(decomp[x]) eq 6};

// We turn to determining Aut(U). Note that N_{G0}(E) is ismorphic to S_4, and that clearly this induces S_3 on U, since E acts trivially on U, and N/E is a non-abelian group of order 6.

N := Normaliser(G0, E);
assert GroupName(N) eq "S4";

Ualg, U_inc := Subalgebra(A, Basis(U));

//Computation 12.4

// Part (a)

F, F_inc := FixedSubalgebra(A, Ualg, N);
assert Dimension(F) eq 4;

F_vsp := sub<VectorSpace(A) | [Vector(v@F_inc) : v in Basis(F)]>;
idemps_F := FindAllIdempotents(A, F_vsp : extend_field:=true);
assert #idemps_F eq 12;

// Part (b)
thirty_four_fifths := [ x : x in idemps_F | Frobenius(x,x) eq 34/5];
assert #thirty_four_fifths eq 1;
d := A!Eltseq(thirty_four_fifths[1]);

//Part (c) & (d)
// First we induce d into U
d_U := Vector(d)@@U_inc;
evals, espaces, FL := IdentifyFusionLaw(d_U: eigenvalues:={@1,0, 9/10,1/2@});
Gr, Gr_map := FinestAdequateGrading(FL);
assert Order(Gr) eq 2;
assert { i : i in Elements(FL) | not IsIdentity(i@Gr_map)} eq { FL | 4 };
assert not HasMonsterFusionLaw(d_U);

// So the fusion law is C_2-graded and 1/2 is the negatively graded part

assert evals eq {@ <1, 1>, <0, 4>, <9/10, 2>, <1/2, 3> @};
d_U_1 := espaces[1];
d_U_0 := espaces[2];
d_U_9_10 := espaces[3];
d_U_1_2 := espaces[4];

assert Dimension(d_U_1) eq 1;
assert Dimension(d_U_0) eq 4;
assert Dimension(d_U_9_10) eq 2;
assert Dimension(d_U_1_2) eq 3;

// We note that the variety of idempotents of length 34/5 in U is 1-dim
R := PolynomialRing(field, 10);
FR := FieldOfFractions(R);
AFR := ChangeRing(A, FR);
u := &+[R.i*(AFR!U.i) : i in [1..10]];
I := ideal<R | Eltseq(u*u-u), Frobenius(u,u)-34/5>;
assert Dimension(I) eq 1;

// Computation 12.5 
T := Eigenspace(d_U, 0);

idemps_T := FindAllIdempotents(Ualg, T : extend_field:=true);
assert #idemps_T eq 16;

// in fact all these idempotents lie over Q
assert forall{x : x in idemps_T | x in Ualg};
assert #{x : x in idemps_T | Frobenius(y,y) eq 7/5 where y is A!(x@U_inc)} eq 3;

// Thus there are three idempotents of length 7/5 in T. We show that these are all in U.

// Computation 12.6

// Part (a) U has exactly three idempotents of length 7/5.
seven_fifths_U := FindAllIdempotents(A, U : length:=7/5);
assert #seven_fifths_U eq 3;

// Part (b)
uis := [ Vector(A!x)@@U_inc : x in seven_fifths_U];
Talg, Talg_inc := Subalgebra(Ualg, uis);
assert Dimension(Talg) eq 4;
assert sub<VectorSpace(Ualg) | [ Vector(x@Talg_inc) : x in Basis(Talg)]> eq T;

// Parts (c) & (d)

for ui in uis do
  evals, espaces, FL := IdentifyFusionLaw(ui: eigenvalues:={@1,0, 3/10,1/20@});
  assert Dimension(espaces[1]) eq 1;
  assert Dimension(espaces[2]) eq 4;
  assert Dimension(espaces[3]) eq 2;
  assert Dimension(espaces[4]) eq 3;

  Gr, Gr_map := FinestAdequateGrading(FL);
  assert Order(Gr) eq 2;
  assert { i : i in Elements(FL) | not IsIdentity(i@Gr_map)} eq { FL | 4 };
  assert not HasMonsterFusionLaw(ui);
end for;

// Part (e)
tau_uis := [ MiyamotoInvolution(ui) : ui in uis];
assert forall{tau : tau in tau_uis | IsAutomorphism(Ualg,tau) eq true};

H := MatrixGroup<10, field | tau_uis>;
assert GroupName(H) eq "S3";

assert uis[2]*tau_uis[1] eq uis[3];
assert uis[1]*tau_uis[2] eq uis[3];
// Since (u_1,u_3) and (u_2,u_3) generate Sym({u_1,u_2,u_3}), action is transitive.


assert Algebra(A)!Vector(d) eq One(Ualg) - One(Talg);

// Computation 12.7

// Part (a)
id_T := IdentityHomomorphism(Talg);

bool, ext := HasInducedMap(Ualg, d_U_1_2, id_T);
assert bool;
assert Dimension(ext) eq 1;
assert IsIdentity(ext.1);

// Part (b)
bas_d_U_1_2 := Basis(d_U_1_2);

// we can check the projection by coercing into A and using the Frobenius form
assert forall{ x : x in bas_d_U_1_2 | 
                   exists{ t : t in Basis(Talg) | Frobenius(A!Ualg!x*A!Ualg!x, A!t) ne 0}};

// Part (c)
assert Subalgebra(Ualg, bas_U1_2d) eq Ualg;

tau_d := MiyamotoInvolution(d_U);
Hhat := MatrixGroup<10, field | tau_uis cat [tau_d] >;
assert Order(Hhat) eq 12;
assert tau_d in Centre(Hhat);
assert Order(Centre(Hhat)) eq 2;
// Since tau_uis generate S_3 which has index 2, it is normal and so Hhat is a direct product

// Computation 12.9
Ws := [decomp[<2,4,4>], decomp[<4,2,4>], decomp[<4,4,2>]];

// Part (a)
id_U := IdentityHomomorphism(Ualg);

for Wi in Ws do
  bool, exten := HasInducedMap(A, Wi, id_U);
  assert bool;
  assert Dimension(exten) eq 1;
  assert IsIdentity(exten.1);
end for;


// Part (b)

bas_Ws := [[ A!w : w in Basis(Ws[i])] : i in [1..3]];

// Part (b) (i)
bas_U := [ A!u : u in Basis(U)];
for i in [1..3] do
  bas_Wi := bas_Ws[i];
  values := [ Frobenius(w*w,u) : w in bas_Wi, u in bas_U ];
  Frob_0 := #{v : v in values | v eq 0};
  Frob_nz := #values - Frob_0;
  print Frob_0, Frob_nz;
end for;
// Only one pair (wi, u) gives 0, the other 59 are non-zero.

// Part (b) (ii)
values := [ Frobenius(w1*w2,w3) : w1 in bas_Ws[1], w2 in bas_Ws[2], w3 in bas_Ws[3]];
Frob_0 := #{v : v in values | v eq 0};
Frob_nz := #values - Frob_0;
print Frob_0, Frob_nz;
// one triple (w1,w2,w3) gives 0, the other 215 are non-zero

//Part (c)
assert Dimension(sub<A | &cat[ Basis(W) : W in Ws]>) eq Dimension(A);

// Part (d)
// It suffices to check on generators.
gensHhat := Generators(Hhat);
assert forall{h : h in gensHhat |
                  exists{W : W in Ws | 
                     not HasInducedMap(A, W, hom<Ualg->Ualg | u:-> u*h>)}};
