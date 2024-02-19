/*

The example for L_3(2) 4A3C

*/
/*
AttachSpec("DecompAlgs.spec");
AttachSpec("/home/tendai/AxialTools/AxialTools.spec");
Attach("AxialTools.m");
Attach("/home/tendai/Downloads/Automorphisms.m");
*/

AttachSpec("../DecompAlgs/DecompAlgs.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("../DecompAlgs/AxialTools.m");
Attach("Automorphisms.m");

// Alter this to the path of where your algebra is stored

path := "../DecompAlgs/library/Monster_1,4_1,32/RationalField()/";

// Preliminary data
A := LoadDecompositionAlgebra(path cat "PSL(2,7)/21/4A3C_1.json");
F := BaseRing(A);
n := Dimension(A);
G0 := MiyamotoGroup(A);
assert GroupName(G0) eq "PSL(2,7)";

// If the algebra is Miyamoto closed, then the Miyamoto group is a permutation group on the axes
axes := Axes(A);
assert forall{ <i,g> : i in [1..#axes], g in Generators(G0) | axes[i]*g eq axes[Image(g,GSet(G0),i)]};

// Computation 12.18 (a) We show that A has no Jordan axes.
assert #JordanAxes(A) eq 0;

// Computation 12.18 (b) We show all the axes are in one orbit, and that there are no twins
axes_reps := AxisOrbitRepresentatives(A);
assert #axes_reps eq 1;
assert #(FindMultiples(axes_reps[1])) eq 1;

// So axes are in bijection with the Miyamoto involutions.

aut := AutomorphismGroup(G0);
assert Order(OuterFPGroup(aut)) eq 2;
exists(out){ out : out in Generators(aut) | not IsInner(out)};

// Since there is a bijection between axes and MiyamotoInvolutions, we can get the action of out on the axes.
Miy_elts := [ MiyamotoElement(A, i) : i in [1..#axes]];
out := Sym(21)![ Position(Miy_elts, Miy_elts[i]@out) : i in [1..#axes]];

assert out notin G0;
G := PermutationGroup<21| G0, out>;
assert GroupName(G) eq "SO(3,7)";  //Recall that SO(3,7) is isomorphic to PGL(2,7).
assert Index(G, G0) eq 2;

// We check that out is indeed an automorphism of A
Vaxes := sub<VectorSpace(Algebra(A)) | [Vector(x):x in axes]>;
out_map := hom<Vaxes->VectorSpace(A) | [<Vector(axes[i]), Vector(axes[i^out])> : i in [1..21]]>;
bool, out_map := ExtendMapToAlgebraAutomorphism(A, out_map);
assert bool;

// Computation 12.18 (c)
// We find the involutions in G outside G0.
invs := [x[3] : x in ConjugacyClasses(G) | x[1] eq 2];
assert #invs eq 2;
assert exists{ g : g in invs | g in G0}; // One class is in G0
assert exists(g){ g : g in invs | g notin G0}; // The other is outside G0
// There is only one class.
g_Vaxes := hom<Vaxes->VectorSpace(A) | [<Vector(axes[i]), Vector(axes[i^g])>:i in [1..21]]>;
so, g_map := ExtendMapToAlgebraAutomorphism(A, g_Vaxes);
assert so;
assert not IsInducedFromAxis(A, g_map);
// So none of the involutions outside G0 are tau involutions.


// We now set up a decomposition with respect to a set of axes generating 2B algebras pairwise and whose tau involutions generate an elementary abelian group 2^2.
a := axes[1];
Y := {@ a @};
possibles := [x : x in axes | x*a eq A!0 ];

so := true;
while so do
  so := exists(b){b : b in possibles | forall{y : y in Y | IsZero(y*b)}};
  if so then
    Include(~Y, b);
  end if;
end while;

assert #Y eq 3;
b := Y[2];
c := Y[3];

assert Dimension(Subalgebra(A, Y)) eq 3;
E := sub<G | [MiyamotoElement(A, Position(axes, y)) : y in Y]>;
assert GroupName(E) eq "C2^2";
N := Normaliser(G, E);
assert GroupName(N) eq "S4";


// Computation 12.19 Details of the decomposition. Here a_1=a, a_2=b and a_3=c.
YD := {@Decomposition(y) : y in Y@};
decomp := JointPartDecomposition(YD);
/*
Note here that the keys of the decomposition are indexed by the tuples <i,j,k>,
where i,j,k are elements of the fusion law
ie 1\le i,j,k\le 4 with 1:->1,0:->2, 1/4:->3 and 1/32:->4.
*/

// Part (a) U_{(0,0,0)}(Y) is indexed by <2,2,2>;

U := decomp[<2, 2, 2>];
assert Dimension(U) eq 9;

// Part (b) The rest of the components are as follows:

// Part (b) (i) U_{(1,0,0)}(Y)=<a>, U_{(0,1,0)}(Y)=<b> and U_{(0,0,1)(Y)=<c>
// by the map above, these will be indexed <1,2,2>, <2,1,2> and <2,2,1> respectively.

assert forall{x : x in [<1, 2, 2>, <2, 1, 2>, <2, 2, 1>] | Dimension(decomp[x]) eq 1};

/* Part (b) (ii) U_{(0,1/4,1/4)}(Y), U{(1/4,0,1/4)}(Y) and U_{(1/4,1/4,0)}(Y). These are indexed by
   <2,3,3>, <3,2,3> and <3,3,2>, respectively.*/
assert forall{x : x in [<2, 3, 3>, <3, 2, 3>, <3, 3, 2>] | Dimension(decomp[x]) eq 1};

/* Part (b) (iii) U_{(1/4,0,0)}(Y), U{(0,1/4,0)}(Y) and U_{(0,0, 1/4)}(Y). These are indexed by
   <3,2,2>, <2,3,2> and <2,2,3>, respectively.*/
assert forall{x : x in [<3, 2, 2>, <2, 3, 2>, <2, 2, 3>] | Dimension(decomp[x]) eq 2};

/*Part (b) (iv) U_{(1/4,1/32,1/32)}(Y),U_{(1/32,1/4,1/32)}(Y) and U_{(1/32,1/32,1/4)(Y),
  which are indexed by <3,4,4>,<4,3,4> and <4,4,3>, respectively.*/
assert forall{x : x in [<3, 4, 4>, <4, 3, 4>, <4, 4, 3>] | Dimension(decomp[x]) eq 2};

/*Part (b) (v) U_{(0,1/32,1/32)}(Y),U_{(1/32,0,1/32)}(Y) and U_{(1/32,1/32,0)(Y),
  which are indexed by <2,4,4>,<4,2,4> and <4,4,2>, respectively.*/

assert forall{x : x in [<2, 4, 4>, <4, 2, 4>, <4, 4, 2>] | Dimension(decomp[x]) eq 10};

/*
We turn to determining Aut(U). Note that N_{G}(E) is isomorphic to S_4, and this clearly induces S_3 on U,
since E acts trivially on U, and N/E is a non-abelian group of order 6.
*/

Ualg, U_inc := Subalgebra(A, Basis(U));

//Computation 12.20
T, T_inc := FixedSubalgebra(A, Ualg, N);
assert Dimension(T) eq 3;

Tsub := sub<VectorSpace(A) | [ Vector(t@T_inc) : t in Basis(T)]>;
idem_T := FindAllIdempotents(A, Tsub: extend_field:=true);
assert #idem_T eq 8;
assert {Frobenius(x,x) : x in idem_T} eq {0, 15, 135/16, 105/16, 75/8, 45/8, 360/37, 195/37};


// Computation 12.21
exists(d){ d : d in idem_T | Frobenius(d,d) eq 45/8};
// Part (a)
idem_U := FindAllIdempotents(A, U: length:=45/8, extend_field:=true);
assert #idem_U eq 4;
assert d in idem_U;
Us := {@ Vector(u)@@U_inc : u in idem_U | u ne d @};
// Part (b)
dU := Vector(d)@@U_inc;
assert Dimension(Eigenspace(dU, 1)) eq 3;
assert forall{u : u in Us | Dimension(Eigenspace(u, 1)) eq 2};

// Computation 12.22

assert Subalgebra(Ualg, Us) eq Ualg;

// Computation 12.24 
Ws := [decomp[x] : x in [ <3, 4, 4>, <4, 3, 4>, <4, 4, 3>]];

// Part (a) the Ws generate A.
assert Subalgebra(A, &cat[ Basis(W) : W in Ws]) eq Algebra(A);

// Part (b)
id_U := IdentityHomomorphism(Ualg);

extend_W := [ phi where so, phi := HasInducedMap(A, Ws[i], id_U) : i in [1..3] ];
assert #extend_W eq 3;
assert forall{ ext : ext in extend_W | Dimension(ext) eq 1};
// For each W, the only possible extensions are scalar multiples of the identity
assert forall{ ext : ext in extend_W | IsIdentity(ext.1) };

// Part (c)
// We check for each basis element of W_i
// Part (c) (i)
forall{ <i, w, u> : w in Basis(Ws[i]), i in [1..3], u in Basis(U) | Frobenius(A!w*A!w,A!u) ne 0};

// Part (c) (ii)
forall{ <w1, w2, w3> : w1 in Basis(Ws[1]), w2 in Basis(Ws[2]), w3 in Basis(Ws[3]) | Frobenius((A!w1*A!w2)*(A!w1*A!w3),A!w1) ne 0};


// Computation 12.26

// The joint decomposition is complete
assert &+[ Dimension(d) : d in decomp] eq Dimension(A);
// So there is a projection from A to any given part of the decomposition, eg U

so, proj := HasProjection(A, U);
assert so;

Ts := {@ sub<U | [ Vector(A!x*A!y)@proj : x, y in Basis(Ws[i])]> : i in [1..3] @};
assert forall{T : T in Ts | Dimension(T) eq 3};
assert forall{i : i in [1..2] | forall{j : j in [i+1..3] | Dimension(Ts[i] meet Ts[j]) eq 0}};
