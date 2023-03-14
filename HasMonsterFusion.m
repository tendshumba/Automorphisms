P<s>:=PolynomialRing(Rationals(),1);

//Thoughts: two functions, one to check if a given idempotent satisfies the 
//monster fusion, another to compute a fusion law if the former is not true.

//Questions: which is faster, matrix or algebra multiplication?

eigens:=[1,0,1/4,1/32];

Pow:=function(u,n)
/*u must be an algebra element and n a nonnegative integer.*/
//if n eq 0 then 
 //if HasIdentity(Parent(u)) then 
  //pow:=Identity(Parent(u));
 //else
  //print("Error, the given power cannot be computed");
  //return 0;
 //end if;
 if n eq 1 then
  pow:=u;
 else
  count:=n; pow:=u;
  while count gt 1 do
   pow:=pow*u; count:=count-1;/*this can actually deal with n=1.*/
  end while;
 end if;
 return pow;
end function;

load "AdPowerAtElement.m";

/*check if the eigenvalues are in eigens, if so, check if dimensions add up.*/
HasMonsterFusion:=function(u)
 bas:=Basis(Parent(u));

 ad:=Matrix(BaseField(Parent(u)), [Eltseq(u*bas[i]): i in [1..Dimension(Parent(u))]]);
  eigs:=IndexedSet(Eigenvalues(ad));
 if exists(ev){eigs[i][1]:i in [1..#eigs]|not (eigs[i][1]  in eigens)} then
  printf("Eigenvalue %o not in [1,0,1/4,1/32]\n"),ev;
  return false; 
 elif &+[eigs[i][2]:i in [1..#eigs]] ne #bas then 
 print("Dimensions do not add up\n");
  return false;
 else 
  E0:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,0))];/*one hopes all eigenvalues are involved,
 if not, then a check has to be made.*/
  E1:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,1))];
  E4:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,1/4))];
  E32:=[Parent(u)!Eltseq(u):u in Basis(Eigenspace(ad,1/32))];
  /*1* everything else, not necessary, but we do it .*/
  bools:=[];
  bool1:=[
  forall{PolynomialAtAdAtElement(s-1,u,E1[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E1],j in [1..#E1]},
  forall{u*(E0[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E0],j in [1..#E1]},
  forall{PolynomialAtAdAtElement(s-1/4,u,E4[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E4],j in [1..#E1]},
  forall{PolynomialAtAdAtElement(s-1/32,u,E32[i]*E1[j]) eq Zero(Parent(u)) :i in [1..#E32],j in [1..#E1]}];
  Append(~bools,forall{bool:bool in bool1|bool eq true});

  /*we now check multiplication by 0 here.*/
  bool2:=[forall{PolynomialAtAdAtElement(s,u,(E0[i]*E0[j])) eq Zero(Parent(u)) :i in [1..#E0],j in [1..#E0]},
  forall{PolynomialAtAdAtElement(s-1/4,u,(E4[i]*E0[j])) eq Zero(Parent(u)) :i in [1..#E4],j in [1..#E0]},   
  forall{PolynomialAtAdAtElement(s-1/32,u,(E32[i]*E0[j])) eq Zero(Parent(u)) :i in [1..#E32],j in [1..#E0]}];
  Append(~bools,forall{bool:bool in bool2|bool eq true});

 /*we check multiplication by 1/4 now.*/
  bool3:=[
  forall{PolynomialAtAdAtElement((s-1)*s,u,E4[i]*E4[j]) eq Zero(Parent(u)) :i in [1..#E4],j in [1..#E4]},
  forall{PolynomialAtAdAtElement(s-(1/32),u,E32[i]*E4[j]) eq Zero(Parent(u)) :i in [1..#E32],j in [1..#E4]}];
  Append(~bools,forall{bool:bool in bool3|bool eq true});

 /*finally multipliction by 1/32.*/
 bool4:=[
 forall{PolynomialAtAdAtElement((s-1)*(s-1/4)*s,u,(E32[i]*E32[j])) eq
 Zero(Parent(u)) :i in [1..#E32],j in [1..#E32]}];
 Append(~bools,forall{bool:bool in bool4|bool eq true});
 if false in bools then 
  return false;
 else 
  return true;
 end if;
end if;
end function;
 





