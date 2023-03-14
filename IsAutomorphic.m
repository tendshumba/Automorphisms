/*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
+This function checks if an invertible endomorphism phi: V->V is an automorphism of a subalgebra V of A +
+                                                                                                       +
+													+
+													+
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*/
IsAutomorphic:=function(A,V,phi)
    CartPower:=[];
	for x in CartesianPower(Basis(V),2) do
		if not <x[2],x[1]> in CartPower then
			Append(~CartPower,x);
		end if;
	end for;
	return forall{x:x in CartPower|
		ToBigVec(A,V,(ToSmallVec(A,V,(A!x[1])*(A!x[2])))*phi) eq (ToBigVec(A,V,ToSmallVec(A,V,x[1])*phi))*(ToBigVec(A,V,ToSmallVec(A,V,x[2])*phi))};

	/* This is naive. The algebra is commutative.
eturn forall{x:x in CartesianProduct(Basis(V),Basis(V))|
		ToBigVec(A,V,(ToSmallVec(A,V,(A!x[1])*(A!x[2])))*phi) eq (ToBigVec(A,V,ToSmallVec(A,V,x[1])*phi))*(ToBigVec(A,V,ToSmallVec(A,V,x[2])*phi))};*/

end function;
