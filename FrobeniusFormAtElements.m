/*Given an axial  algebra A with a form, compute the number (u,v) for given elements u,v in A.*/
	FrobFormAtElements:=function(u,v,U) /* these must live in the axial algebra category for this to work.*/
			A:=Parent(u);
			//so,U:=HasFrobeniusForm(A);
			/*if so eq false then 
				return "Error the parent of u and v does not have a form";
			else*/
			//	UQ:=Matrix(Rationals(),[Eltseq(Vector(Rationals(),Eltseq(U[i]))):i in [1..Nrows(U)]]);
			//
				F:=BaseField(A);
				UQ:=ChangeRing(U,F);
				return (VecToMat(u)*UQ*Transpose(VecToMat(v)))[1][1];
			//end if;
	end function;

